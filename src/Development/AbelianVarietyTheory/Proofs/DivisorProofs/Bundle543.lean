module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle393
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle375
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle493
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Mathlib.Tactic.Linter.HaveILetI
public import Mathlib.Topology.DiscreteQuotient
public import Mathlib.Topology.LocallyConstant.Algebra
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle483
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle304
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle008
public import Mathlib.RingTheory.Ideal.Height
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle497
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BicharacterFourierTransformTwiceEqPosSmulReflect
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle496
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

@[expose] public section

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam.ExpansionB

theorem val_div_ne_int (N : ℕ) [NeZero N] (j : ZMod N) (hj : j ≠ 0) (n : ℤ) :
    ((j.val : ℂ)) / N ≠ n := by
  intro h
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  rw [div_eq_iff hN] at h
  have h' : (j.val : ℤ) = n * (N : ℤ) := by exact_mod_cast h
  apply hj
  have h2 := congrArg (Int.cast : ℤ → ZMod N) h'
  simpa using h2

theorem main : ∀ (N : ℕ) [NeZero N] (x : Fin 2 → ZMod N), x ≠ 0 → HasQ N (wB N x) (cB N x) := by
  classical
  intro N _ x hx
  rw [hasQ_iff]
  intro τ
  obtain ⟨T, hT, hS⟩ := GlobalTheory.T.torsionPoint_rows_sum_eq_divisor_series N 1 τ x _ le_rfl (GlobalTheory.T.G2_add_weierstrassP_row_sum τ (tors N τ x))
  have hc : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero]
  have hT' : HasSum (fun k : ℕ => cSum N 1 1 x k *
      Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * τ / N) ^ k) T := by
    simpa using hT
  set c : ℂ := (if x 0 = 0 then ch N (x 1) / (1 - ch N (x 1)) ^ 2 else 0) with hcdef
  have hval : wB N x τ = T + c := by
    rw [wB_eq, hS, div_eq_iff (pow_ne_zero 2 hc), hcdef]
    by_cases h0 : x 0 = 0
    · have h1 : x 1 ≠ 0 := by
        intro h1
        apply hx
        funext i
        fin_cases i
        · exact h0
        · exact h1
      have him : (((x 1).val : ℂ) / N).im = 0 := by
        have : (((x 1).val : ℂ) / N) = ((((x 1).val : ℝ) / N : ℝ) : ℂ) := by push_cast; rfl
        rw [this, Complex.ofReal_im]
      have hr := (GlobalTheory.T.rowSums_two_three_closedForm_real_nonInteger _ him (val_div_ne_int N (x 1) h1)).1
      have hch : Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (((x 1).val : ℂ) / N)) = ch N (x 1) := by
        rw [ch, mul_div_assoc]
      rw [hch] at hr
      rw [if_pos h0, if_pos h0]
      have e2 : (1 + 1 : ℕ) = 2 := rfl
      rw [e2, hr]
      simp only [Nat.factorial_one, Nat.cast_one]
      ring
    · rw [if_neg h0, if_neg h0]
      simp only [Nat.factorial_one, Nat.cast_one]
      ring
  rw [hval]
  have hs : HasSum (fun k : ℕ => if k = 0 then c else 0) c := hasSum_ite_eq 0 c
  convert hT'.add hs using 2 with k
  by_cases hk : k = 0
  · subst hk
    simp [cB, cSum, hcdef]
  · simp [cB, hk]

end GlobalTheory.WpFam.ExpansionB
end

section

namespace GlobalTheory.OTY

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

section

variable {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La]

theorem etaleSmooth_contDiffAt_chart {A : WeightedAtlas n Y ι La} {U : Set Y} {z : Y → V n}
    (hE : Etale A U z) {x : Y} (hx : x ∈ U) {i : ι} (hi : x ∈ (A.chart i).source) :
    ContDiffAt ℂ ∞ (z ∘ (A.chart i).symm) (A.chart i x) := by
  have ho : IsOpen ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) :=
    (A.chart i).isOpen_inter_preimage_symm hE.isOpen
  have hm : A.chart i x ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹' U :=
    ⟨(A.chart i).map_source hi, by simp [(A.chart i).left_inv hi, hx]⟩
  have hk : ∀ k, ContDiffOn ℂ ∞ (fun v => (z ∘ (A.chart i).symm) v k)
      ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) := fun k =>
    contDiffOn_of_differentiableOn n _ _ ho
      ((EuclideanSpace.proj k : V n →L[ℂ] ℂ).differentiable.comp_differentiableOn (hE.holo i))
  have hpi := contDiffOn_pi.mpr hk
  have h2 : ContDiffOn ℂ ∞ (z ∘ (A.chart i).symm)
      ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) :=
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)).symm.contDiff.comp_contDiffOn hpi
  exact (h2 _ hm).contDiffAt (ho.mem_nhds hm)

theorem etaleSmooth_inverse {A : WeightedAtlas n Y ι La} {U : Set Y} {z : Y → V n}
    (hE : Etale A U z) (e : OpenPartialHomeomorph U (V n))
    (he : IsChart n (fun y : U => z y) e) (v : V n) (hv : v ∈ e.target) (i : ι)
    (hi : ((e.symm v : U) : Y) ∈ (A.chart i).source) :
    ContDiffAt ℂ ∞ (fun v' => A.chart i (e.symm v' : Y)) v ∧
      (∀ᶠ v' in 𝓝 v, ((e.symm v' : U) : Y) ∈ (A.chart i).source) := by
  have hzs : ∀ v' ∈ e.target, z (e.symm v' : Y) = v' := fun v' hv' => by
    have := he (e.map_target hv')
    simp only at this
    rw [this, e.right_inv hv']
  set x : U := e.symm v with hxdef
  set G : V n → V n := fun v' => A.chart i (e.symm v' : Y) with hG
  have hz := etaleSmooth_contDiffAt_chart hE x.2 hi
  have hdet : (GlobalTheory.OTY.jz A z i x).det ≠ 0 := hE.det_ne i x x.2 hi
  set f' := (GlobalTheory.OTY.jz A z i x).toContinuousLinearEquivOfDetNeZero hdet with hf'def
  have hf' : HasFDerivAt (z ∘ (A.chart i).symm) (f' : V n →L[ℂ] V n) (A.chart i x) := by
    rw [hf'def, ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]
    exact (hz.differentiableAt (by simp)).hasFDerivAt
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hstrict := hz.hasStrictFDerivAt' hf' hn
  have hzx : (z ∘ (A.chart i).symm) (A.chart i x) = v := by
    rw [Function.comp_apply, (A.chart i).left_inv hi]
    exact hzs v hv
  have hGv : G v = A.chart i x := rfl
  have hc0 : ContinuousAt (Subtype.val ∘ e.symm) v :=
    continuous_subtype_val.continuousAt.comp (e.continuousAt_symm hv)
  have hsrc : ∀ᶠ v' in 𝓝 v, ((e.symm v' : U) : Y) ∈ (A.chart i).source :=
    hc0.eventually_mem ((A.chart i).open_source.mem_nhds hi)
  have hGc : ContinuousAt G v :=
    ContinuousAt.comp (f := Subtype.val ∘ e.symm) ((A.chart i).continuousAt hi) hc0
  have hright : ∀ᶠ v' in 𝓝 v, (z ∘ (A.chart i).symm) (G v') = v' := by
    filter_upwards [hsrc, e.open_target.mem_nhds hv] with v' h1 h2
    rw [hG]
    simp only [Function.comp_apply]
    rw [(A.chart i).left_inv h1]
    exact hzs v' h2
  have hleft : ∀ᶠ v' in 𝓝 v,
      hstrict.localInverse _ _ _ ((z ∘ (A.chart i).symm) (G v')) = G v' := by
    have := hGc.tendsto.eventually (f := G) (by rw [hGv]; exact hstrict.eventually_left_inverse)
    exact this
  have heq : G =ᶠ[𝓝 v] hstrict.localInverse _ _ _ := by
    filter_upwards [hleft, hright] with v' h1 h2
    rw [← h1, h2]
  have hloc : ContDiffAt ℂ ∞ (hz.localInverse hf' hn) ((z ∘ (A.chart i).symm) (A.chart i x)) :=
    hz.to_localInverse hf' hn
  rw [hzx] at hloc
  exact ⟨hloc.congr_of_eventuallyEq heq, hsrc⟩

theorem etaleSmooth_complex {A : WeightedAtlas n Y ι La} {U : Set Y} {z : Y → V n}
    (hE : Etale A U z) (u : Y → ℂ)
    (hu : ∀ x ∈ U, ∃ i, x ∈ (A.chart i).source ∧
      ContDiffAt ℝ ∞ (u ∘ (A.chart i).symm) (A.chart i x)) :
    Smooth n (fun y : U => z y) (fun y : U => u y) := by
  intro e he v hv
  obtain ⟨i, hi, hui⟩ := hu _ (e.symm v).2
  obtain ⟨hG, hsrc⟩ := etaleSmooth_inverse hE e he v hv i hi
  have hc : ContDiffAt ℝ ∞ ((u ∘ (A.chart i).symm) ∘ fun v' => A.chart i (e.symm v' : Y)) v :=
    hui.comp v (hG.restrict_scalars ℝ)
  refine (hc.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [hsrc] with v' h1
  simp [(A.chart i).left_inv h1]

end

theorem smooth_etale_of_smooth_in_charts : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (U : Set Y) (z : Y → V n), Etale A U z → (∀ u : Y → ℂ, (∀ x ∈ U, ∃ i, x ∈ (A.chart i).source ∧ ContDiffAt ℝ ∞ (u ∘ (A.chart i).symm) (A.chart i x)) → Smooth n (fun y : U => z y) (fun y : U => u y)) ∧ (∀ φ : Y → ℝ, (∀ x ∈ U, ∃ i, x ∈ (A.chart i).source ∧ ContDiffAt ℝ ∞ (φ ∘ (A.chart i).symm) (A.chart i x)) → SmoothR n (fun y : U => z y) (fun y : U => φ y)) := by
  intro n Y _ _ _ _ _ ι La _ A U z hE
  refine ⟨fun u hu => etaleSmooth_complex hE u hu, fun φ hφ => ?_⟩
  refine etaleSmooth_complex hE (fun y => (φ y : ℂ)) fun x hx => ?_
  obtain ⟨i, hi, h⟩ := hφ x hx
  exact ⟨i, hi, Complex.ofRealCLM.contDiff.contDiffAt.comp _ h⟩

end GlobalTheory.OTY
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem Etale.contDiffAt_chart {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La]
    {A : WeightedAtlas n Y ι La} {U : Set Y} {z : Y → V n} (hE : Etale A U z) {x : Y} (hx : x ∈ U)
    {i : ι} (hi : x ∈ (A.chart i).source) :
    ContDiffAt ℂ ∞ (z ∘ (A.chart i).symm) (A.chart i x) := by
  have hS : IsOpen ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) :=
    (A.chart i).isOpen_inter_preimage_symm hE.isOpen
  have hmem : A.chart i x ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹' U :=
    ⟨(A.chart i).map_source hi, by simp [(A.chart i).left_inv hi, hx]⟩
  rw [contDiffAt_euclidean]
  intro k
  have hk : DifferentiableOn ℂ (fun w => (z ∘ (A.chart i).symm) w k)
      ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) :=
    (EuclideanSpace.proj (𝕜 := ℂ) k).differentiable.comp_differentiableOn (hE.holo i)
  exact (contDiffOn_of_differentiableOn n _ _ hS hk).contDiffAt (hS.mem_nhds hmem)

theorem etale_local_inverse : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (U : Set Y) (z : Y → V n), Etale A U z → ∀ e : OpenPartialHomeomorph U (V n), IsChart n (fun y : U => z y) e → ∀ v ∈ e.target, ∀ i, ((e.symm v : U) : Y) ∈ (A.chart i).source → ContDiffAt ℂ ∞ (fun v' => A.chart i (e.symm v' : U)) v ∧ (∀ᶠ v' in 𝓝 v, ((e.symm v' : U) : Y) ∈ (A.chart i).source) ∧ ∀ ξ : V n, fderiv ℂ (fun v' => A.chart i (e.symm v' : U)) v (jz A z i (e.symm v : U) ξ) = ξ := by
  intro n Y _ _ _ _ _ ι La _ A U z hE e he v hv i hi
  set g : V n → V n := z ∘ (A.chart i).symm with hg_def
  have hg : ContDiffAt ℂ ∞ g (A.chart i (e.symm v : U)) := hE.contDiffAt_chart (e.symm v).2 hi
  have hdet : (jz A z i (e.symm v : U)).det ≠ 0 := hE.det_ne i _ (e.symm v).2 hi
  set f' : V n ≃L[ℂ] V n :=
    (jz A z i (e.symm v : U)).toContinuousLinearEquivOfDetNeZero hdet with hf'_def
  have hf'coe : (f' : V n →L[ℂ] V n) = fderiv ℂ g (A.chart i (e.symm v : U)) := by
    ext w; rfl
  have hf' : HasFDerivAt g (f' : V n →L[ℂ] V n) (A.chart i (e.symm v : U)) := by
    rw [hf'coe]; exact (hg.differentiableAt (by simp)).hasFDerivAt
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hstrict := hg.hasStrictFDerivAt' hf' hn

  have hgv : g (A.chart i (e.symm v : U)) = v := by
    have h1 : z (e.symm v : U) = e (e.symm v) := he (e.map_target hv)
    show z ((A.chart i).symm (A.chart i (e.symm v : U))) = v
    rw [(A.chart i).left_inv hi, h1, e.right_inv hv]

  set h : V n → V n := fun v' => A.chart i (e.symm v' : U) with hh_def
  have hcoe : ContinuousAt (fun v' => ((e.symm v' : U) : Y)) v :=
    continuous_subtype_val.continuousAt.comp (e.continuousAt_symm hv)
  have hhc : ContinuousAt h v :=
    ContinuousAt.comp (g := A.chart i) (f := fun v' => ((e.symm v' : U) : Y)) (x := v)
      ((A.chart i).continuousAt hi) hcoe
  have hsrc : ∀ᶠ v' in 𝓝 v, ((e.symm v' : U) : Y) ∈ (A.chart i).source :=
    hcoe.preimage_mem_nhds ((A.chart i).open_source.mem_nhds hi)
  have htgt : ∀ᶠ v' in 𝓝 v, v' ∈ e.target := e.open_target.mem_nhds hv

  have hright : ∀ᶠ v' in 𝓝 v, g (h v') = v' := by
    filter_upwards [hsrc, htgt] with v' h1 h2
    have h3 : z (e.symm v') = e (e.symm v') := he (e.map_target h2)
    show z ((A.chart i).symm (A.chart i (e.symm v' : U))) = v'
    rw [(A.chart i).left_inv h1, h3, e.right_inv h2]

  have hleft : ∀ᶠ v' in 𝓝 v,
      hstrict.localInverse g f' (A.chart i (e.symm v : U)) (g (h v')) = h v' :=
    hhc.tendsto.eventually hstrict.eventually_left_inverse
  have heq : h =ᶠ[𝓝 v] hstrict.localInverse g f' (A.chart i (e.symm v : U)) := by
    filter_upwards [hleft, hright] with v' h1 h2
    rw [← h1, h2]
  have hinv := hstrict.to_localInverse
  rw [hgv] at hinv
  have hGc : ContDiffAt ℂ ∞ (hstrict.localInverse g f' (A.chart i (e.symm v : U))) v := by
    have := hg.to_localInverse hf' hn
    rw [hgv] at this
    exact this
  refine ⟨hGc.congr_of_eventuallyEq heq, hsrc, fun ξ => ?_⟩
  have hfd : fderiv ℂ h v = (f'.symm : V n →L[ℂ] V n) :=
    heq.fderiv_eq.trans hinv.hasFDerivAt.fderiv
  change fderiv ℂ h v (jz A z i (e.symm v : U) ξ) = ξ
  rw [hfd]
  exact f'.symm_apply_apply ξ

end GlobalTheory.OTY
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.LCSec

variable (X : Type) [TopologicalSpace X] (B : Type) [CommRing B]

def preQ {S T : DiscreteQuotient X} (h : T ≤ S) : (S → B) →+* (T → B) where
  toFun g t := g (DiscreteQuotient.ofLE h t)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def stage : (DiscreteQuotient X)ᵒᵖ ⥤ CommRingCat.{0} where
  obj S := CommRingCat.of (S.unop → B)
  map f := CommRingCat.ofHom (preQ X B (leOfHom f.unop))
  map_id S := by
    refine CommRingCat.hom_ext (RingHom.ext fun g => funext fun t => ?_)
    exact congrArg g (DiscreteQuotient.ofLE_refl_apply t)
  map_comp f g := by
    refine CommRingCat.hom_ext (RingHom.ext fun h => funext fun t => ?_)
    exact congrArg h (DiscreteQuotient.ofLE_ofLE _ _ t).symm

def pullQ (S : DiscreteQuotient X) : (S → B) →+* LocallyConstant X B where
  toFun g := ⟨fun x => g (S.proj x), S.proj_isLocallyConstant.comp g⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def lcCocone : Cocone (stage X B) where
  pt := CommRingCat.of (LocallyConstant X B)
  ι := { app := fun S => CommRingCat.ofHom (pullQ X B S.unop)
         naturality := fun S T f => by
           refine CommRingCat.hom_ext (RingHom.ext fun g => LocallyConstant.ext fun x => ?_)
           exact congrArg g (DiscreteQuotient.ofLE_proj _ x) }

def lcCoconeIsColimit : IsColimit (lcCocone X B) := by
  haveI : ReflectsColimitsOfShape (DiscreteQuotient X)ᵒᵖ (forget CommRingCat.{0}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  apply isColimitOfReflects (forget CommRingCat.{0})
  apply Types.FilteredColimit.isColimitOf
  · intro f
    refine ⟨op f.discreteQuotient, ⇑f.lift, ?_⟩
    exact LocallyConstant.ext fun x => rfl
  · intro S T g h e
    change pullQ X B S.unop g = pullQ X B T.unop h at e
    refine ⟨op (S.unop ⊓ T.unop), (homOfLE inf_le_left).op, (homOfLE inf_le_right).op, ?_⟩
    change preQ X B _ g = preQ X B _ h
    funext q
    obtain ⟨x, rfl⟩ := DiscreteQuotient.proj_surjective _ q
    have hx := congrArg (fun φ : LocallyConstant X B => φ x) e
    change g (S.unop.proj x) = h (T.unop.proj x) at hx
    exact (congrArg g (DiscreteQuotient.ofLE_proj _ x)).trans (hx.trans (congrArg h (DiscreteQuotient.ofLE_proj _ x).symm))

end GlobalTheory.EtC.LCSec

namespace GlobalTheory.EtC.LCSec

theorem res_res {R : Type} [CommRing R] {F : Shv R} {U V W : Scheme.{0}} (a : W ⟶ V) (b : V ⟶ U) (y : Sec F U) :
    Sec.res a (Sec.res b y) = Sec.res (a ≫ b) y := by
  simp [Sec.res]

theorem sec_pi_bijective (R : Type) [CommRing R] (F : Shv R) (B : Type) [CommRing B] (S : Type) [Finite S] :
    Function.Bijective (fun (y : Sec F (Spec (CommRingCat.of (S → B)))) (s : S) =>
      Sec.res (Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : S => B) s))) y) := by
  obtain ⟨hc⟩ := GlobalTheory.EtC.spec_pi_cofan_isColimit S (fun _ => B) (S → B) (RingEquiv.refl _)
  exact GlobalTheory.T.etaleModuleSheaf_sections_coprod_bijective R F _ S _ _ hc

theorem res_eval_pullQ (R : Type) [CommRing R] (F : Shv R) (X : Type) [TopologicalSpace X] (B : Type) [CommRing B]
    (S : DiscreteQuotient X) (y : Sec F (Spec (CommRingCat.of (S → B)))) (x : X) :
    Sec.res (Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom x)))
        (Sec.res (Spec.map (CommRingCat.ofHom (pullQ X B S))) y) =
      Sec.res (Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : S => B) (S.proj x)))) y := by
  rw [res_res, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

end GlobalTheory.EtC.LCSec


open GlobalTheory.EtC.LCSec in
theorem GlobalTheory.EtC.sec_locallyConstant : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] (B : Type) [CommRing B], (∀ t : Sec F (Spec (CommRingCat.of (LocallyConstant X B))), IsLocallyConstant (fun x : X => Sec.res (Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom x))) t)) ∧ Function.Injective (fun (t : Sec F (Spec (CommRingCat.of (LocallyConstant X B)))) (x : X) => Sec.res (Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom x))) t) ∧ ∀ ψ : X → Sec F (Spec (CommRingCat.of B)), IsLocallyConstant ψ → ∃ t : Sec F (Spec (CommRingCat.of (LocallyConstant X B))), ∀ x, Sec.res (Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom x))) t = ψ x := by
  intro R _ F hF X _ _ B _
  have hfin := ((GlobalTheory.T.preservesFilteredColimits_moduleCat_iff_forget_iff_elements (ULift.{1} R) (onRings F)).2.mp hF) _ (stage X B) (lcCocone X B) (lcCoconeIsColimit X B)
  have hrep : ∀ t : Sec F (Spec (CommRingCat.of (LocallyConstant X B))), ∃ (S : DiscreteQuotient X)
      (y : Sec F (Spec (CommRingCat.of (S → B)))), Sec.res (Spec.map (CommRingCat.ofHom (pullQ X B S))) y = t := by
    intro t
    obtain ⟨S, y, hy⟩ := hfin.1 t
    exact ⟨S.unop, y, hy⟩
  have hzero : ∀ t : Sec F (Spec (CommRingCat.of (LocallyConstant X B))),
      (∀ x, Sec.res (Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom x))) t = 0) → t = 0 := by
    intro t ht
    obtain ⟨S, y, rfl⟩ := hrep t
    have hall : ∀ s : S, Sec.res (Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : S => B) s))) y = 0 := by
      intro s
      obtain ⟨x, rfl⟩ := DiscreteQuotient.proj_surjective _ s
      rw [← res_eval_pullQ]
      exact ht x
    have hy : y = 0 := by
      apply (sec_pi_bijective R F B S).1
      funext s
      exact (hall s).trans (map_zero _).symm
    rw [hy]
    exact map_zero _
  refine ⟨fun t => ?_, fun t₁ t₂ h => ?_, fun ψ hψ => ?_⟩
  · obtain ⟨S, y, rfl⟩ := hrep t
    have he : (fun x : X => Sec.res (Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom x)))
        (Sec.res (Spec.map (CommRingCat.ofHom (pullQ X B S))) y)) =
        (fun s : S => Sec.res (Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : S => B) s))) y) ∘ S.proj :=
      funext fun x => res_eval_pullQ R F X B S y x
    rw [he]
    exact S.proj_isLocallyConstant.comp _
  · have h0 := hzero (t₁ - t₂) fun x => by
      change (F.obj.map _).hom (t₁ - t₂) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr (congrFun h x)
    exact sub_eq_zero.mp h0
  · let f : LocallyConstant X (Sec F (Spec (CommRingCat.of B))) := ⟨ψ, hψ⟩
    obtain ⟨y, hy⟩ := (sec_pi_bijective R F B f.discreteQuotient).2 (⇑f.lift)
    refine ⟨Sec.res (Spec.map (CommRingCat.ofHom (pullQ X B f.discreteQuotient))) y, fun x => ?_⟩
    rw [res_eval_pullQ]
    exact congrFun hy (f.discreteQuotient.proj x)
end
end

section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem _root_.GlobalTheory.T.span_regularForms_finite_projective_smooth : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (B : Subalgebra k K) [IsFractionRing B K] [Algebra.Smooth k B] (p : ℕ) (W : Type) [AddCommGroup W] [Module K W] [Module k W] [IsScalarTower k K W] (e : W →ₗ[K] DR k K), Function.Injective e → LinearMap.range e = ⋀[K]^p Ω[K⁄k] → Module.Finite B (Submodule.span B ((omB k K B p).comap (e.restrictScalars k) : Set W)) ∧ Module.Projective B (Submodule.span B ((omB k K B p).comap (e.restrictScalars k) : Set W)) := by
  first | (exact @GlobalTheory.PD.span_omB_comap_finite_projective) | (exact GlobalTheory.PD.span_omB_comap_finite_projective) | (intros; apply GlobalTheory.PD.span_omB_comap_finite_projective  <;> assumption)
end

section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem _root_.GlobalTheory.T.regular_topForm_pole_order_height_one_prime : ∀ (k F K : Type) [Field k] [CharZero k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] [FiniteDimensional F K] (d : ℕ) (u : Fin d → F), AlgebraicIndependent k u → ∀ (A : Subalgebra k F) [IsFractionRing A F], A = Algebra.adjoin k (Set.range u) → ∀ (B : Subalgebra k K), B = (integralClosure A K).restrictScalars k → Algebra.Smooth k B → ∀ τ : DR k K →ₗ[K] K, τ (ExteriorAlgebra.ιMulti K d fun j => D k K (algebraMap F K (u j))) = 1 → ∀ (Q : Ideal B), Q.IsPrime → Q.height = 1 → ∀ (t : A) (s : B) (e : ℕ), Irreducible t → 1 ≤ e → s ∈ Q → (∀ y ∈ Q, ∃ c r : B, r ∉ Q ∧ r * y = c * s) → (∃ a r : B, a ∉ Q ∧ r ∉ Q ∧ (r : K) * algebraMap F K t = a * s ^ e) → ∀ z : K, (∃ r : B, r ∉ Q ∧ ∃ y ∈ omB k K B d, τ y = r * z) ↔ ∃ c r : B, r ∉ Q ∧ (r : K) * s ^ (e - 1) * z = c := by
  first | (exact @GlobalTheory.PD.omB_top_coeff_iff_pole) | (exact GlobalTheory.PD.omB_top_coeff_iff_pole) | (intros; apply GlobalTheory.PD.omB_top_coeff_iff_pole  <;> assumption)
end

section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

theorem _root_.GlobalTheory.T.bicharacterFourierTransform_twice_eq_pos_smul_reflect : ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] (_ : Good X) (μ : Measure X) [μ.IsAddHaarMeasure] (e : X → X → ℂ), IsPair e → ∃ C : ℝ, 0 < C ∧ ∀ φ ∈ SB X, ∀ x, four μ e (four μ e φ) x = (C : ℂ) * φ (-x) := by
  first | exact @GlobalTheory.KSp.four_four | exact GlobalTheory.KSp.four_four | (intros; apply GlobalTheory.KSp.four_four <;> assumption)
end

section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

theorem _root_.GlobalTheory.T.hasGaussIntegral_comp_addEquiv_rescale : ∀ (X Y : Type) [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [AddCommGroup Y] [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] (μ : Measure X) (μ' : Measure Y) (T : X ≃ₜ+ Y) (r : NNReal) (f : Y → ℂ) (γ : ℂ), μ.map T = r • μ' → HasGauss μ' f γ → HasGauss μ (fun x => f (T x)) ((r : ℝ) * γ) := by
  first | exact @GlobalTheory.KSp.hasGauss_comp_equiv | exact GlobalTheory.KSp.hasGauss_comp_equiv | (intros; apply GlobalTheory.KSp.hasGauss_comp_equiv <;> assumption)
end
