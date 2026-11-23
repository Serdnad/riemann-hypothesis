module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle047
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle076
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle029
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle019
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PHolomorphicFibreInfinite
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle073
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ImplicitContDiff
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.MemMinimalPrimesOfMemDivSuppDivSupp

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

theorem LelongWeightDiff.proof (hM : ChartMassCompact.Statement) : LelongWeightDiff.Statement := by
  classical
  intro n d J u g k φ hJ hdim hu hg hgc hφ hk hkpos
  have hψ : ∀ i, SmoothNear (zeroSet J) (vecCons g φ i) := fun i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (⟨Set.univ, isOpen_univ, Set.subset_univ _, hg.contDiffOn⟩ : SmoothNear (zeroSet J) g)
    · simpa using hφ j
  have hcs : ∃ i, HasCompactSupport (vecCons g φ i) := ⟨0, by simpa using hgc⟩
  by_cases hA : ∃ A : Matrix (Fin (d + 1)) (Fin n) ℂ, IsFiniteProjection J A
  swap
  · simp only [varInt, dif_neg hA, sub_self]; exact tendsto_const_nhds
  simp only [varInt, dif_pos hA]
  set A := hA.choose
  have hAf : IsFiniteProjection J A := hA.choose_spec
  have hfin : ∀ y, (_root_.GroundTheory.Heights₂.Heights.ComplexSets.fibre J A y).Finite := fun y => (FibreBound.proof n (d + 1) J A hJ hdim hAf y).2.1
  have hkc : ContinuousOn k (zeroSet J) := by
    obtain ⟨U, -, hU, hkU⟩ := hk; exact hkU.continuousOn.mono hU
  have hlc : Continuous fun x => ‖linEval u x‖ ^ 2 := ((contDiff_linEval u).continuous.norm).pow 2
  set D : ℝ → (Fin n → ℂ) → ℝ := fun ε x => Real.log (‖linEval u x‖ ^ 2 + ε * k x ^ 2) / 2 - logReg u ε x
  have hWc : ∀ ε : ℝ, 0 < ε →
      ContinuousOn (fun x => Real.log (‖linEval u x‖ ^ 2 + ε * k x ^ 2) / 2) (zeroSet J) := fun ε hε =>
    ((hlc.continuousOn.add (continuousOn_const.mul (hkc.pow 2))).log fun x hx => by
      exact (add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos hε (pow_pos (hkpos x hx) 2))).ne').div_const 2
  have hLc : ∀ ε : ℝ, 0 < ε → ContinuousOn (logReg u ε) (zeroSet J) := fun ε hε =>
    (contDiff_logReg u hε).continuous.continuousOn
  have hint : ∀ f, ContinuousOn f (zeroSet J) → Integrable (chartDens J A f (vecCons g φ)) := fun f hf =>
    (hM n (d + 1) J A f _ hJ hdim hAf hf hψ (Or.inr hcs)).mono'
      (LelongWeightDiff.measurable_chartDens hJ hdim hAf hf hψ).aestronglyMeasurable
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact LelongWeightDiff.abs_chartDens_le _ _ (hfin y))
  have heq : (fun ε : ℝ => ∫ y, chartDens J A (D ε) (vecCons g φ) y) =ᶠ[𝓝[>] 0]
      fun ε => chartInt J A (fun x => Real.log (‖linEval u x‖ ^ 2 + ε * k x ^ 2) / 2) (vecCons g φ) -
        chartInt J A (logReg u ε) (vecCons g φ) := by
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    rw [chartInt, chartInt, ← integral_sub (hint _ (hWc ε hε)) (hint _ (hLc ε hε))]
    exact integral_congr_ae (Eventually.of_forall fun y =>
      (LelongWeightDiff.chartDens_sub _ _ _ (hfin y)).symm)
  refine Tendsto.congr' heq ?_
  obtain ⟨P, hP0, hPu⟩ := LelongWeightDiff.exists_poly_of_linEval_eq_zero J A hAf u hu
  have h := tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := 𝓝[>] (0 : ℝ))
    (F := fun ε => chartDens J A (D ε) (vecCons g φ)) (f := fun _ => (0 : ℝ))
    (chartAbsDens J A (fun x => Real.log (k x)) (vecCons g φ)) ?_ ?_
    (hM n (d + 1) J A _ _ hJ hdim hAf (hkc.log fun x hx => (hkpos x hx).ne') hψ (Or.inr hcs)) ?_
  · rwa [integral_zero] at h
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    exact (LelongWeightDiff.measurable_chartDens hJ hdim hAf ((hWc ε hε).sub (hLc ε hε)) hψ).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    refine Eventually.of_forall fun y => ?_
    rw [Real.norm_eq_abs]
    unfold chartDens chartAbsDens
    simp only [CutOffDominated.sheetSum_eq_sum _ (hfin y)]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x hx => ?_)
    rw [Set.Finite.mem_toFinset] at hx
    split_ifs
    · rw [abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_right
        (LelongWeightDiff.abs_half_log_sub_le (sq_nonneg _) hε (hkpos x hx.1)) (abs_nonneg _)
    · simp
  · filter_upwards [CutOffDominated.ae_eval_ne_zero P hP0] with y hy
    unfold chartDens
    simp only [CutOffDominated.sheetSum_eq_sum _ (hfin y)]
    refine LelongWeightDiff.tendsto_finset_sum_zero _ _ fun x hx => ?_
    rw [Set.Finite.mem_toFinset] at hx
    by_cases hs : ∃ s, IsSheetAt J A x s
    swap
    · simp only [dif_neg hs]; exact tendsto_const_nhds
    simp only [dif_pos hs]
    have hux : linEval u x ≠ 0 := fun h0 => hy (by rw [← hx.2]; exact hPu x hx.1 h0)
    have ha : 0 < ‖linEval u x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hux) 2
    have hc : ContinuousAt (fun ε : ℝ => D ε x) 0 := by
      simp only [D, logReg]
      refine ((ContinuousAt.log (by fun_prop) ?_).div_const 2).sub
        ((ContinuousAt.log (by fun_prop) ?_).div_const 2) <;> simp [hux]
    have h0 : D 0 x = 0 := by simp [D, logReg]
    simpa [h0] using ((hc.tendsto.mono_left nhdsWithin_le_nhds).mul_const
      (ReciprocityTheory.AnForm.maDens (fun i => vecCons g φ i ∘ hs.choose) y))

end GroundTheory.Heights₂.Heights.Targets
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

section Objects

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {Ω : Type*} [Field Ω]

def curveSectionMod (y : (Σ k, ι k) → Ω) (a : K → ℤ) : Submodule (curveRing y) Ω where
  carrier := chartLat y a 1
  zero_mem' := (chartLat y a 1).zero_mem
  add_mem' := fun ha hb => (chartLat y a 1).add_mem ha hb
  smul_mem' := fun b m hm c hc => by
    have hb : (b : Ω) ∈ chartRingZ y c := mem_curveRing.mp b.2 c hc
    have hm' := hm c hc
    rw [Subring.smul_def, smul_eq_mul, mul_assoc]
    exact mul_mem hb hm'

abbrev curveSectionQuot (y : (Σ k, ι k) → Ω) (a : K → ℤ) (x : Ω) : Type _ :=
  ↥(curveSectionMod y a) ⧸ (Submodule.span (curveRing y) {x}).comap (curveSectionMod y a).subtype

end Objects

def CurveSectionQuotFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (s : MRing ι) (d : K → ℕ),
    IsArithVar (mCoordIdeal y) 1 → _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s d → s ∉ mCoordIdeal y →
      Finite (curveSectionQuot y (fun k => (d k : ℤ)) (aeval y s))

def CurveVertPointLength.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (s : MRing ι) (d : K → ℕ),
    IsArithVar (mCoordIdeal y) 1 → _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s d → s ∉ mCoordIdeal y →
      Set.BijOn (curvePtIdeal y) (divSupp (mCoordIdeal y) s)
          {m | m.IsMaximal ∧ locLen m (curveSectionQuot y (fun k => (d k : ℤ)) (aeval y s)) ≠ 0} ∧
        ∀ W ∈ divSupp (mCoordIdeal y) s,
          multAt (mCoordIdeal y ⊔ Ideal.span {s}) W =
            locLen (curvePtIdeal y W) (curveSectionQuot y (fun k => (d k : ℤ)) (aeval y s))

def CurveVertPointResidue.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (s : MRing ι) (d : K → ℕ),
    IsArithVar (mCoordIdeal y) 1 → _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s d → s ∉ mCoordIdeal y →
      ∀ W ∈ divSupp (mCoordIdeal y) s,
        (geoNum 0 W Fin.elim0 : ℝ) * Real.log (charOf W) =
          Real.log (Nat.card (curveRing y ⧸ curvePtIdeal y W))

end

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

instance isPrime_map_C_maximalIdeal_mv (K : Type*) (R : Type*) [CommRing R] [IsLocalRing R] :
    ((IsLocalRing.maximalIdeal R).map (MvPolynomial.C : R →+* MvPolynomial K R)).IsPrime := by
  rw [← Ideal.mk_ker (I := IsLocalRing.maximalIdeal R), ← MvPolynomial.ker_map]
  exact RingHom.ker_isPrime _

abbrev mNagataRing (K : Type*) (R : Type*) [CommRing R] [IsLocalRing R] : Type _ :=
  Localization.AtPrime ((IsLocalRing.maximalIdeal R).map (MvPolynomial.C : R →+* MvPolynomial K R))

def CurveVertPointNagata.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (s : MRing ι) (d : K → ℕ),
    IsArithVar (mCoordIdeal y) 1 → _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s d → s ∉ mCoordIdeal y →
      ∀ W ∈ divSupp (mCoordIdeal y) s, ∀ c : ∀ k, ι k, (∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ W) →
        ∀ [W.IsPrime] [(curvePtIdeal y W).IsPrime] (a b : (Σ k, ι k) → curveRing y)
          (hb : ∀ p, b p ∉ curvePtIdeal y W), (∀ p, (b p : Ω) * (y p / y ⟨p.1, c p.1⟩) = a p) →
          ∃ Φ : Localization.AtPrime W →+* mNagataRing K (Localization.AtPrime (curvePtIdeal y W)),
            Function.Surjective Φ ∧
            RingHom.ker Φ = (mCoordIdeal y).map (algebraMap (MRing ι) _) ∧
            ∀ f : MRing ι, Φ (algebraMap _ _ f) =
              algebraMap (MvPolynomial K (Localization.AtPrime (curvePtIdeal y W))) _
                (aeval (fun p : (Σ k, ι k) => MvPolynomial.C (IsLocalization.mk'
                  (Localization.AtPrime (curvePtIdeal y W)) (a p)
                  (⟨b p, hb p⟩ : (curvePtIdeal y W).primeCompl)) * MvPolynomial.X p.1) f)

end

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Topology Metric

noncomputable section

theorem CriticalFibreInfinite.proof : CriticalFibreInfinite.Statement := by
  intro k d U f hU hUne hf hninj
  classical
  have hfa : AnalyticOnNhd ℂ f U :=
    GroundTheory.Heights₂.Heights.ImplicitCurve.analyticOnNhd_of_differentiableOn hU hf

  let Q : ℕ → Prop := fun m => ∃ t ∈ U, ∃ v : Fin m → Fin k → ℂ,
    LinearIndependent ℂ (fun j => fderiv ℂ f t (v j))
  have hQ0 : Q 0 := by
    obtain ⟨t, ht⟩ := hUne
    exact ⟨t, ht, Fin.elim0, linearIndependent_empty_type⟩
  have hspec : Q (Nat.findGreatest Q d) := Nat.findGreatest_spec (Nat.zero_le d) hQ0
  have hle : ∀ m, m ≤ d → Q m → m ≤ Nat.findGreatest Q d := fun m hmd hm => Nat.le_findGreatest hmd hm
  have hrd : Nat.findGreatest Q d ≤ d := Nat.findGreatest_le d
  generalize Nat.findGreatest Q d = r at hspec hle hrd
  obtain ⟨s, hs, v, hv⟩ := hspec
  have hmax : ∀ t ∈ U, ∀ u : Fin (r + 1) → Fin k → ℂ,
      ¬ LinearIndependent ℂ (fun j => fderiv ℂ f t (u j)) := by
    intro t ht u hu
    have hcard : r + 1 ≤ d := by simpa using hu.fintype_card_le_finrank
    have := hle (r + 1) hcard ⟨t, ht, u, hu⟩
    omega

  let T : (Fin r → ℂ) →ₗ[ℂ] (Fin d → ℂ) := Fintype.linearCombination ℂ (fun j => fderiv ℂ f s (v j))
  have hT : LinearMap.ker T = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    funext j
    exact Fintype.linearIndependent_iff.1 hv c (by simpa [T, Fintype.linearCombination_apply] using hc) j
  obtain ⟨Λ, hΛ⟩ := T.exists_leftInverse_of_injective hT
  have hΛv : ∀ j, Λ (fderiv ℂ f s (v j)) = Pi.single j 1 := by
    intro j
    have := congrArg (fun g => g (Pi.single j (1 : ℂ))) hΛ
    simpa [T, Fintype.linearCombination_apply_single] using this
  let Λc : (Fin d → ℂ) →L[ℂ] (Fin r → ℂ) := LinearMap.toContinuousLinearMap Λ
  have hΛc : ∀ y, Λc y = Λ y := fun y => rfl

  have hev : ∀ᶠ t in 𝓝 s, t ∈ U ∧ LinearIndependent ℂ (fun j => Λ (fderiv ℂ f t (v j))) := by
    have hUev : ∀ᶠ t in 𝓝 s, t ∈ U := hU.mem_nhds hs
    refine hUev.and ?_
    have hDcont : ContinuousAt (fderiv ℂ f) s := (hfa.fderiv s hs).continuousAt
    have hc : ContinuousAt (fun t => fun j => Λc (fderiv ℂ f t (v j))) s := by
      refine continuousAt_pi.2 fun j => ?_
      exact Λc.continuous.continuousAt.comp
        ((ContinuousLinearMap.apply ℂ (Fin d → ℂ) (v j)).continuous.continuousAt.comp hDcont)
    have h0 : LinearIndependent ℂ (fun j => Λc (fderiv ℂ f s (v j))) := by
      have : (fun j => Λc (fderiv ℂ f s (v j))) = ⇑(Pi.basisFun ℂ (Fin r)) := by
        funext j
        simp [hΛc, hΛv]
      rw [this]
      exact (Pi.basisFun ℂ (Fin r)).linearIndependent
    exact hc.eventually h0.eventually

  obtain ⟨w, hw, hw0⟩ : ∃ w ∈ LinearMap.ker (Λ ∘ₗ (fderiv ℂ f s : (Fin k → ℂ) →ₗ[ℂ] (Fin d → ℂ))), w ≠ 0 := by
    obtain ⟨x, y, hxy, hne⟩ := Function.not_injective_iff.1 (hninj s hs)
    refine ⟨x - y, ?_, sub_ne_zero.2 hne⟩
    simp [map_sub, hxy]
  have hw' : Λ (fderiv ℂ f s w) = 0 := by simpa using hw

  let A' : ℂ × (Fin r → ℂ) →L[ℂ] (Fin k → ℂ) :=
    (ContinuousLinearMap.fst ℂ ℂ (Fin r → ℂ)).smulRight w +
      ∑ j, ((ContinuousLinearMap.proj j).comp (ContinuousLinearMap.snd ℂ ℂ (Fin r → ℂ))).smulRight (v j)
  have hA' : ∀ p : ℂ × (Fin r → ℂ), A' p = p.1 • w + ∑ j, p.2 j • v j := by
    intro p
    simp [A']
  have hLA : ∀ p : ℂ × (Fin r → ℂ), Λ (fderiv ℂ f s (A' p)) = p.2 := by
    intro p

    rw [hA', map_add (f := _), map_add (f := _), map_smul, map_smul, hw', smul_zero, zero_add, map_sum, map_sum]
    simp only [map_smul, hΛv]
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  let H : ℂ × (Fin r → ℂ) → Fin r → ℂ := fun p => Λc (f (s + A' p))
  have hfs : AnalyticAt ℂ f s := hfa s hs
  have hHd : HasFDerivAt H (Λc.comp ((fderiv ℂ f s).comp A')) 0 := by
    have h1 : HasFDerivAt (fun p => s + A' p) A' (0 : ℂ × (Fin r → ℂ)) := A'.hasFDerivAt.const_add s
    have h2 : HasFDerivAt f (fderiv ℂ f s) (s + A' 0) := by
      simpa using hfs.differentiableAt.hasFDerivAt
    exact Λc.hasFDerivAt.comp _ (HasFDerivAt.comp (f := fun p => s + A' p) (0 : ℂ × (Fin r → ℂ)) h2 h1)
  have hHc : ContDiffAt ℂ 1 H 0 := by
    have hf1 : ContDiffAt ℂ 1 f (s + A' 0) := by simpa using hfs.contDiffAt
    exact Λc.contDiff.contDiffAt.comp _
      (ContDiffAt.comp (f := fun p => s + A' p) (0 : ℂ × (Fin r → ℂ)) hf1 (contDiff_const.add A'.contDiff).contDiffAt)
  have hinv : (fderiv ℂ H 0 ∘L ContinuousLinearMap.inr ℂ ℂ (Fin r → ℂ)).IsInvertible := by
    have : fderiv ℂ H 0 ∘L ContinuousLinearMap.inr ℂ ℂ (Fin r → ℂ) =
        ContinuousLinearMap.id ℂ (Fin r → ℂ) := by
      rw [hHd.fderiv]
      refine ContinuousLinearMap.ext fun c => ?_
      simpa [hΛc] using hLA (0, c)
    rw [this]
    exact ⟨ContinuousLinearEquiv.refl ℂ _, rfl⟩

  have hψc := hHc.contDiffAt_implicitFunction one_ne_zero hinv
  set ψ := hHc.implicitFunction one_ne_zero hinv with hψ
  have hψ0 : ψ 0 = 0 := hHc.implicitFunction_apply_self one_ne_zero hinv
  have hψeq : ∀ᶠ z in 𝓝 (0 : ℂ), H (z, ψ z) = H 0 :=
    hHc.eventually_apply_implicitFunction one_ne_zero hinv
  have hψd : ∀ᶠ z in 𝓝 (0 : ℂ), DifferentiableAt ℂ ψ z :=
    (hψc.eventually (by simp)).mono fun z hz => hz.differentiableAt one_ne_zero
  let P : ℂ → Fin k → ℂ := fun z => s + A' (z, ψ z)
  have hP0 : P 0 = s := by simp [P, hψ0, hA']
  have hPcont : ContinuousAt P 0 :=
    continuousAt_const.add (A'.continuous.continuousAt.comp (continuousAt_id.prodMk hψc.continuousAt))
  rw [← hP0] at hev
  obtain ⟨δ, hδ, hball⟩ :=
    Metric.eventually_nhds_iff_ball.1 (((hPcont.eventually hev).and hψeq).and hψd)
  have hPd : ∀ z ∈ ball (0 : ℂ) δ, DifferentiableAt ℂ P z := fun z hz =>
    (differentiableAt_const _).add (A'.differentiableAt.comp z (differentiableAt_id.prodMk (hball z hz).2))
  have hPU : ∀ z ∈ ball (0 : ℂ) δ, P z ∈ U := fun z hz => (hball z hz).1.1.1
  have hfd : ∀ z ∈ ball (0 : ℂ) δ, DifferentiableAt ℂ f (P z) := fun z hz =>
    (hf _ (hPU z hz)).differentiableAt (hU.mem_nhds (hPU z hz))
  have hgP : ∀ z ∈ ball (0 : ℂ) δ, Λc (f (P z)) = Λc (f s) := by
    intro z hz
    have := (hball z hz).1.2
    simpa [H, P] using this

  have hzero : Set.EqOn (fderiv ℂ (fun z => f (P z))) 0 (ball (0 : ℂ) δ) := by
    intro z hz
    have hcomp : fderiv ℂ (fun z => f (P z)) z = (fderiv ℂ f (P z)).comp (fderiv ℂ P z) :=
      fderiv_comp z (hfd z hz) (hPd z hz)
    have hloc : (fun z => Λc (f (P z))) =ᶠ[𝓝 z] fun _ => Λc (f s) :=
      Filter.eventually_of_mem (isOpen_ball.mem_nhds hz) hgP
    have hg0 : fderiv ℂ (fun z => Λc (f (P z))) z = 0 := by
      rw [hloc.fderiv_eq]
      exact fderiv_const_apply _
    have hgc : fderiv ℂ (fun z => Λc (f (P z))) z = Λc.comp ((fderiv ℂ f (P z)).comp (fderiv ℂ P z)) := by
      rw [← hcomp]
      have h := fderiv_comp z Λc.differentiableAt ((hfd z hz).comp z (hPd z hz))
      rw [ContinuousLinearMap.fderiv] at h
      exact h
    have hx : Λ (fderiv ℂ f (P z) (fderiv ℂ P z 1)) = 0 := by
      have := congrArg (fun L => L 1) (hgc.symm.trans hg0)
      simpa [hΛc] using this
    have := IndefiniteRowSideFullHecke.ComplexSets.HolomorphicFibreInfinite.kernel_eq_of_maximal (fderiv ℂ f (P z)) v Λ (hmax _ (hPU z hz)) (hball z hz).1.1.2 hx
    rw [hcomp]
    refine ContinuousLinearMap.ext_ring ?_
    simpa using this
  have hconst : ∀ z ∈ ball (0 : ℂ) δ, f (P z) = f s := by
    intro z hz
    have := isOpen_ball.is_const_of_fderiv_eq_zero (convex_ball (0 : ℂ) δ).isPreconnected
      (fun z hz => ((hfd z hz).comp z (hPd z hz)).differentiableWithinAt) hzero hz (mem_ball_self hδ)
    simpa [hP0] using this

  have hPinj : Function.Injective P := by
    intro z z' hzz
    have hψz : ψ z = ψ z' := by
      have h1 := hLA (z, ψ z)
      have h2 := hLA (z', ψ z')
      have : A' (z, ψ z) = A' (z', ψ z') := add_left_cancel hzz
      rw [this] at h1
      exact h1.symm.trans h2
    have : A' (z, ψ z) = A' (z', ψ z') := add_left_cancel hzz
    rw [hA', hA', hψz] at this
    have h3 : z • w = z' • w := add_right_cancel this
    exact smul_left_injective ℂ hw0 h3
  refine ⟨f s, ?_⟩
  have hinf : (ball (0 : ℂ) δ).Infinite := infinite_of_mem_nhds (0 : ℂ) (ball_mem_nhds 0 hδ)
  refine (hinf.image hPinj.injOn).mono ?_
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨hPU z hz, hconst z hz⟩

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

universe u v w

theorem multAt_pos_of_mem_divSupp_field {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    {F : Type*} [Field F] {V W : Ideal (MRingOver F ι)} {f : MRingOver F ι}
    (hW : W ∈ divSupp V f) : 0 < multAt (V ⊔ Ideal.span {f}) W := by
  have hmin := hW.1
  have hWp : W.IsPrime := hmin.1.1
  have hm : IsLocalRing.maximalIdeal (Localization.AtPrime W) ∈
      ((V ⊔ Ideal.span {f}).map (algebraMap (MRingOver F ι) (Localization.AtPrime W))).minimalPrimes := by
    rw [IsLocalization.minimalPrimes_map W.primeCompl (Localization.AtPrime W)]
    rw [Set.mem_preimage, Localization.AtPrime.under_maximalIdeal]
    exact hmin
  have hne := SwapLoc.length_quot_ne_top_of_mem_minimalPrimes _ hm
  have : Nontrivial (Localization.AtPrime W ⧸
      (V ⊔ Ideal.span {f}).map (algebraMap (MRingOver F ι) (Localization.AtPrime W))) :=
    Ideal.Quotient.nontrivial_iff.mpr
      (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top hm.1.2)
  have hpos := Module.length_pos (R := Localization.AtPrime W)
    (M := Localization.AtPrime W ⧸
      (V ⊔ Ideal.span {f}).map (algebraMap (MRingOver F ι) (Localization.AtPrime W)))
  rw [multAt, dite_eq_left hWp, inh_length_locQuot]
  exact ENat.toNat_pos hpos.ne' hne

theorem SegreDivisor.proof (h₁ : SegreComponent.Statement.{u, v, w}) :
    SegreDivisor.Statement.{u, v, w} := by
  intro K _ ι _ F _ V n hV
  obtain ⟨i, hi⟩ : ∃ i : ∀ k, ι k, IsChart V i :=
    ⟨fun k => (hV.1.2.2 k).choose, fun k => (hV.1.2.2 k).choose_spec⟩
  refine ⟨_, isMultiHomog_coordProd (F := F) i (fun _ => 1), coordProd_not_mem hV.1.1 i hi _, ?_⟩
  obtain ⟨W, hW⟩ := h₁ K ι F V n _ hV (isMultiHomog_coordProd (F := F) i (fun _ => 1))
  intro h0
  have hpos := multAt_pos_of_mem_divSupp_field hW
  rw [← DivisorCycleSwap.divCycle_apply_of_mem hW, h0, Finsupp.zero_apply] at hpos
  exact lt_irrefl _ hpos

end GroundTheory.Heights₂.Heights.Targets
end
