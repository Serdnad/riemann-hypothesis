module

import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle069
public import Mathlib.RingTheory.KrullDimension.Basic
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle030
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PInvertibleIdealIndex
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.POrderIdealIndexExtension
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial

namespace BaseChangeMin

variable {σ : Type*} [Fintype σ] {F : Type*} [Field F] {F' : Type*} [Field F'] [Algebra F F']

section GD

attribute [local instance] MvPolynomial.algebraMvPolynomial



end GD

theorem ringKrullDim_quotient_le_of_minimalPrimes {R : Type*} [CommRing R] (I : Ideal R)
    {N : WithBot ℕ∞} (h : ∀ Z ∈ I.minimalPrimes, ringKrullDim (R ⧸ Z) ≤ N) :
    ringKrullDim (R ⧸ I) ≤ N := by
  apply GroundTheory.Heights₂.Heights.ComplexSets.quotient_dim_le_of_minimalPrimes <;> assumption

end BaseChangeMin

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsArithVar ptsIntegral pot segre PBlk)
open GroundTheory.Heights₂.Heights (varInt IsDegZeroSmooth segreChartSet segreChartComponents chartLift)

def SegreChartIntegralPoints.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (L : Fin 0 → HermLine ι) (g : ((Σ k, ι k) → ℂ) → ℝ) (δ : ℝ)
    (G : (Fin m → ℂ) → ℝ) (Φ : Fin 0 → (Fin m → ℂ) → ℝ),
    IsArithVar P 1 → IsDegZeroSmooth g → 0 < δ →
    (∀ z, ‖segre z i‖ < δ * ‖segre z‖ → g z = 0) →
    (∀ x ∈ segreChartSet P σ i, G =ᶠ[𝓝 x] g ∘ chartLift σ i) →
      ptsIntegral P (pot L) g = ∑ J ∈ segreChartComponents P σ i, varInt J 0 G Φ

end GroundTheory.Heights₂.Heights.Targets
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial Topology Filter ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem ResAboveCover.sameOrbit_symm {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') : SameOrbit z' z := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), funext fun p => ?_⟩
  simp [← mul_assoc, inv_mul_cancel₀ (hc p.1)]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem ResAboveCover.sameOrbit_trans {a b d : (Σ k, ι k) → ℂ} (h₁ : SameOrbit a b)
    (h₂ : SameOrbit b d) : SameOrbit a d := by
  obtain ⟨c, hc, rfl⟩ := h₁
  obtain ⟨c', hc', rfl⟩ := h₂
  exact ⟨fun k => c k * c' k, fun k => mul_ne_zero (hc k) (hc' k), funext fun p => by simp [mul_assoc]⟩


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem ResAboveCover.sameOrbit_of_tendsto {α : Type*} {l : Filter α} [l.NeBot]
    {v u : α → (Σ k, ι k) → ℂ} {v₀ u₀ : (Σ k, ι k) → ℂ}
    (hv : Tendsto v l (𝓝 v₀)) (hu : Tendsto u l (𝓝 u₀))
    (hvu : ∀ᶠ a in l, SameOrbit (v a) (u a))
    (hv₀ : ∀ k, ∃ i, v₀ ⟨k, i⟩ ≠ 0) (hu₀ : ∀ k, ∃ i, u₀ ⟨k, i⟩ ≠ 0) :
    SameOrbit v₀ u₀ := by
  choose i hi using hu₀
  have hcross : ∀ k j, v₀ ⟨k, j⟩ * u₀ ⟨k, i k⟩ = v₀ ⟨k, i k⟩ * u₀ ⟨k, j⟩ := by
    intro k j
    have h₁ : Tendsto (fun a => v a ⟨k, j⟩ * u a ⟨k, i k⟩) l (𝓝 (v₀ ⟨k, j⟩ * u₀ ⟨k, i k⟩)) :=
      ((continuous_apply _).continuousAt.tendsto.comp hv).mul
        ((continuous_apply _).continuousAt.tendsto.comp hu)
    have h₂ : Tendsto (fun a => v a ⟨k, i k⟩ * u a ⟨k, j⟩) l (𝓝 (v₀ ⟨k, i k⟩ * u₀ ⟨k, j⟩)) :=
      ((continuous_apply _).continuousAt.tendsto.comp hv).mul
        ((continuous_apply _).continuousAt.tendsto.comp hu)
    refine tendsto_nhds_unique h₁ (h₂.congr' ?_)
    filter_upwards [hvu] with a ha
    obtain ⟨c, -, hc⟩ := ha
    simp only [hc]
    ring
  refine ⟨fun k => v₀ ⟨k, i k⟩ / u₀ ⟨k, i k⟩, fun k => div_ne_zero ?_ (hi k), ?_⟩
  · intro h0
    obtain ⟨j, hj⟩ := hv₀ k
    have h := hcross k j
    rw [h0, zero_mul] at h
    exact hj ((mul_eq_zero.mp h).resolve_right (hi k))
  · funext p
    obtain ⟨k, j⟩ := p
    show v₀ ⟨k, j⟩ = v₀ ⟨k, i k⟩ / u₀ ⟨k, i k⟩ * u₀ ⟨k, j⟩
    rw [div_mul_eq_mul_div, eq_div_iff (hi k)]
    exact hcross k j


omit [Fintype K] in
theorem ResAboveCover.tendsto_lift {P J : Ideal (MRing ι)} {e : ℕ} (R : AnLogRes P J e) (x : R.X) :
    Tendsto (R.lift x) (𝓝 x) (𝓝 (R.lift x x)) := by
  refine tendsto_pi_nhds.2 fun p => ?_
  obtain ⟨j, hj⟩ := R.A.cover x
  have han := R.holo x p j (R.A.chart j x)
    ⟨(R.A.chart j).map_source hj, by simp [(R.A.chart j).left_inv hj, R.mem_U x]⟩
  have h₁ := han.continuousAt.comp ((R.A.chart j).continuousAt hj)
  have h₂ : ((fun y => R.lift x y p) ∘ (R.A.chart j).symm) ∘ (R.A.chart j) =ᶠ[𝓝 x]
      fun y => R.lift x y p := by
    filter_upwards [(R.A.chart j).eventually_left_inverse hj] with y hy
    simp [hy]
  exact (h₁.congr h₂).tendsto


omit [Fintype K] in
theorem ResAboveCover.limit {P J : Ideal (MRing ι)} {e : ℕ} (R : AnLogRes P J e) {α : Type*}
    {l : Filter α} [l.NeBot] {v : α → (Σ k, ι k) → ℂ} {x : α → R.X} {v₀ : (Σ k, ι k) → ℂ}
    {x₀ : R.X} (hv : Tendsto v l (𝓝 v₀)) (hx : Tendsto x l (𝓝 x₀))
    (hvx : ∀ᶠ a in l, SameOrbit (v a) (R.lift (x a) (x a))) (hv₀ : ∀ k, ∃ i, v₀ ⟨k, i⟩ ≠ 0) :
    SameOrbit v₀ (R.lift x₀ x₀) ∧
      ∀ᶠ a in l, x a ∈ R.U x₀ ∧ SameOrbit (v a) (R.lift x₀ (x a)) := by
  have hU : ∀ᶠ a in l, x a ∈ R.U x₀ := hx ((R.isOpen_U x₀).mem_nhds (R.mem_U x₀))
  have h₂ : ∀ᶠ a in l, x a ∈ R.U x₀ ∧ SameOrbit (v a) (R.lift x₀ (x a)) := by
    filter_upwards [hU, hvx] with a ha hva
    exact ⟨ha, ResAboveCover.sameOrbit_trans hva
      (ResAboveCover.sameOrbit_symm (R.compat x₀ (x a) (x a) ⟨ha, R.mem_U _⟩))⟩
  refine ⟨ResAboveCover.sameOrbit_of_tendsto hv ((ResAboveCover.tendsto_lift R x₀).comp hx)
    (h₂.mono fun a h => h.2) hv₀ (R.mem x₀ x₀ (R.mem_U x₀)).1, h₂⟩


omit [Fintype K] in
theorem ResAboveCover.exists_limit {P J : Ideal (MRing ι)} {e : ℕ} (R : AnLogRes P J e) {α : Type*}
    {l : Filter α} [l.NeBot] {v : α → (Σ k, ι k) → ℂ} {v₀ : (Σ k, ι k) → ℂ}
    (hv : Tendsto v l (𝓝 v₀)) (hv₀ : ∀ k, ∃ i, v₀ ⟨k, i⟩ ≠ 0)
    (hex : ∀ᶠ a in l, ∃ x, SameOrbit (v a) (R.lift x x)) :
    ∃ (F : Ultrafilter α) (x : α → R.X) (x₀ : R.X), (F : Filter α) ≤ l ∧
      Tendsto x F (𝓝 x₀) ∧ SameOrbit v₀ (R.lift x₀ x₀) ∧
      ∀ᶠ a in (F : Filter α), x a ∈ R.U x₀ ∧ SameOrbit (v a) (R.lift x₀ (x a)) := by
  classical
  obtain ⟨-, x₁, -⟩ := hex.exists
  let x : α → R.X := fun a => if h : ∃ x, SameOrbit (v a) (R.lift x x) then h.choose else x₁
  have hvx : ∀ᶠ a in l, SameOrbit (v a) (R.lift (x a) (x a)) :=
    hex.mono fun a h => by simp only [x, dif_pos h]; exact h.choose_spec
  let F := Ultrafilter.of l
  have hFl : (F : Filter α) ≤ l := Ultrafilter.of_le l
  obtain ⟨x₀, -, hx₀⟩ := isCompact_univ.ultrafilter_le_nhds (F.map x) (by simp)
  have hx : Tendsto x F (𝓝 x₀) := by
    rw [Tendsto, ← Ultrafilter.coe_map]
    exact hx₀
  exact ⟨F, x, x₀, hFl, hx, ResAboveCover.limit R (hv.mono_left hFl) hx (hvx.filter_mono hFl) hv₀⟩

theorem ResAboveCover.surj_all (hND : HilbertSamuel.NonvanishingDense.Statement)
    (P J : Ideal (MRing ι)) {e d : ℕ} (R : AnLogRes P J e) (hP : IsArithVar P d) :
    ∀ v ∈ mcPts P, ∃ x, SameOrbit v (R.lift x x) := by
  intro v hv
  obtain ⟨f, hfJ, hfP⟩ := SetLike.not_le_iff_exists.1 R.nondeg
  have hcl := hND K ι P d f hP hfP hv
  have := mem_closure_iff_nhdsWithin_neBot.1 hcl
  have hex : ∀ᶠ w in 𝓝[{w | w ∈ mcPts P ∧ eval w (map (Int.castRingHom ℂ) f) ≠ 0}] v,
      ∃ x, SameOrbit w (R.lift x x) := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    obtain ⟨x, hx⟩ := R.surj w hw.1 (fun hJ => hw.2 (hJ.2 f hfJ))
    exact ⟨x, ResAboveCover.sameOrbit_symm hx⟩
  obtain ⟨-, -, x₀, -, -, h, -⟩ := ResAboveCover.exists_limit R (v := fun w => w)
    (tendsto_id.mono_left nhdsWithin_le_nhds) hv.1 hex
  exact ⟨x₀, h⟩

end GroundTheory.Heights₂.Heights.Targets
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

theorem abs_finsum_mem_le_finsum_mem_abs {α : Type*} (S : Set α) (f : α → ℝ) :
    |∑ᶠ w ∈ S, f w| ≤ ∑ᶠ w ∈ S, |f w| := by
  rw [finsum_mem_def, finsum_mem_def]
  have hind : S.indicator (fun w => |f w|) = fun w => |S.indicator f w| := by
    funext w
    by_cases hw : w ∈ S <;> simp [hw]
  rw [hind]
  have hsupp : Function.support (fun w => |S.indicator f w|) = Function.support (S.indicator f) := by
    ext w
    simp
  by_cases hfin : (Function.support (S.indicator f)).Finite
  · have hfin' : (Function.support (fun w => |S.indicator f w|)).Finite := hsupp ▸ hfin
    rw [finsum_eq_sum _ hfin, finsum_eq_sum _ hfin']
    have hs : hfin'.toFinset = hfin.toFinset := by
      ext w
      simp only [Set.Finite.mem_toFinset, hsupp]
    rw [hs]
    exact Finset.abs_sum_le_sum_abs _ _
  · have hinf' : ¬ (Function.support (fun w => |S.indicator f w|)).Finite := hsupp ▸ hfin
    rw [finsum_of_infinite_support hfin, finsum_of_infinite_support hinf', abs_zero]

theorem PtsIntegrable.of_found (hAbs : Inter.PtsAbsIntegrable.Statement)
    (hMeas : PtsSumMeasurable.Statement) : ReciprocityTheory.ChartRestriction.G.Geo.PtsIntegrableStatement := by
  intro K _ ι _ P e Ψ L A s hP hΨ hL hA hs
  refine (hAbs K ι P e Ψ L A s hP hΨ hL hA hs).mono' (hMeas K ι P e Ψ L A s hP hΨ hL hA hs) ?_
  exact Filter.Eventually.of_forall fun y => by
    rw [Real.norm_eq_abs]
    exact abs_finsum_mem_le_finsum_mem_abs _ _

end GroundTheory.Heights₂.Heights
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open GroundTheory.Heights₂.Heights InvertibleIdealIndexAlt

noncomputable section

namespace InvertibleIndexMultiplicative

variable {Ω : Type} [Field Ω]

theorem index_ne_zero [CharZero Ω] {B : Subring Ω} [Module.Finite ℤ B] {I : Ideal B} (hI : I ≠ ⊥) :
    I.toAddSubgroup.index ≠ 0 := by
  obtain ⟨a, haI, ha⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  obtain ⟨c, hc, q, hq⟩ := OrderIdealIndexExtensionAlt.exists_int_eq_mul ha
  refine OrderIdealIndexExtensionAlt.index_ne_zero_of_zsmul_mem _ hc fun x => ?_
  have e : c • x = a * (q * x) := by rw [zsmul_eq_mul, hq, mul_assoc]
  rw [Submodule.mem_toAddSubgroup, e]
  exact I.mul_mem_right _ haI

theorem relIndex_mulBy_ne_zero [CharZero Ω] {B : Subring Ω} [Module.Finite ℤ B] {β : B} (hβ : β ≠ 0) :
    (B.toAddSubgroup.map (mulBy (β : Ω))).relIndex B.toAddSubgroup ≠ 0 := by
  rw [map_mul_eq, relIndex_map_subtype]
  exact index_ne_zero (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hβ)

theorem relIndex_mulBy_mul {B : Subring Ω} {x y : Ω} (hx : x ≠ 0) (hxB : x ∈ B) (hyB : y ∈ B) :
    (B.toAddSubgroup.map (mulBy (x * y))).relIndex B.toAddSubgroup =
      (B.toAddSubgroup.map (mulBy x)).relIndex B.toAddSubgroup *
        (B.toAddSubgroup.map (mulBy y)).relIndex B.toAddSubgroup := by
  have e : B.toAddSubgroup.map (mulBy (x * y)) = (B.toAddSubgroup.map (mulBy y)).map (mulBy x) := by
    rw [AddSubgroup.map_map]
    congr 1
    ext z
    simp [mul_assoc]
  have h1 : B.toAddSubgroup.map (mulBy y) ≤ B.toAddSubgroup := by
    rintro _ ⟨z, hz, rfl⟩; exact B.mul_mem hyB hz
  have h2 : B.toAddSubgroup.map (mulBy x) ≤ B.toAddSubgroup := by
    rintro _ ⟨z, hz, rfl⟩; exact B.mul_mem hxB hz
  rw [e, ← AddSubgroup.relIndex_mul_relIndex _ _ _ (AddSubgroup.map_mono h1) h2,
    AddSubgroup.relIndex_map_map_of_injective (f := mulBy x) _ _ (mulBy_injective hx), mul_comm]

theorem ne_bot_of_rep {B : Subring Ω} {X : AddSubgroup Ω} {β δ : B} {I : Ideal B} (hβ : β ≠ 0)
    (hX0 : X ≠ ⊥) (hX : ∀ x, x ∈ X ↔ ∃ y ∈ I, (β : Ω) * x = δ * y) : I ≠ ⊥ := by
  intro hI
  obtain ⟨⟨x, hxX⟩, hx0⟩ := AddSubgroup.ne_bot_iff_exists_ne_zero.mp hX0
  obtain ⟨y, hy, hxy⟩ := (hX x).1 hxX
  rw [hI, Ideal.mem_bot] at hy
  subst hy
  have hx : x ≠ 0 := fun h => hx0 (Subtype.ext h)
  have hβL : (β : Ω) ≠ 0 := fun h => hβ (Subtype.ext h)
  simp [hβL, hx] at hxy

theorem genIndex_rep [CharZero Ω] {B : Subring Ω} [Module.Finite ℤ B] {X : AddSubgroup Ω} {β δ : B}
    {I : Ideal B} (hβ : β ≠ 0) (hδ : δ ≠ 0) (hI : I ≠ ⊥)
    (hX : ∀ x, x ∈ X ↔ ∃ y ∈ I, (β : Ω) * x = δ * y) :
    genIndex X B.toAddSubgroup = ((B.toAddSubgroup.map (mulBy (β : Ω))).relIndex B.toAddSubgroup : ℝ) /
      (((B.toAddSubgroup.map (mulBy (δ : Ω))).relIndex B.toAddSubgroup : ℝ) * (I.toAddSubgroup.index : ℝ)) := by
  have hβL : (β : Ω) ≠ 0 := fun h => hβ (Subtype.ext h)
  have hδL : (δ : Ω) ≠ 0 := fun h => hδ (Subtype.ext h)
  have g := genIndex_eq (X := B.toAddSubgroup) (J := I.toAddSubgroup.map B.subtype.toAddMonoidHom)
    (M := X) hβL hδL
    (by rintro _ ⟨y, _, rfl⟩; exact y.2)
    (by rintro _ ⟨y, hy, rfl⟩; exact B.mul_mem β.2 hy)
    (by rintro _ ⟨y, hy, rfl⟩; exact B.mul_mem δ.2 hy)
    (by rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩; exact ⟨β * y, I.mul_mem_left β hy, rfl⟩)
    (by
      intro x
      rw [hX x]
      constructor
      · rintro ⟨y, hy, h⟩
        exact ⟨y, ⟨y, hy, rfl⟩, h⟩
      · rintro ⟨_, ⟨y, hy, rfl⟩, h⟩
        exact ⟨y, hy, h⟩)
    (by rw [relIndex_map_subtype]; exact index_ne_zero hI)
    (relIndex_mulBy_ne_zero hδ)
  rwa [relIndex_map_subtype] at g

end InvertibleIndexMultiplicative


open InvertibleIndexMultiplicative in
theorem InvertibleIndexMul.proof (h1 : LocalGenFamily.Statement) (h2 : LocallyPrincipalCoprimeField.Statement)
    (h3 : InvertibleProductRep.Statement) (h4 : InvertibleIndexCharP.Statement) :
    InvertibleIndexMul.Statement := by
  intro Ω _ B M N P η _ g h hB hM hN hP hg0 hh0 hgc hhc hloc
  have hlocM : ∀ m : Ideal B, m.IsMaximal → ∃ i, LocalGen B M m (g i) :=
    fun m hm => (hloc m hm).imp fun _ hi => hi.1
  have hlocN : ∀ m : Ideal B, m.IsMaximal → ∃ i, LocalGen B N m (h i) :=
    fun m hm => (hloc m hm).imp fun _ hi => hi.2.1
  by_cases hc : ringChar Ω ≠ 0
  · rw [h4 Ω B M η g hc hB hM hg0 hlocM, h4 Ω B N η h hc hB hN hh0 hlocN,
      h4 Ω B P η (fun i => g i * h i) hc hB hP (fun i => mul_ne_zero (hg0 i) (hh0 i))
        (fun m hm => (hloc m hm).imp fun _ hi => hi.2.2)]
    norm_num
  push Not at hc
  have : CharP Ω 0 := ringChar.eq_iff.mp hc
  have : CharZero Ω := CharP.charP_to_charZero Ω
  have := hB
  obtain ⟨hM0, ιM, _, aM, haM, hdM, hlM⟩ := h1 Ω B M η g hB hM hg0 hgc hlocM
  obtain ⟨β, δ, I, hβ, hδ, -, hMI⟩ := h2 Ω B M ιM aM hB hM haM hdM hlM hM0 1 one_ne_zero
  have hI0 := ne_bot_of_rep hβ hM0 hMI
  obtain ⟨t, htI, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI0
  obtain ⟨hN0, ιN, _, aN, haN, hdN, hlN⟩ := h1 Ω B N η h hB hN hh0 hhc hlocN
  obtain ⟨β', δ', J, hβ', hδ', hJt, hNJ⟩ := h2 Ω B N ιN aN hB hN haN hdN hlN hN0 t ht0
  have hJ0 := ne_bot_of_rep hβ' hN0 hNJ
  have hIJ : I ⊔ J = ⊤ := by
    rw [eq_top_iff, ← hJt, sup_comm I J]
    exact sup_le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr htI) _
  have hPr := h3 Ω B M N P η g h β δ β' δ' I J hβ hδ hβ' hδ' hMI hNJ hP hloc
  have hIJ0 : I * J ≠ ⊥ := by
    rw [Ne, Ideal.mul_eq_bot]
    tauto
  have hidx : (I * J).toAddSubgroup.index = I.toAddSubgroup.index * J.toAddSubgroup.index :=
    cardQuot_mul_of_coprime (Ideal.isCoprime_iff_sup_eq.mpr hIJ)
  have hβL : (β : Ω) ≠ 0 := fun e => hβ (Subtype.ext e)
  have hδL : (δ : Ω) ≠ 0 := fun e => hδ (Subtype.ext e)
  rw [genIndex_rep hβ hδ hI0 hMI, genIndex_rep hβ' hδ' hJ0 hNJ,
    genIndex_rep (mul_ne_zero hβ hβ') (mul_ne_zero hδ hδ') hIJ0 hPr, hidx, Subring.coe_mul, Subring.coe_mul,
    relIndex_mulBy_mul hβL β.2 β'.2, relIndex_mulBy_mul hδL δ.2 δ'.2]
  have p1 := Nat.pos_of_ne_zero (relIndex_mulBy_ne_zero hβ)
  have p2 := Nat.pos_of_ne_zero (relIndex_mulBy_ne_zero hδ)
  have p3 := Nat.pos_of_ne_zero (relIndex_mulBy_ne_zero hβ')
  have p4 := Nat.pos_of_ne_zero (relIndex_mulBy_ne_zero hδ')
  have p5 := Nat.pos_of_ne_zero (index_ne_zero hI0)
  have p6 := Nat.pos_of_ne_zero (index_ne_zero hJ0)
  refine ⟨by positivity, by positivity, ?_⟩
  push_cast
  ring

end

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

universe u v w

theorem SegreComponent.proof (h₁ : ChartDimBound.Statement.{u, v, w})
    (h₂ : ChartFiniteIrrel.Statement.{u, v, w}) : SegreComponent.Statement.{u, v, w} := by
  intro K _ ι _ F _ V n f hV hf
  by_contra hne
  have hirr : ∀ W ∈ (V ⊔ Ideal.span {f}).minimalPrimes, ¬ _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant W :=
    fun W hW hrel => hne ⟨W, hW, hrel⟩
  obtain ⟨i, hi⟩ : ∃ i, IsChart V i :=
    ⟨fun k => (hV.1.2.2 k).choose, fun k => (hV.1.2.2 k).choose_spec⟩
  have := h₂ K ι F V f i hV.1.2.1 hf hirr
  have : IsArtinianRing (MRingOver F ι ⧸ chartIdeal V i) :=
    IsArtinianRing.of_finite F (MRingOver F ι ⧸ chartIdeal V i)
  have hA : ringKrullDim (MRingOver F ι ⧸ chartIdeal V i) ≤ ((0 : ℕ) : WithBot ℕ∞) :=
    Ring.krullDimLE_iff.mp inferInstance
  have hdim := h₁ K ι F V i hV.1 hi
  rw [hV.2] at hdim
  have h := hdim.trans (add_le_add hA le_rfl)
  rw [Nat.cast_zero, zero_add] at h
  have h' : n + 1 + Fintype.card K ≤ Fintype.card K := by exact_mod_cast h
  omega

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsGoodProj mcPts segre fibre IsSheet PBlk)

def PtsSheetOnlyNull.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsArithVar P (e + 1) → IsGoodProj P Ψ → IsGoodProj P Ψ' →
      volume {y : Fin e → ℂ | ∃ w ∈ fibre P Ψ y, IsSimpleSheetPt P Ψ w ∧
        ¬ IsSimpleSheetPt P Ψ' ((Ψ' w 0)⁻¹ • w)} = 0

end GroundTheory.Heights₂.Heights
end
end
