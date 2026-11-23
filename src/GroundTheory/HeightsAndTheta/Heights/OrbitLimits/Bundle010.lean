module

public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheetA
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle008
public import Mathlib.FieldTheory.Relrank
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle002
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle008

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsGoodProj mcPts segre fibre IsSheet segre_differentiableAt)

theorem PtsSheetSimpleNull.simple_of_count {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ}
    {P : Ideal (MRing ι)} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {d : ℕ} {y : Fin e → ℂ}
    (hbd : ∀ y', (fibre P Ψ y').encard ≤ d) (hy : (fibre P Ψ y).encard = d)
    (hsh : ∀ w ∈ fibre P Ψ y, ∃ γ, IsSheet P Ψ y w γ) {w : ((k : K) → ι k) → ℂ}
    (hw : w ∈ fibre P Ψ y) : IsSimpleSheetPt P Ψ w := by
  have hF : (fibre P Ψ y).Finite := Set.finite_of_encard_eq_coe hy
  choose! γ hγ using hsh
  obtain ⟨U, hU, hdisj⟩ := hF.t2_separation

  have hev : ∀ᶠ y' in 𝓝 y, ∀ a ∈ fibre P Ψ y,
      (γ a y' ∈ mcPts P ∧ Ψ (segre (γ a y')) = Fin.cons 1 y') ∧ segre (γ a y') ∈ U a := by
    refine (hF.eventually_all).2 fun a ha => ?_
    have hc := (segre_differentiableAt (hγ a ha).2.self_of_nhds.1).continuousAt
    have hmem : U a ∈ 𝓝 (segre (γ a y)) := by
      rw [(hγ a ha).1]
      exact (hU a).2.mem_nhds (hU a).1
    filter_upwards [(hγ a ha).2, hc.preimage_mem_nhds hmem] with y' h1 h2
    exact ⟨⟨h1.2.1, h1.2.2⟩, h2⟩

  have hfib : ∀ y', (∀ a ∈ fibre P Ψ y, (γ a y' ∈ mcPts P ∧ Ψ (segre (γ a y')) = Fin.cons 1 y') ∧
      segre (γ a y') ∈ U a) → fibre P Ψ y' = (fun a => segre (γ a y')) '' fibre P Ψ y := by
    intro y' h
    have hinj : Set.InjOn (fun a => segre (γ a y')) (fibre P Ψ y) := by
      intro a ha b hb hab
      by_contra hne
      exact Set.disjoint_left.mp (hdisj ha hb hne) (h a ha).2 (by simp only at hab; rw [hab]; exact (h b hb).2)
    have hsub : (fun a => segre (γ a y')) '' fibre P Ψ y ⊆ fibre P Ψ y' := by
      rintro _ ⟨a, ha, rfl⟩
      exact ⟨γ a y', (h a ha).1.1, rfl, (h a ha).1.2⟩
    refine ((hF.image _).eq_of_subset_of_encard_le hsub ?_).symm
    rw [hinj.encard_image, hy]
    exact hbd y'
  refine ⟨y, γ w, hγ w hw, ?_⟩
  filter_upwards [hev.prodMk_nhds ((hU w).2.mem_nhds (hU w).1)] with q hq hq2
  rw [hfib q.1 hq.1] at hq2
  obtain ⟨a, ha, hqa⟩ := hq2
  have haw : a = w := by
    by_contra hne
    exact Set.disjoint_left.mp (hdisj ha hw hne) (by rw [← hqa]; exact (hq.1 a ha).2) hq.2
  rw [← hqa, haw]

theorem PtsSheetSimpleNull.proof (hG : PtsGenericCount.Statement) : PtsSheetSimpleNull.Statement := by
  intro K _ ι _ P e Ψ hP hΨ
  obtain ⟨d, hbd, hnull⟩ := hG K ι P e Ψ hP hΨ
  refine measure_mono_null (fun y hy => ?_) hnull
  obtain ⟨w, hw, -, hns⟩ := hy
  exact fun hgood => hns (PtsSheetSimpleNull.simple_of_count hbd hgood.1 hgood.2 hw)

end GroundTheory.Heights₂.Heights
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar PBlk)

def SegreChartDim.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e m : ℕ)
    (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k),
    IsArithVar P (e + 1) → ∀ J ∈ segreChartComponents P σ i,
      ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ J) = (e : ℕ)

end GroundTheory.Heights₂.Heights
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomogIdeal PBlk)
open ComplexSets

def SegreChartZeroSet.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k),
    IsMultiHomogIdeal P → zeroSet (segreChartIdeal P σ i) = segreChartSet P σ i

end GroundTheory.Heights₂.Heights
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open Filter Topology MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomogIdeal mcPts segre IsSheet bsmul eval_bsmul_of_isMultiHomog
  prod_update_eq)

namespace SheetLift

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem bsmul_mem {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) {c : K → ℂ} (hc : ∀ k, c k ≠ 0)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) : bsmul c z ∈ mcPts P := by
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 k
    exact ⟨i, mul_ne_zero (hc k) hi⟩
  · obtain ⟨S, hS, hPS⟩ := hP
    have hle : P ≤ RingHom.ker ((eval (bsmul c z)).comp (map (Int.castRingHom ℂ))) := by
      rw [hPS, Ideal.span_le]
      intro g hg
      obtain ⟨a, ha⟩ := hS g hg
      rw [SetLike.mem_coe, RingHom.mem_ker, RingHom.comp_apply, eval_bsmul_of_isMultiHomog ha c z,
        hz.2 g (by rw [hPS]; exact Ideal.subset_span hg), mul_zero]
    exact hle hf


omit [∀ k, Fintype (ι k)] in
theorem segre_bsmul (c : K → ℂ) (z : (Σ k, ι k) → ℂ) :
    segre (bsmul c z) = fun i => (∏ k, c k) * segre z i := by
  funext i
  simp only [segre, bsmul, Finset.prod_mul_distrib]

def lift [DecidableEq K] (i0 : (k : K) → ι k) (k0 : K) (w : ((k : K) → ι k) → ℂ) : (Σ k, ι k) → ℂ :=
  fun p => (if p.1 = k0 then w i0 else 1) * (w (Function.update i0 p.1 p.2) / w i0)

theorem lift_segre [DecidableEq K] (i0 : (k : K) → ι k) (k0 : K) {z : (Σ k, ι k) → ℂ}
    (hz : segre z i0 ≠ 0) :
    lift i0 k0 (segre z) = bsmul (fun k => (if k = k0 then segre z i0 else 1) / z ⟨k, i0 k⟩) z := by
  have h0 : ∀ k, z ⟨k, i0 k⟩ ≠ 0 := fun k => (Finset.prod_ne_zero_iff.mp hz) k (Finset.mem_univ k)
  funext ⟨k, j⟩
  have e1 : segre z (Function.update i0 k j) = z ⟨k, j⟩ * ∏ k' ∈ Finset.univ.erase k, z ⟨k', i0 k'⟩ :=
    prod_update_eq z i0 k j
  have e2 : segre z i0 = z ⟨k, i0 k⟩ * ∏ k' ∈ Finset.univ.erase k, z ⟨k', i0 k'⟩ := by
    have := prod_update_eq z i0 k (i0 k)
    rwa [Function.update_eq_self] at this
  have hQ : ∏ k' ∈ Finset.univ.erase k, z ⟨k', i0 k'⟩ ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k' _ => h0 k'
  have hk := h0 k
  simp only [lift, bsmul]
  rw [e1, e2]
  field_simp

theorem lift_spec [DecidableEq K] {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) (i0 : (k : K) → ι k)
    (k0 : K) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) (hne : segre z i0 ≠ 0) :
    lift i0 k0 (segre z) ∈ mcPts P ∧ segre (lift i0 k0 (segre z)) = segre z := by
  have h0 : ∀ k, z ⟨k, i0 k⟩ ≠ 0 := fun k => (Finset.prod_ne_zero_iff.mp hne) k (Finset.mem_univ k)
  rw [lift_segre i0 k0 hne]
  refine ⟨bsmul_mem hP (fun k => div_ne_zero (by split_ifs <;> simp [hne]) (h0 k)) hz, ?_⟩
  have hprod : ∏ k, (if k = k0 then segre z i0 else 1) / z ⟨k, i0 k⟩ = 1 := by
    rw [Finset.prod_div_distrib, Finset.prod_ite_eq' Finset.univ k0, if_pos (Finset.mem_univ _)]
    exact div_self hne
  rw [segre_bsmul, hprod]
  funext i
  rw [one_mul]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem differentiableAt_lift [DecidableEq K] {e : ℕ} (i0 : (k : K) → ι k) (k0 : K)
    {h : (Fin e → ℂ) → ((k : K) → ι k) → ℂ} {y : Fin e → ℂ} (hd : DifferentiableAt ℂ h y)
    (hne : h y i0 ≠ 0) : DifferentiableAt ℂ (fun y' => lift i0 k0 (h y')) y := by
  have hc : ∀ i, DifferentiableAt ℂ (fun y' => h y' i) y := fun i => differentiableAt_pi.mp hd i
  refine differentiableAt_pi.mpr fun p => ?_
  simp only [lift, div_eq_mul_inv]
  refine DifferentiableAt.mul ?_ ((hc (Function.update i0 p.1 p.2)).mul ((hc i0).inv hne))
  by_cases hp : p.1 = k0
  · simp only [hp, if_true]
    exact hc i0
  · simp only [hp, if_false]
    exact differentiableAt_const _

theorem proof : SheetLift.Statement := by
  intro K _ ι _ P e Ψ y h hP hev
  classical
  obtain ⟨hd0, ⟨z0, hz0, hs0⟩, -⟩ := hev.self_of_nhds
  rcases isEmpty_or_nonempty K with hK | ⟨⟨k0⟩⟩
  · refine ⟨fun _ => z0, hs0, hev.mono fun y' ⟨_, ⟨z, hz, hs⟩, hΨ⟩ => ?_⟩
    have hzz : z0 = z := funext fun p => (IsEmpty.false p.1).elim
    refine ⟨differentiableAt_const _, hzz ▸ hz, ?_⟩
    show Ψ (segre z0) = _
    rw [hzz, hs]
    exact hΨ
  · choose i0 hi0 using hz0.1
    have hy : h y i0 ≠ 0 := by
      rw [← hs0]
      exact Finset.prod_ne_zero_iff.mpr fun k _ => hi0 k
    have hnear : ∀ᶠ y' in 𝓝 y, h y' i0 ≠ 0 :=
      (differentiableAt_pi.mp hd0 i0).continuousAt.eventually_ne hy
    refine ⟨fun y' => lift i0 k0 (h y'), ?_, (hev.and hnear).mono fun y' ⟨⟨hd, ⟨z, hz, hs⟩, hΨ⟩, hne⟩ => ?_⟩
    · show segre (lift i0 k0 (h y)) = h y
      rw [← hs0]
      exact (lift_spec hP i0 k0 hz0 (hs0 ▸ hy)).2
    · have hne' : segre z i0 ≠ 0 := hs ▸ hne
      obtain ⟨h1, h2⟩ := lift_spec hP i0 k0 hz hne'
      refine ⟨differentiableAt_lift i0 k0 hd hne, ?_, ?_⟩
      · show lift i0 k0 (h y') ∈ mcPts P
        rw [← hs]
        exact h1
      · show Ψ (segre (lift i0 k0 (h y'))) = _
        rw [← hs, h2, hs]
        exact hΨ

end SheetLift

end GroundTheory.Heights₂.Heights
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def LelongChartLimit.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → HermLine ι) (A : HermLine ι) (s : MRing ι) (g : ((Σ k, ι k) → ℂ) → ℝ)
    (i : (k : K) → ι k) (δ : ℝ),
    IsArithVar P (n + 2) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSectionOn P A s →
    IsDegZeroSmooth g → 0 < δ → (∀ z, ‖segre z i‖ < δ * ‖segre z‖ → g z = 0) →
    Tendsto (fun ε : ℝ =>
        ptsIntegral P
          (Fin.cons (fun z => Real.log (‖eval z (map (Int.castRingHom ℂ) s)‖ ^ 2 + ε * A.h z ^ 2) / 2)
            (pot L)) g)
      (𝓝[>] 0)
      (𝓝 (∑ᶠ (W) (_ : W ∈ divSupp P s ∧ IsHorizontal W),
          (multAt (P ⊔ Ideal.span {s}) W : ℝ) * ptsIntegral W (pot L) g))

end GroundTheory.Heights₂.Heights.Targets
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (segre PBlk)

def SegrePartition.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)],
    (∀ k, Nonempty (ι k)) →
      ∃ δ : ℝ, 0 < δ ∧ ∃ ρ : ((k : K) → ι k) → ((Σ k, ι k) → ℂ) → ℝ,
        (∀ i, IsDegZeroSmooth (ρ i)) ∧ (∀ z, ∑ i, ρ i z = 1) ∧
          ∀ i z, ‖segre z i‖ < δ * ‖segre z‖ → ρ i z = 0

end GroundTheory.Heights₂.Heights
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def GenFibreChartDeg.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (G : GenFibre v P')
    [CharZero G.Φ'] (c : ∀ k, ι k) (i : ∀ k : FibreBlock κ, fibreIdx ι' κ k),
    IsBlockMap κ v → IsMultiHomogIdeal P' → (∀ k, G.x ⟨k, c k⟩ ≠ 0) → (∀ k, G.x' ⟨k.1, i k⟩ ≠ 0) →
    Module.finrank G.Φ (IntermediateField.adjoin G.Φ (Set.range fun q : Σ k : FibreBlock κ, fibreIdx ι' κ k =>
        G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, i q.1⟩)) =
      IntermediateField.relfinrank (blockFnField (G.x' ∘ v)) (blockFnField G.x')

end GroundTheory.Heights₂.Heights.Targets
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def CoordFibreDeg.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k', ι' k') → Ω) (d : ℕ) (G : GenFibre v (mCoordIdeal y))
    (i : ∀ k : FibreBlock κ, fibreIdx ι' κ k),
    IsBlockMap κ v → IsArithVar (mCoordIdeal y) d → IsArithVar (imageZ v (mCoordIdeal y)) d →
    IsChart (_root_.ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G) i →
    ptDeg (_root_.ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G) i = IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y)

end GroundTheory.Heights₂.Heights.Targets
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def CoordRatioDeg.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k', ι' k') → Ω) (Φ' : Type) [Field Φ'] [CharZero Φ'] (x' : (Σ k', ι' k') → Φ'),
    IsBlockMap κ v → RingHom.ker (aeval x' : MRing ι' →ₐ[ℤ] Φ') = mCoordIdeal y →
    IntermediateField.relfinrank (blockFnField (x' ∘ v)) (blockFnField x') =
      IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y)

end GroundTheory.Heights₂.Heights.Targets
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

def MoriwakiBigCurve.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (P0 : Ideal (MRing ι)) (II : IntersectionSystem),
    IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (0 + 1) → Birational y →
    P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) A → IsConjInvariantH A →
    NefOnFibres (mCoordIdeal y) A.a → NefOnGeneric (mCoordIdeal y) A →
    II K ι (mCoordIdeal y) (0 + 1) (fun _ => A) ≤
      arVolP (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) 1 0

namespace MoriwakiBigCurve

end MoriwakiBigCurve

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def FibreMultiHomog.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (G : GenFibre v P'),
    IsBlockMap κ v → IsMultiHomogIdeal P' → IsMultiHomogIdeal (_root_.ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G)

end GroundTheory.Heights₂.Heights.Targets
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.AI.I1

universe u v w v' w'

def SymmRelabel.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type v) [Fintype K] (ι : K → Type w) [∀ k, Fintype (ι k)]
    (K' : Type v') [Fintype K'] (ι' : K' → Type w') [∀ k, Fintype (ι' k)] (e : K ≃ K'),
    (∀ k, ι k ≃ ι' (e k)) → SymmStatement F ι' → SymmStatement F ι

end GroundTheory.Heights₂.Heights.Targets
end
