module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeight
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Bundle003
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
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle006

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights Matrix

noncomputable section

def UnitDetBound (m j : ℕ) (e : ℝ) : Prop :=
  ∀ Z : Matrix (Fin m) (Fin j) ℂ, (∀ a b, ‖Z a b‖ = 1) → 1 / 2 * Real.log (1 + Z * Zᴴ).det.re ≤ e

def RootLogNormBoundE.Statement : Prop :=
  ∀ (f j m : ℕ) (e : ℝ) (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ), UnitDetBound m j e → IsRootMatrix ζ →
    ∀ z ∈ mcPts (rootPointIdeal ζ),
      -((f : ℝ) * e) ≤ logNorm (fsMulti (plBlocks f j m)) (rootAnchorSection f j m) z

def RootHeightE.Statement : Prop :=
  ∀ (f j m : ℕ) (e : ℝ) (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ), 1 ≤ f → UnitDetBound m j e → IsRootMatrix ζ →
    ∀ II : IntersectionSystem, IsIntersectionSystem II →
      II (Fin f) (plBlocks f j m) (rootPointIdeal ζ) 1 ![fsMulti (plBlocks f j m)] ≤
        (f : ℝ) * e * degC (rootPointIdeal ζ)

def GrassHeightE.Statement : Prop :=
  SuccessiveMinimaUpperBound → ∀ (f j m : ℕ) (e : ℝ), 1 ≤ f → UnitDetBound m j e →
    ∀ II : IntersectionSystem, IsIntersectionSystem II →
      II (Fin f) (plBlocks f j m) (grassIdeal f j m) (f * j * m + 1) (fun _ => fsMulti (plBlocks f j m)) ≤
        ((f * j * m + 1 : ℕ) : ℝ) * ((f : ℝ) * e) *
          geomDeg (grassIdeal f j m) (fsMulti (plBlocks f j m)) (f * j * m)

end

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

def BirationalRatioClosure.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω)
    (c : ∀ k, ι k), Birational y → (∀ k, y ⟨k, c k⟩ ≠ 0) → Subfield.closure (coneRatios y c) = ⊤

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

namespace RatioFieldSpan

variable {F M : Type} [Field F] [Field M] [Algebra F M]

theorem div_mem_adjoin {I : Type} (u : I → M) (v : M) {x : M}
    (hx : x ∈ Submodule.span F (Set.range u)) :
    x / v ∈ IntermediateField.adjoin F (Set.range fun i => u i / v) := by
  induction hx using Submodule.span_induction with
  | mem x h =>
    obtain ⟨i, rfl⟩ := h
    exact IntermediateField.subset_adjoin F _ ⟨i, rfl⟩
  | zero => simp
  | add x y _ _ hx hy =>
    rw [add_div]
    exact add_mem hx hy
  | smul a x _ hx =>
    rw [Algebra.smul_def, mul_div_assoc]
    exact mul_mem (IntermediateField.algebraMap_mem _ a) hx

theorem adjoin_le {I J : Type} (u : I → M) (w : J → M) (v v' : M)
    (hw : ∀ j, w j ∈ Submodule.span F (Set.range u)) (hv' : v' ∈ Submodule.span F (Set.range u))
    (hv : v ≠ 0) (hv'0 : v' ≠ 0) :
    IntermediateField.adjoin F (Set.range fun j => w j / v') ≤
      IntermediateField.adjoin F (Set.range fun i => u i / v) := by
  rw [IntermediateField.adjoin_le_iff]
  rintro _ ⟨j, rfl⟩
  have h1 := div_mem_adjoin (F := F) u v (hw j)
  have h2 := div_mem_adjoin (F := F) u v hv'
  have key : w j / v' = (w j / v) / (v' / v) := by
    field_simp
  show w j / v' ∈ IntermediateField.adjoin F (Set.range fun i => u i / v)
  rw [key]
  exact div_mem h1 h2

theorem full : RatioFieldSpan.Statement := by
  intro F M _ _ _ I J u w v v' hspan hv hv' hv0 hv'0
  apply le_antisymm
  · apply adjoin_le w u v' v
    · intro i
      rw [← hspan]
      exact Submodule.subset_span ⟨i, rfl⟩
    · rw [← hspan]; exact hv
    · exact hv'0
    · exact hv0
  · apply adjoin_le u w v v'
    · intro j
      rw [hspan]
      exact Submodule.subset_span ⟨j, rfl⟩
    · exact hv'
    · exact hv0
    · exact hv'0

end RatioFieldSpan

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

section Subbundle

variable {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {N : ℕ}

def IsSubbundle (y : (Σ k, ι k) → Ω) (W : ChartBundle ℤ (segreCoord y) N E) (F : Submodule Ω E)
    (r : ℕ) : Prop :=
  ∀ c : (k : K) → ι k, segreCoord y c ≠ 0 →
    ∃ (m : ℕ) (f a : Fin m → Ω), (∀ l, f l ∈ chartRing ℤ (segreCoord y) c) ∧
      (∀ l, a l ∈ chartRing ℤ (segreCoord y) c) ∧ ∑ l, a l * f l = 1 ∧
      ∀ l, f l ≠ 0 → ∃ b : Fin N → E, IsFrameOver y W c (f l) b ∧
        Submodule.span Ω (b '' {i | (i : ℕ) < r}) = F

end Subbundle

structure ComponentDataHodge (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (K : Type) [Fintype K]
    (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type)
    [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)] extends ComponentData II Ψ K ι Ω E where

  F : ∀ τ, Submodule Ω (E τ)
  hodge : ∀ τ, IsSubbundle y (W τ) (F τ) j

namespace Line

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def SmoothAlong {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (S : Set V) (f : V → ℝ) : Prop :=
  ∀ z ∈ S, ∃ U ∈ 𝓝 z, ∃ G : V → ℝ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G U ∧ ∀ w ∈ U ∩ S, f w = G w

def HermExtend.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (a : K → ℤ)
    (F : ((Σ k, ι k) → ℂ) → ℝ), IsMultiHomogIdeal P → (∀ z ∈ mcPts P, 0 < F z) →
    (∀ z ∈ mcPts P, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → F (torusSmul c z) = (∏ k, ‖c k‖ ^ a k) * F z) →
    SmoothAlong (mcPts P) F →
    ∃ Z : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι, Z.a = a ∧ IsSmoothHerm Z ∧ ∀ z ∈ mcPts P, Z.h z = F z

namespace Line

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def LocalOrbitChart.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    (y : (Σ k, ι k) → Ω) (n : ℕ), IsArithVar (mCoordIdeal y) (n + 1) → SmoothGenericFibreM y →
    ∀ z₀ ∈ mcPts (mCoordIdeal y), ∃ N : Set ((Σ k, ι k) → ℂ), IsOpen N ∧ z₀ ∈ N ∧
      ∃ κ : ((Σ k, ι k) → ℂ) → (Fin n → ℂ), AnalyticOnNhd ℂ κ N ∧
        (∀ z ∈ N, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → torusSmul c z ∈ N ∧ κ (torusSmul c z) = κ z) ∧
        ∀ z ∈ N ∩ mcPts (mCoordIdeal y), ∀ z' ∈ N ∩ mcPts (mCoordIdeal y), κ z = κ z' →
          ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ z' = torusSmul c z

namespace Line

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def IsPtsNull (P : Ideal (MRing ι)) (e : ℕ) (N : Set ((Σ k, ι k) → ℂ)) : Prop :=
  ∀ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P Ψ →
    volume {y : Fin e → ℂ | ∃ z ∈ mcPts P, z ∈ N ∧ Ψ (segre z) = Fin.cons 1 y} = 0

def IsPtsIntegrable (P : Ideal (MRing ι)) {e : ℕ} (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    (g : ((Σ k, ι k) → ℂ) → ℝ) : Prop :=
  ∀ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P Ψ →
    Integrable (fun y => ∑ᶠ w ∈ fibre P Ψ y, sheetDensity P Ψ φ g y w)

def PtsBddConv.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (L : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (r : ℝ) (g : ℝ → ((Σ k, ι k) → ℂ) → ℝ) (g₀ : ((Σ k, ι k) → ℂ) → ℝ)
    (N : Set ((Σ k, ι k) → ℂ)) (C s₀ : ℝ),
    IsArithVar P (e + 1) → IsSmoothHerm L → 0 < r → IsPtsNull P e N → 0 < s₀ →
    (∀ s : ℝ, 0 < s → s < s₀ → (∀ z ∈ mcPts P, |g s z| ≤ C) ∧ ContinuousOn (g s) (mcPts P \ N) ∧
      ∀ c : K → ℂ, (∀ k, c k ≠ 0) → ∀ z ∈ mcPts P, g s (torusSmul c z) = g s z) →
    (∀ z ∈ mcPts P, z ∉ N → Tendsto (fun s => g s z) (𝓝[>] 0) (𝓝 (g₀ z))) →
    IsPtsIntegrable P (fun (_ : Fin e) z => Real.log (L.h z) / r) g₀ ∧
      Tendsto (fun s => ptsIntegral P (fun (_ : Fin e) z => Real.log (L.h z) / r) (g s)) (𝓝[>] 0)
        (𝓝 (ptsIntegral P (fun (_ : Fin e) z => Real.log (L.h z) / r) g₀))

namespace Line

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree.ComponentDataEquivalence

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

section Boundary

theorem mcPts_torus {B : Ideal (MRing ι)} (hB : IsMultiHomogIdeal B) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts B)
    {c : K → ℂ} (hc : ∀ k, c k ≠ 0) : torusSmul c z ∈ mcPts B := by
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 k
    exact ⟨i, mul_ne_zero (hc k) hi⟩
  obtain ⟨S, hS, rfl⟩ := hB
  induction hf using Submodule.span_induction with
  | mem s hs =>
    obtain ⟨a, ha⟩ := hS s hs
    rw [eval_map]
    unfold torusSmul
    rw [IndefiniteRowSideFullHecke.HeightsSet.CurveComplexPoint.eval₂_smul_homog s a ha, ← eval_map, hz.2 s (Ideal.subset_span hs),
      mul_zero]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), eval_add, hx, hy, add_zero]
  | smul r x _ hx => rw [smul_eq_mul, map_mul, eval_mul, hx, mul_zero]

end Boundary

section Ample

end Ample

end GroundTheory.Heights₂.Heights.LowerBoundFree.ComponentDataEquivalence
end
end
