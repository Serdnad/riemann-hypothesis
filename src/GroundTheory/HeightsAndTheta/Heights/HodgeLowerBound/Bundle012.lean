module

public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices.InstFintypeFlIdx
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Weights
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHodgeFlag
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeight
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle010
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Sheaves.Init
public import GroundTheory.HeightsAndTheta.Heights.Bundle002

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable section

def FlagGrassPush.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N j : ℕ) (cf : ℚ),
    IsIntersectionSystem II → 2 ≤ N → 1 ≤ j → j ≤ N - 1 →
    -hFl Ψ N II (FA Ψ N j cf) *
        geomDeg (grassIdeal (Fintype.card Ψ) j (N - j))
          (GroundTheory.Heights₂.Heights.fsMulti (plBlocks (Fintype.card Ψ) j (N - j))) (dimN Ψ N j) =
      (Jint Ψ N j cf : ℝ) *
        II (Fin (Fintype.card Ψ)) (plBlocks (Fintype.card Ψ) j (N - j)) (grassIdeal (Fintype.card Ψ) j (N - j))
          (dimN Ψ N j + 1) (fun _ => GroundTheory.Heights₂.Heights.fsMulti (plBlocks (Fintype.card Ψ) j (N - j)))

end

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {e : ℕ}

def modelU (M : CxModel P e) (x : M.Xc) : Set M.Xc :=
  (M.sections x).choose

def modelLift (M : CxModel P e) (x : M.Xc) : M.Xc → (Σ k, ι k) → ℂ :=
  (M.sections x).choose_spec.2.2.choose

theorem modelU_isOpen (M : CxModel P e) (x : M.Xc) : IsOpen (modelU M x) :=
  (M.sections x).choose_spec.1

theorem mem_modelU (M : CxModel P e) (x : M.Xc) : x ∈ modelU M x :=
  (M.sections x).choose_spec.2.1

theorem modelLift_spec (M : CxModel P e) (x : M.Xc) :
    (∀ y ∈ modelU M x, modelLift M x y ∈ mcPts P ∧ M.proj (modelLift M x y) = y) ∧
      ∀ p, M.atlas.HoloOn (modelU M x) fun y => modelLift M x y p :=
  (M.sections x).choose_spec.2.2.choose_spec

def modelPot (M : CxModel P e) (L : _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (c : ℝ) : LocPot M.Xc where
  U := modelU M
  isOpen_U := modelU_isOpen M
  mem_U := mem_modelU M
  φ x y := c * Real.log (L.h (modelLift M x y))

def modelQ (M : CxModel P e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (x : M.Xc) : Fin e → ℂ :=
  fun i => Ψ (segre (modelLift M x x)) i.succ / Ψ (segre (modelLift M x x)) 0

def modelCrit (M : CxModel P e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) : Set M.Xc :=
  {x | Ψ (segre (modelLift M x x)) 0 = 0 ∨ ∃ j, x ∈ (M.atlas.chart j).source ∧
    ¬ (AnalyticAt ℂ (modelQ M Ψ ∘ (M.atlas.chart j).symm) (M.atlas.chart j x) ∧
      LinearMap.det (fderiv ℂ (modelQ M Ψ ∘ (M.atlas.chart j).symm) (M.atlas.chart j x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)}

def modelBad (M : CxModel P e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (E : Set M.Xc) : Set M.Xc :=
  E ∪ modelCrit M Ψ

theorem modelQ_good_of_notMem (M : CxModel P e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (E : Set M.Xc) : ∀ x ∉ modelBad M Ψ E, ∀ j, x ∈ (M.atlas.chart j).source →
      AnalyticAt ℂ (modelQ M Ψ ∘ (M.atlas.chart j).symm) (M.atlas.chart j x) ∧
        LinearMap.det (fderiv ℂ (modelQ M Ψ ∘ (M.atlas.chart j).symm) (M.atlas.chart j x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0 := by
  intro x hx j hj
  by_contra h
  exact hx (Or.inr (Or.inr ⟨j, hj, h⟩))

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def ProjHoloLocal.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (M : XModel D)
    (e : OpenPartialHomeomorph M.Xc (Fin D.n → ℂ)), ReciprocityTheory.AnForm.M.IsCompatChart M.atlas e →
    ∀ z ∈ mcPts (mCoordIdeal D.y), M.proj z ∈ e.source →
      ∃ W : Set ((Σ k, ι k) → ℂ), IsOpen W ∧ z ∈ W ∧ ∃ F : ((Σ k, ι k) → ℂ) → Fin D.n → ℂ,
        DifferentiableOn ℂ F W ∧
          ∀ z' ∈ W ∩ mcPts (mCoordIdeal D.y), M.proj z' ∈ e.source ∧ e (M.proj z') = F z'

namespace Line

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def RefAlongSheet.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (M : CxModel P n) (Xo : Set ((Σ k, ι k) → ℂ)) (A : _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (S : LogLogRegularisationSetting M Xo A)
    (γ : (Fin n → ℂ) → (Σ k, ι k) → ℂ) (y : Fin n → ℂ) (j : Fin S.R.N),
    (∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ γ y' ∧ γ y' ∈ mcPts P) →
    M.proj (γ y) ∈ (S.R.chart j).source →
    (∀ᶠ y' in 𝓝 y, M.proj (γ y') ∈ (S.R.chart j).source ∧
      DifferentiableAt ℂ (fun y'' => S.R.chart j (M.proj (γ y''))) y') →
    ∃ G : (Fin n → ℂ) → ℂ, AnalyticAt ℂ G y ∧ ∀ᶠ y' in 𝓝 y,
      Real.log (S.ref.h (γ y')) = S.R.q j (S.R.chart j (M.proj (γ y'))) + (G y').re

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open GroundTheory.Heights₂.Heights.Regular (RegChartData)

def SheetChartHolo.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (M : CxModel P n) (R : RegChartData M.atlas) (Q : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)),
    ∀ᵐ y : Fin n → ℂ, ∀ (w : ((k : K) → ι k) → ℂ) (γ : (Fin n → ℂ) → (Σ k, ι k) → ℂ),
      IsSheet P Q y w γ → ∃ j : Fin R.N, M.proj (γ y) ∈ (R.chart j).source ∧ M.proj (γ y) ∈ R.Yo ∧
        ∀ᶠ y' in 𝓝 y, M.proj (γ y') ∈ (R.chart j).source ∧
          DifferentiableAt ℂ (fun y'' => R.chart j (M.proj (γ y''))) y'

namespace Line

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def VertFactorPos.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (p : ℕ),
    p ∈ D.S → ∀ z ∈ mcPts (mCoordIdeal D.y), 0 < D.vertFactor p z

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

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {d : ℕ}

def IsChartVel (M : CxModel P d) (e : OpenPartialHomeomorph M.Xc (Fin d → ℂ)) (z w : (Σ k, ι k) → ℂ)
    (v : Fin d → ℂ) : Prop :=
  ∃ γ : ℂ → (Σ k, ι k) → ℂ, γ 0 = z ∧ HasDerivAt γ w 0 ∧
    (∀ᶠ s in 𝓝 (0 : ℂ), DifferentiableAt ℂ γ s ∧ γ s ∈ mcPts P) ∧
    HasDerivAt (fun s => e (M.proj (γ s))) v 0

namespace Line

open GroundTheory.Heights₂.Heights (CP)

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open ReciprocityTheory.AnForm.M (IsCompatChart)

def ModelPtsIntegrable.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (M : CxModel P e) (n : ℕ) (ψ : Fin n → OpenPartialHomeomorph M.Xc (Fin e → ℂ)) (L : _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (c : ℝ)
    (N : Set ((Σ k, ι k) → ℂ)) (E : Set M.Xc) (v : M.Xc → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ),
    IsArithVar P (e + 1) → IsSmoothHerm L → IsPtsNull P e N →
    (∀ j, IsCompatChart M.atlas (ψ j)) → (∀ x, ∃ j, x ∈ (ψ j).source) →
    (∀ j, volume ((ψ j).target ∩ (ψ j).symm ⁻¹' E) = 0) →
    (∀ j, ∀ Q ⊆ (ψ j).target, IsCompact Q → IntegrableOn (fun y => v ((ψ j).symm y)) Q) →
    (∀ z ∈ mcPts P, z ∉ N → M.proj z ∉ E → g z = v (M.proj z)) →
      IsPtsIntegrable P (fun (_ : Fin e) z => c * Real.log (L.h z)) g

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

def HodgeFlagNeZero.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (Pl : PlueckerData D) (H : HodgeData D)
    (B : AdaptedBasis H) (τ : Ψ) (i : Fin (D.N - 1)), ∃ m, Pl.pluecker0 B τ i m ≠ 0

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def HodgeFlagRatioTrdeg.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (Pl : PlueckerData D) (H : HodgeData D)
    (B : AdaptedBasis H) (c : ∀ k, Pl.ιY k), (∀ k, Pl.flagGenericPoint B ⟨k, c k⟩ ≠ 0) →
    Algebra.trdeg ℤ (Subfield.closure (coneRatios (Pl.flagGenericPoint B) c)) = ((D.n + D.flagDim0 : ℕ) : Cardinal)

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def PushDown.Statement : Prop :=
  ∀ (II : IntersectionSystem), IsFullIntersectionSystem II →
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
    (D : ComponentData II Ψ K ι Ω E) (Pl : PlueckerData D) (H : HodgeData D) (B : AdaptedBasis H),
    (∀ (G : GenFibre Pl.xV (Pl.flagPrime B))
        (J : IFamily G.Φ (fibreIdx Pl.ιY (Sum.inl : K → K ⊕ (Ψ × Fin (D.N - 1)))))
        (L : Fin (D.n + 1) → _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (L' : Fin (D.n + 1) → _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine Pl.ιY)
        (N : Fin D.flagDim0 → _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine Pl.ιY),
        IsFieldIntersection J → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm Sum.inl Pl.xV (L j) (L' j)) →
        (∀ j, IsSmoothHerm (N j)) →
        II _ Pl.ιY (Pl.flagPrime B) (D.n + 1 + D.flagDim0) (Fin.append L' N) =
          (J (fibreIdeal Sum.inl G) D.flagDim0 (fun j => fibreDeg Sum.inl (N j).a) : ℝ) *
            II K ι (mCoordIdeal D.y) (D.n + 1) L) ∧
    (∀ (d r : ℕ) (L : Fin d → _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (L' : Fin d → _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine Pl.ιY) (N : Fin r → _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine Pl.ιY),
        d + r = D.n + 1 + D.flagDim0 → D.n + 1 < d → (∀ j, IsSmoothHerm (L j)) →
        (∀ j, IsPullHerm Sum.inl Pl.xV (L j) (L' j)) → (∀ j, IsSmoothHerm (N j)) →
        II _ Pl.ιY (Pl.flagPrime B) (d + r) (Fin.append L' N) = 0)

section Bot

variable {K : Type} {ι : K → Type} {K' : Type} {ι' : K' → Type}

end Bot

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end
