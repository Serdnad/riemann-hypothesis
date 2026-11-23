module

public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSaturatedFirstCoordinateLine
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle005
public import ReciprocityTheory.AnalyticForms.MaIntEmpty
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle006
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle006

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open ReciprocityTheory.ChartRestriction.G.Geo

def ZhangLowerX.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P P0 : Ideal (MRing ι)) (n : ℕ)
    (A : _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (e : ℝ) (II : IntersectionSystem),
    IsIntersectionSystem II → IsArithVar P (n + 1) → P0 ≤ P → IsSemipositiveRel P0 P A →
    NefOnFibres P A.a → IsConjInvariantH A →
    (∀ W, IsArithVar W 1 → P ≤ W → e ≤ IndefiniteRowSideFullHecke.HeightsSet.height (II K ι) A W) →
    ((n + 1 : ℕ) : ℝ) * e * geomDeg P A n ≤ II K ι P (n + 1) (fun _ => A)

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

namespace BirationalRatioClosure

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem aeval_eq_prod_mul (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    {g : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d) :
    aeval y g = (∏ k, y ⟨k, c k⟩ ^ d k) * aeval (fun p ↦ y p / y ⟨p.1, c p.1⟩) g := by
  classical
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  rw [mul_left_comm]
  congr 1
  have h1 : (∏ p, y p ^ m p) =
      ∏ p : Σ k, ι k, (y ⟨p.1, c p.1⟩ ^ m p * (y p / y ⟨p.1, c p.1⟩) ^ m p) := by
    refine Finset.prod_congr rfl fun p _ ↦ ?_
    rw [← mul_pow, mul_div_cancel₀ _ (hc p.1)]
  rw [h1, Finset.prod_mul_distrib]
  congr 1
  rw [Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  show ∏ i, y ⟨k, c k⟩ ^ m ⟨k, i⟩ = y ⟨k, c k⟩ ^ d k
  rw [Finset.prod_pow_eq_pow_sum, hg m hm k]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem aeval_mem_closure (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (g : MRing ι) :
    aeval (fun p ↦ y p / y ⟨p.1, c p.1⟩) g ∈ Subfield.closure (coneRatios y c) := by
  induction g using MvPolynomial.induction_on with
  | C a =>
    rw [aeval_C, algebraMap_int_eq, eq_intCast]
    exact intCast_mem _ a
  | add p q hp hq =>
    rw [map_add (f := _)]
    exact add_mem hp hq
  | mul_X p i hp =>
    rw [map_mul, aeval_X]
    exact mul_mem hp (Subfield.subset_closure ⟨i, rfl⟩)

theorem full : BirationalRatioClosure.Statement := by
  intro K _ ι _ Ω _ y c hy hc
  refine eq_top_iff.2 fun s _ ↦ ?_
  obtain ⟨d, g, h, hg, hh, hh0, hgs⟩ := hy s
  have hP : (∏ k, y ⟨k, c k⟩ ^ d k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ ↦ pow_ne_zero _ (hc k)
  rw [aeval_eq_prod_mul y c hc hg, aeval_eq_prod_mul y c hc hh] at hgs
  rw [aeval_eq_prod_mul y c hc hh] at hh0
  have hr := right_ne_zero_of_mul hh0
  have hs : s = aeval (fun p ↦ y p / y ⟨p.1, c p.1⟩) g / aeval (fun p ↦ y p / y ⟨p.1, c p.1⟩) h := by
    rw [eq_div_iff hr]
    exact (mul_left_cancel₀ hP (hgs.trans (mul_left_comm _ _ _))).symm
  rw [hs]
  exact div_mem (aeval_mem_closure y c g) (aeval_mem_closure y c h)

end BirationalRatioClosure

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

def BdPtsNull.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E),
    IsPtsNull (mCoordIdeal D.y) D.n D.Bd

namespace Line

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

def BoundaryNull.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E),
    IsPtsNull (mCoordIdeal D.y) D.n D.Bd

namespace Line

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def BoundaryPtsNull.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E),
    IsPtsNull (mCoordIdeal D.y) D.n D.Bd

namespace Line

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

def ParamImageNull.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d m : ℕ)
    (V A : Fin m → Set (Fin d → ℂ)) (γ : Fin m → (Fin d → ℂ) → (Σ k, ι k) → ℂ) (N : Set ((Σ k, ι k) → ℂ)),
    (∀ i, IsOpen (V i)) → (∀ i, A i ⊆ V i) → (∀ i, volume (A i) = 0) → (∀ i, AnalyticOnNhd ℂ (γ i) (V i)) →
    (∀ z ∈ N ∩ mcPts P, ∃ i, ∃ w ∈ A i, ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ z = torusSmul c (γ i w)) →
    IsPtsNull P d N

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def PtsMonoSemipos.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (L : _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (r : ℝ) (g₁ g₂ : ((Σ k, ι k) → ℂ) → ℝ) (N : Set ((Σ k, ι k) → ℂ)),
    IsArithVar P (e + 1) → IsSemipositiveH P L → 0 < r → IsPtsNull P e N →
    (∀ z ∈ mcPts P, z ∉ N → g₁ z ≤ g₂ z) →
    IsPtsIntegrable P (fun (_ : Fin e) z => Real.log (L.h z) / r) g₁ →
    IsPtsIntegrable P (fun (_ : Fin e) z => Real.log (L.h z) / r) g₂ →
    ptsIntegral P (fun (_ : Fin e) z => Real.log (L.h z) / r) g₁ ≤
      ptsIntegral P (fun (_ : Fin e) z => Real.log (L.h z) / r) g₂

namespace Line

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo

namespace PtsPencil

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem cxHessian_congr {D : ℕ} {f f' : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ} (h : f =ᶠ[𝓝 y] f') :
    cxHessian f y = cxHessian f' y := by
  have h2 : fderiv ℝ (fderiv ℝ f) y = fderiv ℝ (fderiv ℝ f') y := (h.fderiv (𝕜 := ℝ)).fderiv_eq
  ext i j
  simp only [cxHessian, h2]

theorem cxHessian_lin {D : ℕ} {f g ψ : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ} (a b : ℝ)
    (hf : ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 f y') (hg : ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 g y')
    (hψ : ψ =ᶠ[𝓝 y] fun y' => a * f y' + b * g y') :
    cxHessian ψ y = (a : ℂ) • cxHessian f y + (b : ℂ) • cxHessian g y := by
  have h1 : fderiv ℝ ψ =ᶠ[𝓝 y] fun y' => a • fderiv ℝ f y' + b • fderiv ℝ g y' := by
    filter_upwards [hψ.fderiv (𝕜 := ℝ), hf, hg] with y' h1 h2 h3
    rw [h1]
    exact (((h2.differentiableAt (by norm_num)).hasFDerivAt.const_mul a).add
      ((h3.differentiableAt (by norm_num)).hasFDerivAt.const_mul b)).fderiv
  have df : DifferentiableAt ℝ (fderiv ℝ f) y :=
    (hf.self_of_nhds.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have dg : DifferentiableAt ℝ (fderiv ℝ g) y :=
    (hg.self_of_nhds.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hH : fderiv ℝ (fderiv ℝ ψ) y = a • fderiv ℝ (fderiv ℝ f) y + b • fderiv ℝ (fderiv ℝ g) y := by
    rw [h1.fderiv_eq]
    exact ((df.hasFDerivAt.const_smul a).add (dg.hasFDerivAt.const_smul b)).fderiv
  ext i j
  simp only [cxHessian, hH, Matrix.add_apply, Matrix.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  push_cast
  ring

def IsC2AlongSheets {e : ℕ} (Q : Ideal (MRing ι)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (f : ((Σ k, ι k) → ℂ) → ℝ) : Prop :=
  ∀ y w γ, IsSheet Q Ψ y w γ → ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 (fun y'' => f (γ y'')) y'

theorem isC2AlongSheets_log_metric {e : ℕ} (Q : Ideal (MRing ι))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) {L : _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hL : IsSmoothHerm L) :
    IsC2AlongSheets Q Ψ fun z => Real.log (L.h z) := by
  intro y w γ hs
  have han : ∀ᶠ y' in 𝓝 y, AnalyticAt ℂ γ y' := (sheet_analyticAt osgood hs).eventually_analyticAt
  have hmc : ∀ᶠ y' in 𝓝 y, γ y' ∈ mcPts Q := hs.2.mono fun _ h => h.2.1
  exact (han.and hmc).mono fun y' h => pot_contDiffAt hL h.1 h.2.1

theorem IsC2AlongSheets.lin {e : ℕ} {Q : Ideal (MRing ι)}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {f g : ((Σ k, ι k) → ℂ) → ℝ}
    (hf : IsC2AlongSheets Q Ψ f) (hg : IsC2AlongSheets Q Ψ g) (a b : ℝ) :
    IsC2AlongSheets Q Ψ fun z => a * f z + b * g z := by
  intro y w γ hs
  filter_upwards [hf y w γ hs, hg y w γ hs] with y' h1 h2
  exact (contDiffAt_const.mul h1).add (contDiffAt_const.mul h2)

theorem sheetDensity_congr {e : ℕ} (Q : Ideal (MRing ι))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) {φ φ' : Fin e → ((Σ k, ι k) → ℂ) → ℝ}
    (h : ∀ j, ∀ z ∈ mcPts Q, φ j z = φ' j z) (g : ((Σ k, ι k) → ℂ) → ℝ) (y : Fin e → ℂ)
    (w : ((k : K) → ι k) → ℂ) :
    sheetDensity Q Ψ φ g y w = sheetDensity Q Ψ φ' g y w := by
  by_cases hγ : ∃ γ, IsSheet Q Ψ y w γ
  · simp only [sheetDensity, dif_pos hγ]
    have hmc : ∀ᶠ y' in 𝓝 y, hγ.choose y' ∈ mcPts Q := hγ.choose_spec.2.mono fun _ h => h.2.1
    have hH : (fun k => cxHessian (fun y' => φ k (hγ.choose y')) y) =
        fun k => cxHessian (fun y' => φ' k (hγ.choose y')) y :=
      funext fun k => cxHessian_congr (hmc.mono fun y' hy' => h k _ hy')
    simp only [maDensity, hH]
  · simp only [sheetDensity, dif_neg hγ]

theorem ptsIntegral_congr {e : ℕ} (Q : Ideal (MRing ι)) {φ φ' : Fin e → ((Σ k, ι k) → ℂ) → ℝ}
    (h : ∀ j, ∀ z ∈ mcPts Q, φ j z = φ' j z) (g : ((Σ k, ι k) → ℂ) → ℝ) :
    ptsIntegral Q φ g = ptsIntegral Q φ' g := by
  have hA : ∀ Ψ, ptsIntegralAt Q Ψ φ g = ptsIntegralAt Q Ψ φ' g := fun Ψ => by
    simp only [ptsIntegralAt, sheetDensity_congr Q Ψ h g]
  simp only [ptsIntegral, hA]

def mixW {e : ℕ} (α β : ((Σ k, ι k) → ℂ) → ℝ) (i : ℕ) : Fin e → ((Σ k, ι k) → ℂ) → ℝ :=
  fun k => if (k : ℕ) < i then β else α

theorem mixW_zero {e : ℕ} (α β : ((Σ k, ι k) → ℂ) → ℝ) : mixW (e := e) α β 0 = fun _ => α := by
  funext k
  simp [mixW]

theorem mixedDisc_eq_mdisc {D : ℕ} (A : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    mixedDisc A = ReciprocityTheory.AnForm.mdisc A := rfl

theorem sheetDensity_pencil {e : ℕ} (Q : Ideal (MRing ι))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) {α β : ((Σ k, ι k) → ℂ) → ℝ}
    (hα : IsC2AlongSheets Q Ψ α) (hβ : IsC2AlongSheets Q Ψ β) (a b : ℝ)
    {φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ} (hφ : ∀ j, ∀ z ∈ mcPts Q, φ j z = a * α z + b * β z)
    (g : ((Σ k, ι k) → ℂ) → ℝ) (y : Fin e → ℂ) (w : ((k : K) → ι k) → ℂ) :
    sheetDensity Q Ψ φ g y w = ∑ i ∈ Finset.range (e + 1),
      (e.choose i : ℝ) * b ^ i * a ^ (e - i) * sheetDensity Q Ψ (mixW α β i) g y w := by
  by_cases hγ : ∃ γ, IsSheet Q Ψ y w γ
  · simp only [sheetDensity, dif_pos hγ]
    have hs : IsSheet Q Ψ y w hγ.choose := hγ.choose_spec
    have hmc : ∀ᶠ y' in 𝓝 y, hγ.choose y' ∈ mcPts Q := hs.2.mono fun _ h => h.2.1
    have hHφ : (fun k => cxHessian (fun y' => φ k (hγ.choose y')) y) = fun _ =>
        (a : ℂ) • cxHessian (fun y' => α (hγ.choose y')) y +
          (b : ℂ) • cxHessian (fun y' => β (hγ.choose y')) y :=
      funext fun k => cxHessian_lin a b (hα y w _ hs) (hβ y w _ hs)
        (hmc.mono fun y' hy' => hφ k _ hy')
    have hHmix : ∀ i, (fun k : Fin e => cxHessian (fun y' => mixW α β i k (hγ.choose y')) y) =
        fun k : Fin e => if (k : ℕ) < i then cxHessian (fun y' => β (hγ.choose y')) y
          else cxHessian (fun y' => α (hγ.choose y')) y := by
      intro i
      funext k
      unfold mixW
      split_ifs <;> rfl
    simp only [maDensity, hHφ, hHmix, mixedDisc_eq_mdisc, ReciprocityTheory.AnForm.A.mdisc_const]
    rw [add_comm, ReciprocityTheory.AnForm.A.det_smul_add_smul_eq_sum_mdisc, Complex.re_sum, Finset.mul_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hc : (e.choose i : ℂ) * (b : ℂ) ^ i * (a : ℂ) ^ (e - i) =
        (((e.choose i : ℝ) * b ^ i * a ^ (e - i) : ℝ) : ℂ) := by push_cast; ring
    rw [hc, Complex.re_ofReal_mul]
    ring
  · simp only [sheetDensity, dif_neg hγ, mul_zero, Finset.sum_const_zero]

theorem fibreSum_pencil {e : ℕ} {Q : Ideal (MRing ι)} (hQ : IsArithVar Q (e + 1))
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (hΨ : IsGoodProj Q Ψ)
    {α β : ((Σ k, ι k) → ℂ) → ℝ} (hα : IsC2AlongSheets Q Ψ α) (hβ : IsC2AlongSheets Q Ψ β) (a b : ℝ)
    {φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ} (hφ : ∀ j, ∀ z ∈ mcPts Q, φ j z = a * α z + b * β z)
    (g : ((Σ k, ι k) → ℂ) → ℝ) (y : Fin e → ℂ) :
    ∑ᶠ w ∈ fibre Q Ψ y, sheetDensity Q Ψ φ g y w = ∑ i ∈ Finset.range (e + 1),
      (e.choose i : ℝ) * b ^ i * a ^ (e - i) * ∑ᶠ w ∈ fibre Q Ψ y, sheetDensity Q Ψ (mixW α β i) g y w := by
  have hfin := fibreFinite K ι Q e Ψ hQ hΨ y
  simp only [finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun w _ => sheetDensity_pencil Q Ψ hα hβ a b hφ g y w

theorem ptsIntegral_pencil {e : ℕ} {Q : Ideal (MRing ι)} (hQ : IsArithVar Q (e + 1))
    {α β : ((Σ k, ι k) → ℂ) → ℝ} (hα : ∀ Ψ, IsC2AlongSheets (e := e) Q Ψ α)
    (hβ : ∀ Ψ, IsC2AlongSheets (e := e) Q Ψ β) (g : ((Σ k, ι k) → ℂ) → ℝ)
    (hint : ∀ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj Q Ψ → ∀ i ∈ Finset.range (e + 1),
      Integrable (fun y => ∑ᶠ w ∈ fibre Q Ψ y, sheetDensity Q Ψ (mixW α β i) g y w))
    (a b : ℝ) {φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ} (hφ : ∀ j, ∀ z ∈ mcPts Q, φ j z = a * α z + b * β z) :
    ptsIntegral Q φ g = ∑ i ∈ Finset.range (e + 1),
      (e.choose i : ℝ) * b ^ i * a ^ (e - i) * ptsIntegral Q (mixW (e := e) α β i) g := by
  simp only [ptsIntegral]
  split_ifs with hΨ
  · simp only [ptsIntegralAt]
    have hfun : (fun y => ∑ᶠ w ∈ fibre Q hΨ.choose y, sheetDensity Q hΨ.choose φ g y w) =
        fun y => ∑ i ∈ Finset.range (e + 1), (e.choose i : ℝ) * b ^ i * a ^ (e - i) *
          ∑ᶠ w ∈ fibre Q hΨ.choose y, sheetDensity Q hΨ.choose (mixW α β i) g y w :=
      funext fun y => fibreSum_pencil hQ hΨ.choose_spec (hα _) (hβ _) a b hφ g y
    rw [hfun, integral_finsetSum _ fun i hi => (hint _ hΨ.choose_spec i hi).const_mul _]
    exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  · simp


open Matrix in
theorem integrable_of_nodes {Y : Type*} [MeasurableSpace Y] {μ : Measure Y} {N : ℕ} (M : ℕ → Y → ℝ)
    (h : ∀ j : Fin N, Integrable (fun y => ∑ i ∈ Finset.range N,
      (1 / (((j : ℕ) + 1 : ℕ) : ℝ)) ^ i * M i y) μ) :
    ∀ i < N, Integrable (M i) μ := by
  let x : Fin N → ℝ := fun j => 1 / (((j : ℕ) + 1 : ℕ) : ℝ)
  have hinj : Function.Injective x := by
    intro j k hjk
    simp only [x, one_div, _root_.inv_inj, Nat.cast_inj] at hjk
    exact Fin.ext (by omega)
  have hdet : IsUnit (Matrix.vandermonde x).det := by
    rw [isUnit_iff_ne_zero, Matrix.det_vandermonde_ne_zero_iff]
    exact hinj
  let F : Y → Fin N → ℝ := fun y j => ∑ i ∈ Finset.range N, x j ^ i * M i y
  have hval : ∀ y, F y = Matrix.vandermonde x *ᵥ fun i : Fin N => M i y := by
    intro y
    funext j
    simp only [F, Matrix.mulVec, dotProduct, Matrix.vandermonde_apply]
    exact (Fin.sum_univ_eq_sum_range (fun i => x j ^ i * M i y) N).symm
  have hinv : ∀ y, (fun i : Fin N => M i y) = (Matrix.vandermonde x)⁻¹ *ᵥ F y := by
    intro y
    rw [hval, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  intro i hi
  have hM : M i = fun y => ∑ j : Fin N, (Matrix.vandermonde x)⁻¹ ⟨i, hi⟩ j * F y j := by
    funext y
    have := congrFun (hinv y) ⟨i, hi⟩
    simpa only [Matrix.mulVec, dotProduct] using this
  rw [hM]
  exact integrable_finsetSum _ fun j _ => (h j).const_mul _

end PtsPencil

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end
