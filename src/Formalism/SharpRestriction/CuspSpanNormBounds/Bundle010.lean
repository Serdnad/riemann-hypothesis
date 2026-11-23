module

public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle007
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle008
public import Formalism.SharpRestriction.CuspSpanNormBounds.WeightedLatticeSum
public import Formalism.SharpRestriction.CuspSpanNormBounds.CntPartners
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.CuspSpanNormBounds.AuxiliarySlotStates
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle006
public import Formalism.SharpRestriction.CuspSpanNormBounds.FamilyBlockLiftEstimate
import Formalism.SharpRestriction.CuspSpanNormBounds.WeightedMirrorLevelOperator
public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
public import Formalism.SharpRestriction.Bundle001
public import Formalism.SharpRestriction.ParConsts

@[expose] public section

section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace Formalism.MainNotions.OnePlaceEstimates

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions

theorem cOfDpsi_one : cOfDpsi ((1 : ℝ) : ℂ) = cStd := by
  simp [cOfDpsi, cStd]

def TheoremBPrimePointwise (D : D7) (Ch Cg Cb : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp))
    (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) (ka b : ℝ),
    LocOk D Ch Cg L L.lam ka b 1 → IsKFinCoefH L.σ f → IsSection D.R.k D.R.rS L.z L.z' μsec →
    ∀ γ : Point ℂ (D.R.rS + 1), Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ ≠ 0 → BpIneq D Cb L f μsec b γ

def PathWeightComponents (D : D7) (C : ℝ) : Prop :=
  ∀ T T' : ℕ, 1 ≤ T → 1 ≤ T' →
    ∑' γ : {γ : Point D.host.E (D.R.rS + 1) // IsBPt D T T' γ}, ENNReal.ofReal (wPt D γ.1)⁻¹ ≤
      ENNReal.ofReal (C ^ (Fintype.card D.what₂.Tau * (D.R.rS + 1)))

def ConclusionB3 (D : D7) (Aw Ch Cg Cb : ℝ) : Prop :=
  ∀ (T T' : ℕ) (b : ℝ) (X : BData D Ch Cg T T' b 0),
    (∀ v, AllGaps (X.L v).lam (Cg * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 4)) →
    BSumRot D X (fun γ => normWt D T T' γ ^ (Aw * ((D.R.rS : ℝ) + 1) ^ 2)) ≤
      ENNReal.ofReal (Real.exp (Cb * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 5 * (Fintype.card D.what₂.Tau : ℝ) * Real.log b)) *
        jSqG D X

def FormalDegreeRatioAlt (_D : D7) : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (X : TensorDS n ε μ H σ),
    IsHCParam μ → IsDS ε μ σ →
    (∀ v w : H, IsKFin ε σ v → IsKFin ε σ w →
      MemLp (fun g : Formalism.REAL.UJ ε => (frob (umat g) : ℂ) * coefOn σ v w g) 2 (Formalism.REAL.muG ε)) →
    ∀ s ∈ X.Sm, ∀ (v : H) (vs : X.Hs s), v ≠ 0 → vs ≠ 0 →
      fdegOf (Formalism.REAL.muG ε) (X.σs s) vs / fdegOf (Formalism.REAL.muG ε) σ v =
        ∏ s' ∈ Finset.univ.erase s, (μ s + 1 - μ s') / (μ s - μ s')

def RngU (D : D7) (Cu Cg' : ℝ) (lam' lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) : Prop :=
  AllGaps lam0 (Cg' * D.R.k * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3) ∧
    l1 lam' lam0 ≤ Cu * D.R.k * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3

def UniformityTheoremBPrime (D : D7) (Ch Cu Cg Cg' Cb : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ)
    (f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)) (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ)
    (ka b : ℝ), LocOk D Ch Cg L lam0 ka b 1 → RngU D Cu Cg' L.lam lam0 →
    IsKFinCoefH L.σ f → IsSection D.R.k D.R.rS L.z L.z' μsec → jNorm2 L f μsec ≠ 0 →
    ∀ γ : Point ℂ (D.R.rS + 1), Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ ≠ 0 → BpIneq D Cb L f μsec b γ

def Dpt {r : ℕ} (γ : Point ℂ (r + 1)) (l : Fin (r + 1)) : ℂ := leadMinor (ptMat γ) (l.val + 1) (by omega)

def scaleBlocks (κ τ : ℝ) (r : ℕ) : ℕ → List (ℂ × ℕ) → List (ℂ × ℕ)
  | _, [] => []
  | acc, (t, s) :: bs =>
    (((τ ^ 2 * κ ^ (2 * (r + 1 - (acc + s)) + (s - 1)) : ℝ) : ℂ) * t, s) :: scaleBlocks κ τ r (acc + s) bs

def FrameBesselBound (D : D7) (Cgf Cf : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)) (κ₀ κ τ : ℝ),
    0 < κ₀ → 0 < κ → 0 < τ → L.c = cOfDpsi (κ₀ : ℂ) → 0 < L.κN → L.κN ≠ ⊤ → L.ε = epsSH D.R →
    GapAtLeast L.ε L.lam (Cgf * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
      (((3 * (D.R.rS + 1) : ℕ) : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 2 + ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 3)) →
    IsKFinCoefH L.σ f →
    ∃ (L₁ : LocBessel D.R.k D.R.rS) (f₁ : Mx D.R.k D.R.rS → (L₁.Wq →L[ℂ] L₁.Wp)),
      L₁.ε = L.ε ∧ L₁.lam = L.lam ∧ L₁.u = L.u ∧ L₁.u' = L.u' ∧ L₁.c = cOfDpsi ((κ * κ₀ : ℝ) : ℂ) ∧
      0 < L₁.κN ∧ L₁.κN ≠ ⊤ ∧
      Tz D.R.k D.R.rS L₁.z = τ ^ 2 * Tz D.R.k D.R.rS L.z ∧ Tz D.R.k D.R.rS L₁.z' = τ ^ 2 * Tz D.R.k D.R.rS L.z' ∧
      IsKFinCoefH L₁.σ f₁ ∧
      ∀ μsec, IsSection D.R.k D.R.rS L.z L.z' μsec → ∃ μsec₁, IsSection D.R.k D.R.rS L₁.z L₁.z' μsec₁ ∧
        ∃ K₁ : ℝ, 0 < K₁ ∧ jNorm2 L₁ f₁ μsec₁ = ENNReal.ofReal K₁ * jNorm2 L f μsec ∧
        ∀ γ : Point ℂ (D.R.rS + 1), Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ ≠ 0 →
          ∃ γ₁ : Point ℂ (D.R.rS + 1), γ₁.1 = scaleBlocks κ τ D.R.rS 0 γ.1 ∧
            Gpt (Tz D.R.k D.R.rS L₁.z) (Tz D.R.k D.R.rS L₁.z') γ₁ =
              κ ^ (2 * D.R.rS * (D.R.rS + 1)) * τ ^ (4 * (D.R.rS + 1)) *
                Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ ∧
            ENNReal.ofReal (ptWeight D.R.k D.R.rS (Tz D.R.k D.R.rS L₁.z) (Tz D.R.k D.R.rS L₁.z') γ₁) * orbSq L₁ f₁ γ₁ ≤
              ENNReal.ofReal (K₁ * (max κ κ⁻¹ ^ (Cf * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2) *
                  max τ τ⁻¹ ^ (Cf * ((2 * D.R.rS + 2 : ℕ) : ℝ)))) *
                (ENNReal.ofReal (ptWeight D.R.k D.R.rS (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ) * orbSq L f γ) ∧
            ENNReal.ofReal K₁ *
                (ENNReal.ofReal (ptWeight D.R.k D.R.rS (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ) * orbSq L f γ) ≤
              ENNReal.ofReal (max κ κ⁻¹ ^ (Cf * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2) *
                  max τ τ⁻¹ ^ (Cf * ((2 * D.R.rS + 2 : ℕ) : ℝ))) *
                (ENNReal.ofReal (ptWeight D.R.k D.R.rS (Tz D.R.k D.R.rS L₁.z) (Tz D.R.k D.R.rS L₁.z') γ₁) *
                  orbSq L₁ f₁ γ₁)

end Formalism.MainNotions.OnePlaceEstimates

namespace Formalism.MainNotions.OnePlaceEstimates

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.S.TopsChoicePartA
open scoped ContDiff

section Cells71

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end Cells71

structure TensorDSd (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) where
  Sm : Finset (Fin n)
  Hs : Fin n → Type
  [nH : ∀ s, NormedAddCommGroup (Hs s)]
  [iH : ∀ s, InnerProductSpace ℂ (Hs s)]
  [cH : ∀ s, CompleteSpace (Hs s)]
  σs : ∀ s, Matrix (Fin n) (Fin n) ℂ → (Hs s →L[ℂ] Hs s)
  ds : ∀ s ∈ Sm, IsHCParam (μ - Pi.single s 1) ∧ IsDS ε (μ - Pi.single s 1) (σs s)
  inequiv : ∀ s ∈ Sm, ∀ s' ∈ Sm, s ≠ s' → ¬ ∃ U : Hs s ≃ₗᵢ[ℂ] Hs s',
    ∀ g ∈ UJset ε, ∀ x, U (σs s g x) = σs s' g (U x)
  toSum : ∀ (v w : H) (x y : Fin n → ℂ), IsKFin ε σ v → IsKFin ε σ w →
    ∃ (ι : Type) (_ : Fintype ι) (sI : ι → Fin n) (vI wI : ∀ i, Hs (sI i)),
      (∀ i, sI i ∈ Sm ∧ IsKFin ε (σs (sI i)) (vI i) ∧ IsKFin ε (σs (sI i)) (wI i)) ∧
      ∀ g ∈ UJset ε, ⟪w, σ g v⟫_ℂ * (star y ⬝ᵥ (g⁻¹ *ᵥ x)) = ∑ i, ⟪wI i, σs (sI i) g (vI i)⟫_ℂ
  ofSum : ∀ s ∈ Sm, ∀ v w : Hs s, IsKFin ε (σs s) v → IsKFin ε (σs s) w →
    ∃ (ι : Type) (_ : Fintype ι) (vI wI : ι → H) (xI yI : ι → Fin n → ℂ),
      (∀ i, IsKFin ε σ (vI i) ∧ IsKFin ε σ (wI i)) ∧
      ∀ g ∈ UJset ε, ⟪w, σs s g v⟫_ℂ = ∑ i, ⟪wI i, σ g (vI i)⟫_ℂ * (star (yI i) ⬝ᵥ (g⁻¹ *ᵥ xI i))

attribute [instance] TensorDSd.nH TensorDSd.iH TensorDSd.cH

end Formalism.MainNotions.OnePlaceEstimates

section ShortGrids

open Filter Topology NumberField
open scoped ContDiff ComplexOrder nonZeroDivisors

namespace Formalism.MainNotions.OnePlaceEstimates

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA

section Raw

variable {D : D7} {k0 : ℕ} (Gm : GramWordSpace.GramMap k0 D.R.rS) (X : GramWordSpace.Dat D k0) (Pst : D.what₂.Tau → ℝ → ℝ)

end Raw

end Formalism.MainNotions.OnePlaceEstimates

end ShortGrids

namespace Formalism.MainNotions.OnePlaceEstimates

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.LevR
open Filter Topology
open scoped ContDiff

export Formalism.MainNotions.S.UnitaryLevelOperators (levOf cutF Msq)

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

end Family

end Formalism.MainNotions.OnePlaceEstimates
end
end

section

noncomputable section

namespace Formalism.MainNotions.LatticeSumConvergence

theorem LatSum_holds : Formalism.MainNotions.KTwoMinorIntegrality.LatSum :=
  fun ι _ P R hR hsep => Formalism.MainNotions.WeightedLatticeSum.latSum ι P R hR hsep

end Formalism.MainNotions.LatticeSumConvergence

end
end

section

noncomputable section

open NumberField MeasureTheory
open scoped ENNReal

namespace Formalism.MainNotions.LatticeIndexAndWeightTheory

export Formalism.MainNotions.S.UnitaryVolumeMass (KTwoParameterConditions Kpp)

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Hyps

variable (D : D7) (large₂ : SizeData₂ D)

end Hyps

def IsInertiaCyclotomicGeneratorElement {D : D7} {u u' : D.what₂.Word} (t : D.s.Term u u') : Prop :=
  D.s.relevant t ∧ D.s.Gterm t = 0 ∧ ¬ D.s.isId t

section TermObj

variable {D : D7} (X : TermTie D) {u u' : D.what₂.Word} (t : D.s.Term u u')

def Iof : Submodule D.host.E (hS D).V := Isp (X.fl t).fl (X.fl' t).fl

def OrthogonalComplementV0 : Submodule D.host.E (hS D).V := perpS (hS D) (Xplus (X.fl t) ⊔ Xplus (X.fl' t))

def jOf : ℕ := D.R.rS - Module.finrank D.host.E (Iof X t)

def NDl (l : ℕ) : ℝ := (Nloc (ddS D) D.R.rS l (Dl (X.fl t).fl (X.fl' t).fl l) : ℝ)

def DelJ : ℝ := NDl X t (jOf X t)

def ends : Finset ℕ := blockEnds (X.fl t).fl (X.fl' t).fl (jOf X t)

def sg (H1 : ℝ) (τ : D.what₂.Tau) : ℝ :=
  (ends X t).fold max 1 (fun l =>
    absReal D.host.rdE (embS D τ) D.R.rS l (Dl (X.fl t).fl (X.fl' t).fl l) / (2 * H1) ^ (2 * D.R.rS))

def FrameHyp : Prop :=
  (X.fl t).fl.e = D.sp.hypE ∧ (X.fl t).fl.z = D.zmOf u ∧ IsRowLat D (X.fl t).fl (X.abelian₂ t) ∧
    FrameOK D (X.abelian₂ t) (X.fl' t)

end TermObj

def NF {D : D7} (X : TermTie D) {u u' : D.what₂.Word} (t : D.s.Term u u') : Prop :=
  ∃ j : ℕ, j ≤ D.R.rS ∧ (u = u' → 1 ≤ j) ∧
    (∀ a : ℕ, (∃ x ∈ Iof X t, x ≠ 0 ∧ (X.fl t).fl.level x = a) ↔ (j + 1 ≤ a ∧ a ≤ D.R.rS)) ∧
    (∀ a : ℕ, (∃ x ∈ Iof X t, x ≠ 0 ∧ (X.fl' t).fl.level x = a) ↔ (j + 1 ≤ a ∧ a ≤ D.R.rS)) ∧
    (∃ c : D.host.E, (X.fl' t).fl.z - c • (X.fl t).fl.z ∈ Xsp (X.fl t) ⊔ Xsp (X.fl' t) ∧
      c * star c * ((Tu D u : ℕ) : D.host.E) = ((Tu D u' : ℕ) : D.host.E)) ∧
    Dl (X.fl t).fl (X.fl' t).fl j ≠ 0 ∧
    (OrthogonalComplementV0 X t ⊓ Xsp (X.fl t) = Iof X t ∧ OrthogonalComplementV0 X t ⊔ Xsp (X.fl t) = (X.fl t).fl.XplusPerp) ∧
    (OrthogonalComplementV0 X t ⊓ Xsp (X.fl' t) = Iof X t ∧ OrthogonalComplementV0 X t ⊔ Xsp (X.fl' t) = (X.fl' t).fl.XplusPerp)

section Datum

variable {D : D7} (X : TermTie D) {u u' : D.what₂.Word}

def SameDC {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F₁ F₂ : LFlag (D.sp.Y 0) D.R.rS T') : Prop :=
  ∃ σ ∈ Formalism.HermitianLatticesTheory.isom (hS D).hT,
    (∀ a : Fin D.R.rS, σ (F.fl.e a) - F.fl.e a ∈ Xflag F a.val) ∧ σ F.fl.z - F.fl.z ∈ Xsp F ∧
    (∀ a : Fin D.R.rS, σ (F₁.fl.e a) - F₂.fl.e a ∈ Xflag F₂ a.val) ∧ σ F₁.fl.z - F₂.fl.z ∈ Xsp F₂

def TermInj (u : D.what₂.Word) : Prop :=
  ∀ t t' : D.s.Term u u, X.abelian₂ t = X.abelian₂ t' → TEqv D (X.abelian₂ t) (X.fl t) (X.fl' t) (X.fl' t') → t = t'

def NormOK (u : D.what₂.Word) : Prop :=
  (∀ p : D.s.Pair u u, X.wRow p = Formalism.MainNotions.S.wRow D (X.fl (D.s.pfst p)).fl (X.abelian₂ (D.s.pfst p))) ∧
  ∀ t : D.s.Term u u, IsInertiaCyclotomicGeneratorElement t → ∃ p : D.s.Pair u u, D.s.pfst p = t ∧ D.s.psnd p = t ∧
    X.beta p = LinearEquiv.refl D.host.E (hS D).V ∧
    D.s.pval p = ((Formalism.MainNotions.S.wRow D (X.fl t).fl (X.abelian₂ t) * hsNormSq (X.Jt t) : ℝ) : ℂ)

def IndW (D : D7) (σ : (hS D).V ≃ₗ[D.host.E] (hS D).V) (h : (D.sp.X 0).V ≃ₗ[D.host.E] (D.sp.X 0).V) : Prop :=
  ∀ w, σ (D.sp.iXY 0 w) - D.sp.iXY 0 (h w) ∈ Submodule.span D.host.E (Set.range D.sp.hypE)

def AmpOK : Prop :=
  (∀ (u u' : D.what₂.Word) (t : D.s.Term u u'), (X.fl t).fl.e = D.sp.hypE ∧ (X.fl t).fl.z = D.zmOf u) ∧
  ∃ (ρ : ∀ u : D.what₂.Word, ((D.sp.X 0).V ≃ₗ[D.host.E] (D.sp.X 0).V) → (X.Hpi u →L[ℂ] X.Hpi u))
    (δ : ∀ u u' : D.what₂.Word, D.s.Term u u' → ((hS D).V ≃ₗ[D.host.E] (hS D).V)),
    (∀ u, ρ u 1 = ContinuousLinearMap.id ℂ (X.Hpi u) ∧
      ∀ h ∈ Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT, ∀ h' ∈ Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT, ρ u (h * h') = (ρ u h).comp (ρ u h')) ∧
    (∀ u (K : Submodule ℂ (X.Hpi u)), (∀ h ∈ Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT, ∀ x ∈ K, ρ u h x ∈ K) → K = ⊥ ∨ K = ⊤) ∧
    (∀ u u', u ≠ u' → ∀ P : X.Hpi u' →L[ℂ] X.Hpi u,
      (∀ h ∈ Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT, (ρ u h).comp P = P.comp (ρ u' h)) → P = 0) ∧
    (∀ u u' (t : D.s.Term u u'), δ u u' t ∈ Formalism.HermitianLatticesTheory.isom (hS D).hT ∧
      (∀ a, δ u u' t (D.sp.hypE a) = (X.fl' t).fl.e a) ∧ δ u u' t (D.zmOf u') = (X.fl' t).fl.z) ∧
    (∀ u u' (t : D.s.Term u u'), ∀ σ ∈ Formalism.HermitianLatticesTheory.isom (hS D).hT,
      (∀ x ∈ Xplus (X.fl t) ⊔ Xplus (X.fl' t), σ x = x) →
      ∀ h ∈ Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT, ∀ h' ∈ Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT,
        IndW D σ h → IndW D ((δ u u' t)⁻¹ * σ * δ u u' t) h' → (ρ u h).comp (X.Jt t) = (X.Jt t).comp (ρ u' h')) ∧
    ∀ u (t : D.s.Term u u), IsInertiaCyclotomicGeneratorElement t → NF X t → ∀ x ∈ OrthogonalComplementV0 X t, δ u u t x - x ∈ Xsp (X.fl' t)

def TieOK (u : D.what₂.Word) : Prop :=
  (∀ t : D.s.Term u u, FrameHyp X t) ∧ TermInj X u ∧ NormOK X u ∧ AmpOK X

end Datum

section Terms

variable (D : D7) (large₂ : SizeData₂ D) (X : TermTie D)

end Terms

section Size

variable (D : D7) (large₂ : SizeData₂ D)

end Size

section Mass

variable (D : D7) (large₂ : SizeData₂ D)

end Mass

section Targets

variable (D : D7) (large₂ : SizeData₂ D) (X : TermTie D)

end Targets

section Packet

variable (D : D7) (large₂ : SizeData₂ D) (X : TermTie D) (G : GlobalTheoryTheory.GenusMassVolumes.GaugeFam D.host.F D.host.E D.sp.cm.sig)

end Packet

section Family

variable {eps : ℝ} (Fm : FamP eps) (At : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))

end Family

end Formalism.MainNotions.LatticeIndexAndWeightTheory

end
end
