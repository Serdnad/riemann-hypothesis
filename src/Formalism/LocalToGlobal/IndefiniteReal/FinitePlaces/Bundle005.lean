module

public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section



noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix NumberField
open scoped TensorProduct

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

variable (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))

theorem frMapO_add (x y : WO S T) : frMapO S T βS βT (x + y) = frMapO S T βS βT x + frMapO S T βS βT y := by
  unfold frMapO
  rw [Matrix.map_add (toEAf D) (fun a b => (toEAf D).map_add a b), Matrix.mul_add, Matrix.add_mul]

theorem frMapO_zero : frMapO S T βS βT 0 = 0 := by
  unfold frMapO
  rw [Matrix.map_zero (toEAf D) (toEAf D).map_zero, Matrix.mul_zero, Matrix.zero_mul]

theorem frMapO_nsmul (k : ℕ) (x : WO S T) : frMapO S T βS βT (k • x) = k • frMapO S T βS βT x := by
  induction k with
  | zero => rw [zero_smul, zero_smul, frMapO_zero]
  | succ n ih => rw [succ_nsmul, succ_nsmul, frMapO_add, ih]

end Formalism.IndefR.Fin

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum
open scoped TensorProduct ComplexOrder

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev latAll (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) : AddSubgroup (WO S T) :=
  latO S T ΛS ΛT fun _ => True

def PlaceLatDual (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    (∀ e' : AE D, IsSplitIdem D e' → ∀ u ∈ latAll S T ΛS ΛT, u.map (fun a => e' * a) ∈ latAll S T ΛS ΛT) ∧
    (∀ e' : AE D, IsSplitIdem D e' → ∀ (g : GA D S) (h : GA D T), SuppAt e' S g → SuppAt e' T h →
      ∃ k : ℕ, 0 < k ∧ ∀ t ∈ latAll S T ΛS ΛT, k • actO S T g h t ∈ latAll S T ΛS ΛT) ∧
    ∀ (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P →
      (∀ y : WO S T, IsHalf (cA D e) y →
        ((∀ x ∈ latAll S T ΛS ΛT, IsHalf e x → ψ (symplO S T x y) = 1) ↔ y ∈ latAll S T ΛS ΛT)) ∧
      (∀ x : WO S T, IsHalf e x →
        ((∀ y ∈ latAll S T ΛS ΛT, IsHalf (cA D e) y → ψ (symplO S T x y) = 1) ↔ x ∈ latAll S T ΛS ΛT)) ∧
      (∀ k : ℕ, 0 < k → ∀ e₁ : AE D, (e₁ = e ∨ e₁ = cA D e) →
        ∃ R : Finset (WO S T), ∀ u ∈ latAll S T ΛS ΛT, IsHalf e₁ u →
          ∃ r ∈ R, ∃ v ∈ latAll S T ΛS ΛT, IsHalf e₁ v ∧ u = r + k • v) ∧
      ∀ e₁ : AE D, (e₁ = e ∨ e₁ = cA D e) → ∀ x : WO S T, IsHalf e₁ x → ∃ k : ℕ, 0 < k ∧ k • x ∈ latAll S T ΛS ΛT

def PlaceModelAt (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P →
    ∀ f₀ : WO S T → ℂ, IsThetaFunO ψ S T f₀ →
      (∀ u ∈ latAll S T ΛS ΛT, (IsHalf e u ∨ IsHalf (cA D e) u) → heisO ψ S T u f₀ = f₀) →
      ∀ e₁ : AE D, (e₁ = e ∨ e₁ = cA D e) →
        ∃ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) e₁ (latAll S T ΛS ΛT) 1 f₀ Tm ∧
          (∀ Tm', IsPlaceModel ψ (symplO S T) (heisO ψ S T) e₁ (latAll S T ΛS ΛT) 1 f₀ Tm' →
            ∀ Φ, IsSBHalf e₁ (latAll S T ΛS ΛT) Φ → Tm' Φ = Tm Φ) ∧
          (∀ Φ, IsSBHalf e₁ (latAll S T ΛS ΛT) Φ → IsThetaFunO ψ S T (Tm Φ)) ∧
          ∀ Φ, IsSBHalf e₁ (latAll S T ΛS ΛT) Φ → ∀ u : WO S T, (∀ i j, (e + cA D e) * u i j = 0) →
            heisO ψ S T u f₀ = f₀ → heisO ψ S T u (Tm Φ) = Tm Φ

def SplitLin (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P →
    ∀ f₀ : WO S T → ℂ, IsThetaFunO ψ S T f₀ →
    (∀ u ∈ latAll S T ΛS ΛT, (IsHalf e u ∨ IsHalf (cA D e) u) → heisO ψ S T u f₀ = f₀) →
    ∀ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latAll S T ΛS ΛT) 1 f₀ Tm →
    ∀ e₁ : AE D, IsSplitIdem D e₁ → e₁ * e = e₁ →
    ∀ (g : GA D S) (h : GA D T), SuppAt e₁ S g → SuppAt e₁ T h →
    ∀ x y : (AE D)ˣ, IsDetAt e₁ S g x → IsDetAt e₁ T h y →
      ∃ r : ℝ, 0 < r ∧
        (∀ Φ, IsSBHalf e (latAll S T ΛS ΛT) Φ →
          om (g, h) (Tm Φ) = ((r : ℂ) * (splitFacO χS χT x y : ℂ)) • Tm (fun t => Φ (actO S T g⁻¹ h⁻¹ t))) ∧
        ((∀ t : WO S T, IsHalf e t → (actO S T g h t ∈ latAll S T ΛS ΛT ↔ t ∈ latAll S T ΛS ΛT)) →
          (∃ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 ∧ nrm2 μ 𝓕 f₀ = 1) → r = 1)

end Formalism.IndefR.Fin

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def StepVecThetaSD (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (LS : Formalism.L2.DIV.LevDat D.host.E ℂ S.rank) (χj : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ)
    (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ)
    (f₀ f : WO S T → ℂ),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT →
    IsStepVecOf ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) βS βT LS χj Q ξ f₀ f →
    IsThetaFunO ψ S T f

def ThPVecThetaSD (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ)
    (f₀ f : WO S T → ℂ),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT →
    IsThPVecOf ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) βS βT Pg Q ξ f₀ f →
    IsThetaFunO ψ S T f

def VecThetaSD (D : D7) : Prop := StepVecThetaSD D ∧ ThPVecThetaSD D

end Formalism.IndefR.Fin
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.IndefR.Datum

def TwoSplits (D : D7) : Prop :=
  ∀ P : HeightOneSpectrum (𝓞 D.host.E), (2 : 𝓞 D.host.E) ∈ P.asIdeal → ¬ Lev.IsConjPl (D := D) P P

def TwoSplitIdem (D : D7) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 D.host.F), (2 : 𝓞 D.host.F) ∈ v.asIdeal →
    ∃ (e : AE D) (ε : AF D.host.F), IsSplitIdem D e ∧ IsPlaceIdem D v ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε

def LatSelfDual (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
      (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT →
      IsCompact ((latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True :
          AddSubgroup (WO S T)) : Set (WO S T)) ∧
      IsOpen {w : WO S T | ∃ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
          (fun _ => True), (w - u).map (finPart D) = 0} ∧
      (∀ a : AE D, finPart D a ∈ intAE D →
        ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
          a • u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) ∧
      ∀ x : WO S T, x.map (infPart D) = 0 →
        (x ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ↔
          ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
            ψ (symplO S T x u) = 1)


def HeisStable (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (S T : HSp D) (w₀ : WO S T) (f : WO S T → ℂ),
    IsThetaFunO ψ S T f → IsThetaFunO ψ S T (heisO ψ S T w₀ f)

def DRhoStable (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (S T : HSp D) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (f : WO S T → ℂ),
      IsThetaFunO ψ S T f → IsThetaFunO ψ S T (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f)

def PtStable (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
      (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
      (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ)
      (P : MvPolynomial (FVar D T.rank S.rank) ℂ),
      IsThetaFunO ψ S T f → IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f P)

end Formalism.IndefR.Fin

end
end
