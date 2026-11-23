module

public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Filter Topology
open scoped TensorProduct ContDiff

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S T : HSp D}

theorem actO_add (g : GA D S) (h : GA D T) (x y : WO S T) :
    actO S T g h (x + y) = actO S T g h x + actO S T g h y := by
  unfold actO
  simp [Matrix.mul_add, Matrix.add_mul, smul_add]

end Formalism.IndefR.Eqv

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField
open scoped TensorProduct ContDiff

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def ratMx (D : D7) (m n : ℕ) : AddSubgroup (Mx D m n) :=
  ((incA D).toAddMonoidHom.mapMatrix (m := Fin m) (n := Fin n)).range

def embI (S T : HSp D) {r : ℕ} (C : Matrix (Fin T.rank) (Fin r) D.host.E) (a : Mx D r S.rank) : WO S T :=
  HMul.hMul (C.map (incA D)) a

def ellI (S T : HSp D) {r : ℕ} (C : Matrix (Fin T.rank) (Fin r) D.host.E) (μ : Measure (Mx D r S.rank))
    (𝓕 : Set (Mx D r S.rank)) (f : WO S T → ℂ) : ℂ :=
  ∫ a in 𝓕, f (embI S T C a) ∂μ

end Formalism.IndefR.Eqv

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField
open scoped TensorProduct

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem infMat_eq (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) (g : GA D V) (i j : Fin V.rank) :
    infMat D.sp.cm.sig V.gram (θ τ) g i j = θ τ (infPart D (mt V g i j)) := rfl

theorem mt_mul (V : HSp D) (a b : GA D V) : mt V (a * b) = mt V a * mt V b := by
  simp only [Formalism.L2.Theta.mt, map_mul, Units.val_mul]

theorem mt_one (V : HSp D) : mt V 1 = 1 := by
  simp only [Formalism.L2.Theta.mt, map_one, Units.val_one]

end Formalism.IndefR.Eqv

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory NumberField Matrix
open scoped TensorProduct

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

def InfFamExists : Prop :=
  ∃ θ : Datum.InfFam D, IsInfFam θ

def InfFamUnique : Prop :=
  ∀ θ θ' : Datum.InfFam D, IsInfFam θ → IsInfFam θ' → θ = θ'

def AtTauExUnique : Prop :=
  ∀ θ : Datum.InfFam D, IsInfFam θ → ∀ (V : HSp D) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ),
    gᴴ * gramAt D V τ * g = gramAt D V τ → ∃! h : GA D V, IsAtTau θ V τ g h

def AtTauUnitary : Prop :=
  ∀ θ : Datum.InfFam D, IsInfFam θ → ∀ (V : HSp D) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (h : GA D V),
    IsAtTau θ V τ g h → gᴴ * gramAt D V τ * g = gramAt D V τ

def AtTauHom : Prop :=
  ∀ θ : Datum.InfFam D, IsInfFam θ → ∀ (V : HSp D) (τ : D.what₂.Tau),
    atTau θ V τ 1 = 1 ∧
    (∀ g g' : Matrix (Fin V.rank) (Fin V.rank) ℂ, gᴴ * gramAt D V τ * g = gramAt D V τ →
      g'ᴴ * gramAt D V τ * g' = gramAt D V τ → atTau θ V τ (g * g') = atTau θ V τ g * atTau θ V τ g') ∧
    ContinuousOn (atTau θ V τ) {g | gᴴ * gramAt D V τ * g = gramAt D V τ}

def GQDiscrete : Prop :=
  ∀ V : HSp D, DiscreteTopology (GQ V)

def FundDomExists : Prop :=
  ∀ V : HSp D, ∃ 𝓕 : Set (GA D V), MeasurableSet 𝓕 ∧ ∀ μ : Measure (GA D V), IsFundamentalDomain (GQ V) 𝓕 μ

variable {D}

def IsLevelA (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) : Prop :=
  IsCompact (Lev.levA V K : Set (GA D V)) ∧ IsOpen (((Lev.levA V K).subgroupOf (GfC V)) : Set (GfC V))

variable (D)

def MeasLevExists : Prop :=
  ∀ V : HSp D, V.SigOK → ∀ K : Subgroup (GL (Fin V.rank) (Lev.EAf D)), IsLevelA V K → ∃ μ, Lev.IsMeasLev V K μ

def MeasLevDefExists : Prop :=
  ∀ V : HSp D, V.SigOK → V.IsDefinite → ∀ K : Subgroup (GL (Fin V.rank) (Lev.EAf D)), IsLevelA V K →
    ∃ μ, Lev.IsMeasLevDef V K μ

def MeasFDExists : Prop :=
  ∀ V : HSp D, V.SigOK → ∀ K : Subgroup (GL (Fin V.rank) (Lev.EAf D)), IsLevelA V K →
    ∃ μ 𝓕, Lev.IsMeasFD V K μ 𝓕

end Formalism.IndefR.Eqv

end
end
