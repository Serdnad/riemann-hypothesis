module

public import Formalism.LocalToGlobal.KernelLattices.ColumnData
public import Formalism.LocalToGlobal.AlgebraicTheory.StatementKer
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open NumberField Formalism.BasicNotions

namespace Formalism.L2.Ker

open Formalism.MainNotions Formalism.L2.Col Formalism.L2.GlobalTheoryTheory.Jets

section Bridge

variable (D : D7)

variable {D}

def KapChoice.toCar {γ₀ : IsoK D} (k : KapChoice γ₀) : Cd.KapChoice (D := Car.ofRec D) γ₀ where
  pp := k.pp
  pp_over := k.pp_over
  pi := k.pi
  pi_gen := k.pi_gen
  gaP := k.gaP
  gaP_at := k.gaP_at
  rt := k.rt
  rt_pow := k.rt_pow

variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

def Base.toCar (B : Base D cc δ) : Cd.Base (Car.ofRec D) cc δ where
  L := B.L
  lat := B.lat
  ω₀ := B.ω₀
  t0 := B.t0
  γ₀ := B.γ₀
  gC := B.gC
  gC_spec := B.gC_spec
  kc := B.kc.toCar

variable {X : Fields}

def Seam.toCar (s : Seam D X) : Cd.Seam (Car.ofRec D) X := ⟨s.iE, s.iT, s.σ₀⟩

end Bridge

section OverColDat

variable (d : ColDat)

variable {d}


end OverColDat

namespace Test

open Formalism.BasicNotions.Examples₂ Formalism.FrobeniusOrbits

end Test

end Formalism.L2.Ker
end
end

section

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker.Cd

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Th1.H Formalism.L2.Col

variable {D : Car} {X : Fields}

def Seam.push (s : Seam D X) {a b : ℕ} (F : VCx X.Tau a b → ℂ) : TaylorLogMetric.VC D a b → ℂ := fun z => F fun τ => z (s.iT τ)

variable (s : Seam D X) {a b : ℕ}

end Formalism.L2.Ker.Cd
end
end

section

noncomputable section
open scoped BigOperators
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.Ker.Cd

open Formalism.MainNotions Formalism.L2.Col
open Formalism.L2.Th1.H (cmL CmOK matH stdLat pow4 imgLat relIdx IsIsom)
open Formalism.L2.Th1.E (IntCurve curveL)
open Formalism.L2.Th1.GD (LocNorm)
open Formalism.L2.AlgTh (KerStd lamF)

section Defs

variable {D : Car} {X : Fields} (s : Seam D X)

def Seam.flatV (a b : ℕ) : (DVar X.Tau a b → ℂ) ≃ₗ[ℂ] Formalism.L2.Ker.Cd.TaylorLogMetric.VC D a b where
  toFun z := fun τ i j => z (s.iT.symm τ, i, j)
  invFun w := fun k => w (s.iT k.1) k.2.1 k.2.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv z := by funext k; simp
  right_inv w := by funext τ i j; simp

def Seam.laF (T : Formalism.L2.Ker.Cd.TaylorLogMetric.Tor D) {a b : ℕ} (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) :
    AddSubgroup (DVar X.Tau a b → ℂ) :=
  (Formalism.L2.Ker.Cd.TaylorLogMetric.La D T L L').comap (s.flatV a b).toLinearMap.toAddMonoidHom

def Seam.StdAtP (p : ℕ) {n : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E n)) : Prop :=
  Formalism.L2.Ker.Cd.TaylorLogMetric.EqAt D p (Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D n) (s.lat N)

variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ)

def Base.IsCm (a₀ : ℕ) (b₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0) : Prop :=
  B.L = cmL a₀ b₀ D.host.d ha hd lam hlam ∧ B.ω₀ = lam * a₀

end Defs

def LamTie : Prop :=
  ∀ (D : Car) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : Formalism.L2.Ker.Cd.TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)
    (a b : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), s.Ok →
    lamF (ambOf s B χ cD) N N' = s.laF B.tor (s.lat N) (s.lat N')

end Formalism.L2.Ker.Cd
end
end
