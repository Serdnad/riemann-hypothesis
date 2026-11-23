module

public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle004
public import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.NormFr
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
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ThetaSquareIntegrable

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory Matrix
open Formalism.L2.Theta Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Scalar

variable {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

def IsEmbHom (ι : A.V →ₗ[D.host.E] B.V) (s : GA D A →* GA D B) : Prop :=
  ∀ h, EmbRel B A ι (s h) h

end Scalar

section Vec

variable {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

variable (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
  {Vt : D.what₂.Tau → Type} [∀ τ, NormedAddCommGroup (Vt τ)] [∀ τ, InnerProductSpace ℂ (Vt τ)]
  {S : D.what₂.Tau → SPar}




end Vec

end Formalism.IndefR.Mi

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Eqv MeasureTheory
  IsDedekindDomain NumberField

namespace Formalism.IndefR.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsQuotFrame (T : HSp D) {r : ℕ} (C C' : Matrix (Fin T.rank) (Fin r) D.host.E) (T0 : HSp D)
    (B0 : Matrix (Fin T.rank) (Fin T0.rank) D.host.E) : Prop :=
  IsIsoFrame T C ∧
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C' * T.gram * C' = 0 ∧
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C' * T.gram * C = 1 ∧
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * T.gram * B0 = 0 ∧
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C' * T.gram * B0 = 0 ∧
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B0 * T.gram * B0 = T0.gram ∧
    T.rank = 2 * r + T0.rank

def desc (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {r : ℕ} (C : Matrix (Fin T.rank) (Fin r) D.host.E)
    (μ : Measure (Mx D r S.rank)) (𝓕 : Set (Mx D r S.rank)) (T0 : HSp D)
    (B0 : Matrix (Fin T.rank) (Fin T0.rank) D.host.E) (f : WO S T → ℂ) : WO S T0 → ℂ :=
  fun x0 => Red ψ S T C μ 𝓕 f (embI S T B0 x0)

def IsLeviEmb (T : HSp D) {r : ℕ} (C C' : Matrix (Fin T.rank) (Fin r) D.host.E) (T0 : HSp D)
    (B0 : Matrix (Fin T.rank) (Fin T0.rank) D.host.E) (h0 : GA D T0) (h : GA D T) : Prop :=
  HMul.hMul (mt T h) (C.map (incA D)) = C.map (incA D) ∧
    HMul.hMul (mt T h) (C'.map (incA D)) = C'.map (incA D) ∧
    HMul.hMul (mt T h) (B0.map (incA D)) = HMul.hMul (B0.map (incA D)) (mt T0 h0)

def IsDescOf (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {r : ℕ} (C C' : Matrix (Fin T.rank) (Fin r) D.host.E)
    (T0 : HSp D) (B0 : Matrix (Fin T.rank) (Fin T0.rank) D.host.E) (μ : Measure (Mx D r S.rank))
    (𝓕 : Set (Mx D r S.rank)) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (om0 : GA D S × GA D T0 →* Module.End ℂ (WO S T0 → ℂ)) : Prop :=
  ∀ g h0 h, IsLeviEmb T C C' T0 B0 h0 h → ∀ f, IsThetaFunO ψ S T f →
    desc ψ S T C μ 𝓕 T0 B0 (om (g, h) f) = om0 (g, h0) (desc ψ S T C μ 𝓕 T0 B0 f)

def hv (T : HSp D) (x y : Fin T.rank → AE D) : AE D :=
  ∑ i, ∑ j, cA D (x i) * incA D (T.gram i j) * y j

end Formalism.IndefR.Mi

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Datum

namespace Formalism.IndefR.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def frame0 (i : ℕ) : Fin (D.sp.Y 0).rank → D.host.E :=
  if h : i < D.R.rS then (D.sp.Y 0).frame.repr (D.sp.hypE ⟨i, h⟩)
  else if i = D.R.rS then (D.sp.Y 0).frame.repr D.sp.zm
  else if h' : 2 * D.R.rS - i < D.R.rS then
    (D.sp.Y 0).frame.repr ((-(D.sp.T : D.host.E)) • D.sp.hypF ⟨2 * D.R.rS - i, h'⟩)
  else 0


open Classical in
def NormalFrame0 (βY0 : GL (Fin (D.sp.Y 0).rank) (EAf D)) (S Pg : Finset (Pl D.host.E)) : Prop :=
  ∀ PP ∈ S, ∀ ei : AE D, Formalism.L2.NTheta.IsIdemAt ei PP →
    (∀ i < D.R.m - 1, ∀ col : Fin (D.sp.Y 0).rank, col.val = D.R.N 0 + i →
      ColAt 0 βY0.val ei col fun r =>
        (if PP ∈ Pg then ((Ideal.absNorm PP.asIdeal : ℕ) : D.host.E) ^ (i + 1) else 1) * frame0 i r) ∧
    (∀ col : Fin (D.sp.Y 0).rank, col.val < D.R.N 0 → XSpanAt 0 βY0.val ei col)

def VertexAt (j : ℕ) (βY0 : GL (Fin (D.sp.Y 0).rank) (EAf D)) (βW : GL (Fin (D.sp.W j).rank) (EAf D))
    (e : Fin (D.sp.Y 0).rank ≃ Fin (D.sp.W j).rank)
    (ι : GL (Fin (D.sp.W j).rank) (EAf D)) (Pg : Finset (Pl D.host.E)) : Prop :=
  (∀ k, (e k).val = k.val) ∧
  Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) ι.val *
            (((D.sp.Y 0).gram.reindex e e).map (Formalism.UG.inclE (Formalism.L2.Herm.Af D.host.F))) *
            ι.val =
    (D.sp.W j).gram.map (Formalism.UG.inclE (Formalism.L2.Herm.Af D.host.F)) ∧
  ∀ PP ∈ Pg, ∀ ei : AE D, Formalism.L2.NTheta.IsIdemAt ei PP →
    IsIntM (toEAf D ei • ((βY0⁻¹ : GL (Fin (D.sp.Y 0).rank) (EAf D)).val.reindex e e * ι.val * βW.val)) ∧
      redM PP (toEAf D ei • ((βY0⁻¹ : GL (Fin (D.sp.Y 0).rank) (EAf D)).val.reindex e e * ι.val * βW.val)) = 1

end Formalism.IndefR.Mi

end
end
