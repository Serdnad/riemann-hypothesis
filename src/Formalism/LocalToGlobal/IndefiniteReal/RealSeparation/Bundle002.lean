module

public import Formalism.LocalToGlobal.GlobalTheory.VolumeCarry.VolumeTheoremTwoOfRationalFrames
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AtTauExUniqueHolds
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Eqv MeasureTheory
  IsDedekindDomain NumberField

namespace Formalism.IndefR.Mi



attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {A T : HSp D} {ι : A.V →ₗ[D.host.E] T.V}

theorem frameMat_eq_global : frameMat T A ι = Formalism.L2.GlobalTheoryTheory.VolumeCarry.frameMat D T A ι := by
  ext i j
  simp [frameMat, Formalism.L2.GlobalTheoryTheory.VolumeCarry.frameMat, LinearMap.toMatrix_apply]

def embP' (A T : HSp D) (ι : A.V →ₗ[D.host.E] T.V) : Matrix (Fin A.rank) (Fin T.rank) D.host.E :=
  A.gram⁻¹ * Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat T A ι) * T.gram

theorem perp_of_embP' (hι : HSpace.IsIsomEmb A T ι) :
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat T A ι) * T.gram * (1 - frameMat T A ι * embP' A T ι) = 0 := by
  have hG := Formalism.L2.GlobalTheoryTheory.VolumeCarry.gram_frameMat D T A ι hι
  rw [← frameMat_eq_global] at hG
  have hu : A.gram * A.gram⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (Formalism.IndefR.Eqv.gram_det_ne' D A))
  rw [Matrix.mul_sub, Matrix.mul_one]
  unfold embP'
  rw [sub_eq_zero]
  calc Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat T A ι) * T.gram
      = A.gram * A.gram⁻¹ * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat T A ι) * T.gram) := by
        rw [hu, Matrix.one_mul]
    _ = _ := by rw [hG]; simp only [Matrix.mul_assoc]



theorem mt_of_embRel (hι : HSpace.IsIsomEmb A T ι) {g : GA D T} {h : GA D A} (hr : EmbRel T A ι g h) :
    mt T g = (frameMat T A ι).map (incA D) * mt A h * (embP' A T ι).map (incA D) +
      (1 - (frameMat T A ι * embP' A T ι).map (incA D)) := by
  set F := frameMat T A ι
  set P := embP' A T ι
  set Q : Matrix (Fin T.rank) (Fin T.rank) D.host.E := 1 - F * P with hQ
  have hperp : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) F * T.gram * Q = 0 := perp_of_embP' hι
  have h1 : mt T g * F.map (incA D) = F.map (incA D) * mt A h := hr.1
  have h2 : mt T g * Q.map (incA D) = Q.map (incA D) := by
    ext i k
    have hx : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) F * T.gram).mulVec (fun i => Q i k) = 0 := by
      funext i'
      have := congrFun (congrFun hperp i') k
      rw [Matrix.mul_apply, Matrix.zero_apply] at this
      rw [Pi.zero_apply, Matrix.mulVec, dotProduct]
      exact this
    have := congrFun (hr.2 (fun i => Q i k) hx) i
    rw [Matrix.mulVec, dotProduct] at this
    rw [Matrix.mul_apply, Matrix.map_apply]
    exact this
  have hQmap : Q.map (incA D) = 1 - (F * P).map (incA D) := by
    ext i j
    simp only [hQ, Matrix.map_apply, Matrix.sub_apply, map_sub, Matrix.one_apply]
    split_ifs <;> simp
  have hsplit : (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) = (F * P).map (incA D) + Q.map (incA D) := by
    rw [hQmap, add_sub_cancel]
  calc mt T g = mt T g * 1 := (Matrix.mul_one _).symm
    _ = mt T g * (F.map (incA D) * P.map (incA D)) + mt T g * Q.map (incA D) := by
        rw [hsplit, Matrix.mul_add, Matrix.map_mul]
    _ = _ := by rw [← Matrix.mul_assoc, h1, h2, hQmap]

end Formalism.IndefR.Mi

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta NumberField IsDedekindDomain

namespace Formalism.IndefR.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def liftRes (PP : Formalism.L2.DIV.Pl D.host.E) (x : Formalism.L2.DIV.kP PP) : 𝓞 D.host.E :=
  Function.surjInv Ideal.Quotient.mk_surjective x

def supSum {k : Type} [AddCommMonoid k] {r : ℕ} (x : Matrix (Fin r) (Fin r) k) : k :=
  ∑ i : Fin r, if h : i.1 + 1 < r then x i ⟨i.1 + 1, h⟩ else 0

def psiAt (ψ : AddChar (AF D.host.F) ℂ) (e : AE D) (y : D.host.E) : ℂ :=
  ψ (Algebra.trace (AF D.host.F) (AE D) (e * incA D (D.host.xi0 * y)))

def SignsAtG {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : Formalism.IndefR.Links.RealDat D A Ks) (F : Formalism.IndefR.Links.Face D A) : Prop :=
  ∀ (e : R.Pg → AE D), (∀ PP : R.Pg, Formalism.L2.NTheta.IsIdemAt (e PP) PP.1) → ∀ u : F.P0,
    D.what₂.embLL ((F.ψ0 u : D.what₂.LLˣ) : D.what₂.LL) =
      ∏ PP : R.Pg, psiAt R.ψ (e PP)
        ((((Ideal.absNorm PP.1.asIdeal : ℕ) : D.host.E))⁻¹ *
          ((liftRes PP.1 (supSum (((R.eG (u : G)) PP : GL (Fin D.R.r) (Formalism.L2.DIV.kP PP.1)) :
            Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.L2.DIV.kP PP.1))) : 𝓞 D.host.E) : D.host.E))

end Formalism.IndefR.Mi
end
end
