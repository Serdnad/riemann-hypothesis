module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.Bundle001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.ThetaC
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.CoordLHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.ModularBoundZeroHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.Bundle002
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle006

@[expose] public section

section

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.LocCnt0LWork

theorem locCnt0L_of
    (h1 : Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ∀ r n, ThetaMbe0 M r n false))
    (h2 : Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ∀ r, Mbe0 M r)) :
    Formalism.L2.SG.LocalCountModules.LocCnt0L.LocCnt0L := by
  intro F _ _ _ E _ _ _ _ M hOK r n hmode V _ _ H hn t₁ f₂ f₂' φ φ' hyp hD Z₁ Z₂ e₁ e₂
  have hs : M.split = none := by simpa using hmode
  rw [h1 F E M hOK r n hmode V H hn t₁ f₂ f₂' φ φ' hyp hD Z₁ Z₂ e₁ e₂]
  refine h2 F E M hOK r Z₁ Z₂ ?_ ?_
  · have : Z₁.Z.map M.R.subtype = H.Zhat t₁.f t₁.f' := by
      rw [e₁]; exact zzplusOf_none hs _ _ _
    unfold headDet; rw [this, ← dl_eq_det]; exact hD
  · have : Z₂.Z.map M.R.subtype = H.Zhat f₂ f₂' := by
      rw [e₂]; exact zzplusOf_none hs _ _ _
    unfold headDet; rw [this, ← dl_eq_det]; exact dl_zero_two hyp hD

theorem locCnt0L_of_theta
    (h1 : Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ∀ r n, ThetaMbe0 M r n false)) :
    Formalism.L2.SG.LocalCountModules.LocCnt0L.LocCnt0L :=
  locCnt0L_of h1 (fun _ _ _ _ _ _ _ _ _ M _ r => modularBoundZero_holds M r)

theorem locCnt0L_of_coordL_unramified (h1 : CoordL) (h2 : UnramifiedIsoCountZero) : Formalism.L2.SG.LocalCountModules.LocCnt0L.LocCnt0L :=
  locCnt0L_of_theta (thetaMbe0_L_of h1 h2)

theorem locCnt0L_of_alg (h2 : UnramifiedIsoCountZero) : Formalism.L2.SG.LocalCountModules.LocCnt0L.LocCnt0L :=
  locCnt0L_of_coordL_unramified coordL_holds h2

end Formalism.L2.SG.LocalCountModules.LocCnt0LWork
end
end

section

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

theorem map_inv_of {K L : Type} [CommRing K] [CommRing L] {n : Type} [Fintype n] [DecidableEq n]
    (f : K →+* L) (A : Matrix n n K) (hA : IsUnit A.det) : (A⁻¹).map f = (A.map f)⁻¹ := by
  symm
  apply Matrix.inv_eq_left_inv
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul A hA, Matrix.map_one f f.map_zero f.map_one]

theorem splitFirstProj_conj (x : E) : ph1 g (M.L.cj x) = ph2 g x := by
  change (g.e (M.L.cj x)).1 = (g.e x).2
  rw [g.e_cj]
  rfl

theorem splitFirstProj_algebraMap (a : F) : ph1 g (algebraMap F E a) = a := by
  change (g.e (algebraMap F E a)).1 = a
  rw [AlgEquiv.commutes]
  rfl

def gHat (g : SplitG M.L) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) : Matrix (Ix r) (Ix r) F :=
  Matrix.fromBlocks (Matrix.of fun a b => if a = Fin.last r ∧ b = Fin.last r then -T else 0)
    (Zh.map (ph2 g)) (Zh.map (ph1 g)).transpose
    (Matrix.of fun a b => if a = Fin.last r ∧ b = Fin.last r then -T' else 0)

def pM (r : ℕ) (x : F) : Matrix (Ix r) (Ix r) F := Matrix.fromBlocks 1 (-x • 1) 0 (x • 1)

theorem map_gramG (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) :
    (gramG (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T) (algebraMap F E T')).map
        (ph1 g) = (pM r (g.q : F)⁻¹).transpose * gHat g Zh T T' * pM r (g.q : F)⁻¹ := by
  simp only [gramG, gHat, pM, Matrix.fromBlocks_map, Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_multiply, Matrix.transpose_one, Matrix.transpose_zero, Matrix.transpose_smul,
    Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, Matrix.smul_mul, Matrix.mul_smul,
    add_zero, zero_add]
  congr 1 <;> ext a b <;>
    by_cases h : a = Fin.last r ∧ b = Fin.last r <;>
    simp [cor, h, splitFirstProj_conj, splitFirstProj_algebraMap, map_mul, map_add (f := _), map_neg, map_sub, Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply] <;>
    ring

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
end
end
