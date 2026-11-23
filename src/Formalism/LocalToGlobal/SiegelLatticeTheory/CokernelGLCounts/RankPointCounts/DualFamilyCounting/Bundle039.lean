module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle010
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle020
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.SpectralTiesReal
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle011
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle014
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Assemble
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle023
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle023
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle035
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.AdmNPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle025
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HermitianZZEqNeg
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ProductExactness
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle031
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle005
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle038
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.MeasurablePinv
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibAlg
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle033
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcValVolOrdA
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcValVolOrdTr
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle037
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.HermitianLattices.Ext.L3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def OrbitFiniteR : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (_L : LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ → ∀ Z : MatZ D, ∀ Λ ∈ what₂, cntE (Tn u') F0 Λ Z ≠ ⊤

def RowLatExists : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (T : Formalism.L2.SG.SpectralTiesReal.STies D) (u : D.what₂.Word), ∃ Λ, IsRowLat D (T.X.Fu u) Λ

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem cExpl_pos' (D : Formalism.BasicNotions.D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (hR : IsRowReps D F0 what₂) (hne : what₂.Nonempty) :
    0 < cExpl D F0 what₂ := by
  obtain ⟨hK, hF, -⟩ := field_dictionary_holds D
  have hk : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
  have hc := (Formalism.L2.SG.Pf.Asm.cMass_spec hK hF (D.R.k - 1) (by omega)).1
  have hd : 0 < |(NumberField.discr D.host.F : ℝ)| ^
      (-((2 * D.R.rS * (D.R.rS + 1) * (D.R.k - 1) : ℕ) : ℤ)) := by
    apply zpow_pos
    exact abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero D.host.F)
  have hL : 0 < ∏ i ∈ Finset.Icc D.R.k D.R.r, lValEtaF D.host.E D.host.F i := by
    apply Finset.prod_pos
    intro i hi
    have hi2 : 2 ≤ i := by simp only [Finset.mem_Icc] at hi; omega
    rw [← lValEta_eq_lValEtaF hK hF i hi2]
    exact lValEta_pos hK i hi2
  have hA : Formalism.L2.SG.PairVal.AutFin D F0 what₂ := by
    intro Λ hΛ
    exact _root_.automorphism_lattice_finite D (D.sp.Y_sig 0) (D.mem u).A.T (D.mem u).A.T_prime.pos F0 Λ (hR.1 Λ hΛ)
  have hm := Formalism.L2.SG.PairVal.massRows_pos D F0 what₂ hA hne
  unfold cExpl
  positivity


end Formalism.L2.SG.Pf.Cnt
end
end

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.Pf.NcReal.JX Formalism.L2.SG.TermOp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Pl

variable {D : D7} (X : HidaSetting D)

theorem umat_rv {x : X.B.I.GA} {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hRL : RatLink X x n) (v : InfinitePlace X.B.I.F)
    (y : (VS D).V) : uMat (x.1 v) *ᵥ rv X.B.I v (X.crd y) = rv X.B.I v (X.crd (n y)) := by
  obtain ⟨M, -, hv, -, hcrd⟩ := hRL
  rw [hv v, Formalism.L2.SG.Pf.rv_mulVec, ← hcrd]

theorem inv_map_emb {m : ℕ} {K L : Type*} [Field K] [Field L] (f : K →+* L) (A : Matrix (Fin m) (Fin m) K) :
    (A.map f)⁻¹ = A⁻¹.map f := by
  have h1 : (A.map f).det = f A.det := (f.map_det A).symm
  have h2 : (A.map f).adjugate = A.adjugate.map f := (f.map_adjugate A).symm
  rw [Matrix.inv_def, Matrix.inv_def, h1, h2, Ring.inverse_eq_inv', Ring.inverse_eq_inv', ← map_inv₀]
  ext i j
  simp [Matrix.smul_apply]

theorem hJ_span_ef (v : InfinitePlace X.B.I.F) (α β : Fin D.R.rS → D.host.E) (w : Fin X.B.I.n → ℂ)
    (he : ∀ c, hJ (X.B.I.ε v) (rv X.B.I v (X.crd (X.eX c))) w = 0)
    (hf : ∀ c, hJ (X.B.I.ε v) (rv X.B.I v (X.crd (X.fY c))) w = 0) :
    hJ (X.B.I.ε v) (rv X.B.I v (X.crd (∑ c, α c • X.eX c + ∑ c, β c • X.fY c))) w = 0 := by
  rw [Formalism.L2.SG.NormCut.crd_add', Formalism.L2.SG.NormCut.crd_sum', Formalism.L2.SG.NormCut.crd_sum']
  simp only [Formalism.L2.SG.NormCut.crd_smul']
  have rv_add (a b : Fin X.B.I.n → X.B.I.E) : rv X.B.I v (a + b) = rv X.B.I v a + rv X.B.I v b := by
    unfold rv
    rw [← Matrix.mulVec_add]
    congr 1
    ext i
    simp
  rw [rv_add, Formalism.L2.SG.RealObj.RealFramesCharacters.rv_sum, Formalism.L2.SG.RealObj.RealFramesCharacters.rv_sum,
    Formalism.L2.SG.RealObj.InfCut.ProductExactness.hJ_add_l, Formalism.L2.SG.RealObj.HermitianSumRootCoordinateFrames.hJ_sum_left,
    Formalism.L2.SG.RealObj.HermitianSumRootCoordinateFrames.hJ_sum_left]
  simp only [he, hf, mul_zero, Finset.sum_const_zero, add_zero]

end Pl

section Main

theorem dictionary_place_holds : DictPlace := by
  intro D X u x n hRL hNF
  set ψ : InfinitePlace X.B.I.F → D.host.E →+* ℂ := fun v => embS D (X.pl v) with hψ
  have hxM : ∀ v, LsNc5.xMat X v x.1 = (Xq X n).map (ψ v) := fun v => by
    ext b a
    simp only [LsNc5.xMat, LsNc5.fV, LsNc5.eV, Matrix.map_apply]
    rw [show X.eR a = X.crd (X.eX a) from rfl, umat_rv X hRL v, show X.fR b = X.crd (X.fY b) from rfl,
      Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.hJ_rvX]
    rfl
  have haM : ∀ v, LsNc5.aMat X v x.1 = (Aq X n).map (ψ v) := fun v => by
    ext b a
    simp only [LsNc5.aMat, LsNc5.fV, Matrix.map_apply]
    rw [show X.fR a = X.crd (X.fY a) from rfl, umat_rv X hRL v, show X.fR b = X.crd (X.fY b) from rfl,
      Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.hJ_rvX]
    rfl
  have hmM : ∀ v, LsNc5.mMat X v x.1 = (Mq X n).map (ψ v) := fun v => by
    unfold LsNc5.mMat Mq
    rw [hxM, haM, inv_map_emb, Matrix.map_mul]

  have hrow : ∀ v b (w : Fin X.B.I.n → ℂ), (∀ c, hJ (X.B.I.ε v) (rv X.B.I v (X.crd (X.eX c))) w = 0) →
      (∀ c, hJ (X.B.I.ε v) (rv X.B.I v (X.crd (X.fY c))) w = 0) →
      hJ (X.B.I.ε v) (LsNc5.fV X v b) (uMat (x.1 v) *ᵥ w) = hJ (X.B.I.ε v) (rv X.B.I v (X.crd (xq X n b))) w := by
    intro v b w he hf
    have h1 := Formalism.L2.SG.RealObj.InfCut.RealHermitianForms.hJ_inv_r (X.B.I.ε v) (x.1 v)⁻¹ (LsNc5.fV X v b) w
    rw [inv_inv] at h1
    rw [h1]
    have h2 : uMat (x.1 v)⁻¹ *ᵥ LsNc5.fV X v b = rv X.B.I v (X.crd (n.symm (X.fY b))) :=
      umat_rv X (Formalism.L2.SG.TermOp.Vanish.ratLink_inv X hRL) v (X.fY b)
    rw [h2]
    have hy : n.symm (X.fY b) = xq X n b + (∑ c, (VS D).hT (X.fY c) (n.symm (X.fY b)) • X.eX c +
        ∑ c, (VS D).hT (X.eX c) (n.symm (X.fY b)) • X.fY c) := by
      simp only [xq, pW]; abel
    have rv_add (a b : Fin X.B.I.n → X.B.I.E) : rv X.B.I v (a + b) = rv X.B.I v a + rv X.B.I v b := by
      unfold rv
      rw [← Matrix.mulVec_add]
      congr 1
      ext i
      simp
    rw [hy, Formalism.L2.SG.NormCut.crd_add', rv_add, Formalism.L2.SG.RealObj.InfCut.ProductExactness.hJ_add_l,
      hJ_span_ef X v _ _ w he hf, add_zero]
  funext p
  rcases p with ((p | b) | (p | a))
  · funext v
    show LsNc5.xMat X v x.1 p.1.1 p.1.2 = embS D (X.pl v) (Xq X n p.1.1 p.1.2)
    rw [hxM]; rfl
  · funext v j
    show (if h : j.val < D.R.k then LsNc5.phiMat X u v x.1 b ⟨j.val, h⟩ else LsNc5.yVec X u v x.1 b) =
      rowV X u (xq X n b) v j
    unfold rowV
    split_ifs with h
    · exact hrow v b _ (fun c => ((X.wfr_perp u v ⟨j.val, h⟩).1 c).1) (fun c => ((X.wfr_perp u v ⟨j.val, h⟩).1 c).2)
    · refine hrow v b _ (fun c => ?_) (fun c => ?_)
      · show hJ (X.B.I.ε v) (rv X.B.I v (X.crd (X.eX c))) (rv X.B.I v (X.crd (X.zu u))) = 0
        rw [Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.hJ_rvX, (X.zu_orth u c).1, map_zero]
      · show hJ (X.B.I.ε v) (rv X.B.I v (X.crd (X.fY c))) (rv X.B.I v (X.crd (X.zu u))) = 0
        rw [Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.hJ_rvX, (X.zu_orth u c).2, map_zero]
  · funext v
    show (LsNc5.mMat X v x.1 p.1.1 p.1.2 - star (LsNc5.mMat X v x.1 p.1.2 p.1.1)) / 2 =
      (embS D (X.pl v) (Mq X n p.1.1 p.1.2) - star (embS D (X.pl v) (Mq X n p.1.2 p.1.1))) / 2
    rw [hmM]; rfl
  · funext v
    show (LsNc5.mMat X v x.1 a a).im = (embS D (X.pl v) (Mq X n a a)).im
    rw [hmM]; rfl

end Main

end Formalism.L2.SG.Pf.NcReal.JX.NOf
end
end

section

noncomputable section

open NumberField Formalism.BasicNotions Matrix
open scoped BigOperators

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf.Ex

open Formalism.L2.SG.HidaSetting Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX.NOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (xs : Fin D.R.rS → (VS D).V)
  (M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)

def Ym : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E := (X0⁻¹)ᴴ

def om (a : Fin D.R.rS) : (VS D).V := -∑ b, Ym X0 b a • xs b

def nE (a : Fin D.R.rS) : (VS D).V := ∑ b, X0 b a • X.eX b

def nF (a : Fin D.R.rS) : (VS D).V := ∑ c, Ym X0 c a • X.fY c + om X0 xs a + ∑ b, (X0 * M) b a • X.eX b

def nWL : (VS D).V →ₗ[D.host.E] (VS D).V := LinearMap.id + ∑ b, ((VS D).hT (xs b)).smulRight (X.eX b)

def pWL : (VS D).V →ₗ[D.host.E] (VS D).V :=
  LinearMap.id - ∑ c, ((VS D).hT (X.fY c)).smulRight (X.eX c) - ∑ c, ((VS D).hT (X.eX c)).smulRight (X.fY c)

theorem pWL_apply (y : (VS D).V) : pWL X y = pW X y := by
  simp [pWL, pW, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smulRight_apply]

def nL : (VS D).V →ₗ[D.host.E] (VS D).V :=
  ∑ c, ((VS D).hT (X.fY c)).smulRight (nE X X0 c) + ∑ c, ((VS D).hT (X.eX c)).smulRight (nF X X0 xs M c) +
    (nWL X xs).comp (pWL X)

theorem nL_apply (y : (VS D).V) : nL X X0 xs M y =
    ∑ c, (VS D).hT (X.fY c) y • nE X X0 c + ∑ c, (VS D).hT (X.eX c) y • nF X X0 xs M c +
      (pW X y + ∑ b, (VS D).hT (xs b) (pW X y) • X.eX b) := by
  simp [nL, nWL, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.comp_apply, pWL_apply]

theorem pW_of_inW {w : (VS D).V} (hw : InW X w) : pW X w = w := by
  unfold pW
  simp [(hw _).1, (hw _).2]

theorem pW_e (a : Fin D.R.rS) : pW X (X.eX a) = 0 := by
  unfold pW
  simp [h_fe, X.ee, Finset.sum_ite_eq']

theorem pW_f (a : Fin D.R.rS) : pW X (X.fY a) = 0 := by
  unfold pW
  simp [X.ef, X.ff, Finset.sum_ite_eq']

theorem nL_e (a : Fin D.R.rS) : nL X X0 xs M (X.eX a) = nE X X0 a := by
  rw [nL_apply, pW_e]
  simp [h_fe, X.ee, Finset.sum_ite_eq']

theorem nL_f (a : Fin D.R.rS) : nL X X0 xs M (X.fY a) = nF X X0 xs M a := by
  rw [nL_apply, pW_f]
  simp [X.ef, X.ff, Finset.sum_ite_eq']

theorem nL_w {w : (VS D).V} (hw : InW X w) : nL X X0 xs M w = w + ∑ b, (VS D).hT (xs b) w • X.eX b := by
  rw [nL_apply, pW_of_inW X hw]
  simp [(hw _).1, (hw _).2]

end Formalism.L2.SG.Pf.NcReal.JX.NOf.Ex
end
end

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Onto

theorem mem_closure_image {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B) (H : AddSubgroup A)
    (y : B) : y ∈ AddSubgroup.closure (f '' (H : Set A)) ↔ ∃ t ∈ H, f t = y := by
  rw [← AddSubgroup.coe_map, AddSubgroup.closure_eq, AddSubgroup.mem_map]

variable {D : D7} (X : HidaSetting D)

def embHom : D.host.E →+ (InfinitePlace X.B.I.F → ℂ) where
  toFun := embV X
  map_zero' := by funext v; simp [embV]
  map_add' x y := by funext v; simp [embV]

theorem mem_cl_emb (I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)
    (y : InfinitePlace X.B.I.F → ℂ) :
    y ∈ AddSubgroup.closure (embV X '' (I : Set D.host.E)) ↔ ∃ t ∈ I, embV X t = y := by
  have := mem_closure_image (embHom X) ((I : Submodule (𝓞 D.host.E) D.host.E).toAddSubgroup) y
  exact this

theorem theta_spec (D : D7) : IsIntegral ℤ (theta D) ∧ theta D + D.host.conj (theta D) = 1 := by
  have h := thetaEx_holds D
  unfold theta
  rw [dite_eq_left h]
  exact h.choose_spec

end Onto

end Formalism.L2.SG.Pf.NcReal.JX.NOf
end
end

section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem mem_cl_row (b : Fin D.R.rS) (x : InfinitePlace X.B.I.F → Fin (D.R.k + 1) → ℂ) :
    x ∈ cLat X u (Sum.inl (Sum.inr b)) ↔ ∃ y ∈ aaLb X b, rowV X u y = x := by
  let f : (VS D).V →+ (InfinitePlace X.B.I.F → Fin (D.R.k + 1) → ℂ) :=
    AddMonoidHom.mk' (rowV X u) (fun x y => rowV_add (X := X) (u := u) x y)
  let S : AddSubgroup (VS D).V := (Submodule.span (𝓞 D.host.E)
    {y | ∃ c ∈ (aaD D b : Set D.host.E), ∃ l ∈ X.Lb, y = c • l}).toAddSubgroup
  have hc : cLat X u (Sum.inl (Sum.inr b)) = S.map f := AddSubgroup.closure_eq (S.map f)
  have key : x ∈ cLat X u (Sum.inl (Sum.inr b)) ↔ x ∈ S.map f := by
    rw [hc]; exact Iff.rfl
  exact key.trans AddSubgroup.mem_map

def imSub (a : Fin D.R.rS) : AddSubgroup D.host.E where
  carrier := {t | t ∈ ((aaD D a * aaD D a : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E) ∧
    D.host.conj t = -t}
  add_mem' := fun {s t} hs ht => ⟨Submodule.add_mem _ hs.1 ht.1, by rw [map_add (f := _), hs.2, ht.2, neg_add]⟩
  zero_mem' := ⟨Submodule.zero_mem _, by rw [map_zero, neg_zero]⟩
  neg_mem' := fun {t} ht => ⟨Submodule.neg_mem _ ht.1, by rw [map_neg, ht.2]⟩

def imHom : D.host.E →+ (InfinitePlace X.B.I.F → ℝ) where
  toFun t := fun v => (embS D (X.pl v) t).im
  map_zero' := by funext v; simp
  map_add' s t := by funext v; simp

theorem mem_cl_im (a : Fin D.R.rS) (x : InfinitePlace X.B.I.F → ℝ) :
    x ∈ cLat X u (Sum.inr (Sum.inr a)) ↔
      ∃ t : D.host.E, t ∈ aaD D a * aaD D a ∧ D.host.conj t = -t ∧ (fun v => (embS D (X.pl v) t).im) = x := by
  have hc : cLat X u (Sum.inr (Sum.inr a)) = (imSub a).map (imHom X) :=
    AddSubgroup.closure_eq ((imSub a).map (imHom X))
  have key : x ∈ cLat X u (Sum.inr (Sum.inr a)) ↔ x ∈ (imSub a).map (imHom X) := by
    rw [hc]; exact Iff.rfl
  refine key.trans (AddSubgroup.mem_map.trans ?_)
  constructor
  · rintro ⟨t, ⟨h1, h2⟩, rfl⟩
    exact ⟨t, h1, h2, rfl⟩
  · rintro ⟨t, h1, h2, rfl⟩
    exact ⟨t, ⟨h1, h2⟩, rfl⟩

theorem im_inj {t t' : D.host.E} (ht : D.host.conj t = -t) (ht' : D.host.conj t' = -t')
    (h : ∀ v : InfinitePlace X.B.I.F, (embS D (X.pl v) t).im = (embS D (X.pl v) t').im) : t = t' := by
  obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace X.B.I.F))
  have hs : D.host.conj (t - t') = -(t - t') := by rw [map_sub, ht, ht']; ring
  have h1 := CovB.embS_conj (D := D) (X.pl v) (t - t')
  rw [hs, map_neg] at h1
  have him : (embS D (X.pl v) (t - t')).im = 0 := by rw [map_sub, Complex.sub_im, h v, sub_self]
  have hre : (embS D (X.pl v) (t - t')).re = 0 := by
    have h2 := congrArg Complex.re h1
    simp only [Complex.neg_re, Complex.conj_re] at h2
    linarith
  have h0 : embS D (X.pl v) (t - t') = 0 := Complex.ext hre him
  exact sub_eq_zero.mp ((map_eq_zero_iff _ (RingHom.injective _)).mp h0)

theorem aaLb_inW {b : Fin D.R.rS} {y : (VS D).V} (hy : y ∈ aaLb X b) : InW X y := by
  have hL : ∀ l ∈ X.Lb, InW X l := by
    intro l hl
    have hp := Alg.pW_inW (X := X) l
    have he : pW X l = l := by
      have h1 := Level.prV_Lb (X := X) l hl
      rw [Level.prV_apply] at h1
      simpa only [pW] using h1
    rwa [he] at hp
  simp only [aaLb, SetLike.mem_coe] at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, -, l, hl, rfl⟩ := hx
    intro d
    exact ⟨by rw [map_smul, ((hL l hl) d).1, smul_zero], by rw [map_smul, ((hL l hl) d).2, smul_zero]⟩
  | zero => intro d; exact ⟨map_zero _, map_zero _⟩
  | add x z _ _ hx hz =>
    intro d
    exact ⟨by rw [map_add (f := _), (hx d).1, (hz d).1, add_zero], by rw [map_add (f := _), (hx d).2, (hz d).2, add_zero]⟩
  | smul o x _ hx =>
    intro d
    refine ⟨?_, ?_⟩
    · rw [← algebraMap_smul D.host.E o x, map_smul, (hx d).1, smul_zero]
    · rw [← algebraMap_smul D.host.E o x, map_smul, (hx d).2, smul_zero]

end Formalism.L2.SG.Pf.NcReal.JX.NOf
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sdNormDV_of {D : D7} (X : HidaSetting D) (ψ : AddChar (AF X.B.I.F) ℂ) (hA : AnnX X ψ)
    (hψ : IsCharAF X.B.I.F ψ) (hs : IsStdChar ψ) : SdNormDV X ψ := by
  have c1 : SdFromAnn := SdW.sdFromAnn_holds
  intro v hv ι _
  refine c1 ψ v (dV v) hψ ?_ ?_ (hA hψ hs v) ι
  · exact X.B.I.cm.deg2
  · exact VolOrdW.dV_ne_zero (v := v)

theorem volOrdV_of {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)
    (hC : CondAll) : VolOrdV X u u' ψ := by
  intro hψ hs
  exact volOrd_body X u u' ψ (sdNormDV_of X ψ (annX_of X ψ hC) hψ hs) SdW.boxScaleL_holds

end Formalism.L2.SG.Pf.NcVal
end
end
