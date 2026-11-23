module

public import Formalism.LocalToGlobal.Divisibility.Bundle003
public import Formalism.LocalToGlobal.IndefiniteForms.PairingConditionOfInverseMatrixIdentity
public import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
public import Formalism.LocalToGlobal.Divisibility.RowLatLemmas
public import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
public import Formalism.LocalToGlobal.Divisibility.FramesLemmas
public import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}

def faceOf3 (A3 : FamIn3 K G Pl0 I0 Ty T m) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) : DefSub A3.fam3.amb3 → DefFace A3.fam3.base3 :=
  fun Zs => ⟨A3.side3 P0 ψ0 Zs, A3.side3 P1 ψ1 Zs, Dc Zs, Sp Zs, Zsc Zs⟩

def crdOf3 (A3 : FamIn3 K G Pl0 I0 Ty T m) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) : Crd A3.fam3.amb3 (faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) where
  toR Zs b t := match b with
    | false => (A3.A.fam.R t).toF (A3.A.fam.lvl P0 ψ0) (Zs.Z t)
    | true => (A3.A.fam.R t).toF (A3.A.fam.lvl P1 ψ1) (Zs.Z t)
  toL Zs b j t := match b with
    | false => (A3.A.fam.L j t).toF (A3.A.fam.lvlA P0 ψ0) (Zs.Zl j t)
    | true => (A3.A.fam.L j t).toF (A3.A.fam.lvlA P1 ψ1) (Zs.Zl j t)

end Formalism.IndefR.Cx
end
end

section

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K] [StarRing K]

namespace CxData

variable {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A) {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (b : Bool)

structure RowHyp : Prop where

  wf : (lv (fc X.zs) b).WF

  h4pos : X.H4pos

  h2 : X.H2 cr b

  ratMu : X.RATmu cr b

  h3 : X.H3 cr b

  h4 : X.H4 cr b

  partsOrth : X.PartsOrth b (fc := fc)

structure LiftHyp : Prop where

  h5 : X.H5 cr b

  ratTh : X.RATth cr b

  kForm : X.KForm b

  ewNorm : X.EWnorm b

  thmA : X.ThmA cr b

  galD : X.GalD cr b

  h3W : X.H3W cr b

  mLat : X.MLat b

theorem XE_specR (hR : RowHyp X cr b) :
    (∀ v, IsUnit (X.XE cr b v).det) ∧ X.XE cr b Bs.v0 = frameOf (X.gramE cr b) :=
  let h := rowXE_spec (Df := lv (fc X.zs) b) hR.wf _ (X.gramE_unit cr b (hR.h2) (hR.h4pos.2.2 b)) X.κ hR.h4pos.1
    (fun j p v => X.lam j Bs.μ0 p v) (fun j p v => hR.h4pos.2.1 j Bs.μ0 p v)
  ⟨h.1, h.2.1⟩

theorem scal_rowsR (hR : RowHyp X cr b) (t : Bs.Tup) (v : InfinitePlace K)
    (htv : t = Bs.μ0 ∨ v = Bs.v0) (p : Bs.Ix) :
    IsScalarOn ((lv (fc X.zs) b).XQ t) (X.data cr b).XE v ((X.data cr b).ι t) ((X.data cr b).Qpart t p)
      ((X.data cr b).κ v * ∏ j, (X.data cr b).lam j t p v) := by
  intro x hx y
  have hx' : X.iC cr b t (cpt Bs.v0.embedding x) ∈ X.EEp p := by
    have h : (X.rowMat cr b t).mulVec x ∈ X.Ep cr b p := hx
    rwa [mem_Ep, key_row X cr b (hR.h2) (hR.ratMu)] at h
  by_cases hv : v = Bs.v0
  · subst hv
    change Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin ((lv (fc X.zs) b).dQ Bs.μ0))) (X.XE cr b) Bs.v0 ((X.rowMat cr b t).mulVec x) ((X.rowMat cr b t).mulVec y) = _
    rw [majAt_gram_smul (X.XE cr b) Bs.v0 (fun i => X.iC cr b Bs.μ0 (Pi.single i 1))
      (li_of_lin_injective (by rw [lin_basis]; exact (hR.h2).1)) _ (inv_pos.mpr (hR.h4pos.2.2 b))
      (X.XE_specR cr b hR).2, lin_basis,
      key_row X cr b (hR.h2) (hR.ratMu), key_row X cr b (hR.h2) (hR.ratMu), (hR.h4) t p x hx' y]
    have hn : (X.nP b : ℂ) ≠ 0 := by exact_mod_cast (hR.h4pos.2.2 b).ne'
    push_cast
    field_simp
    dsimp only [CxData.data]
    ring
  · rcases htv with rfl | h
    · change Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin ((lv (fc X.zs) b).dQ Bs.μ0))) (X.XE cr b) v ((X.rowMat cr b Bs.μ0).mulVec x) ((X.rowMat cr b Bs.μ0).mulVec y) = _
      rw [X.rowMat_base cr b (hR.h2), Matrix.one_mulVec, Matrix.one_mulVec]
      have hxQ : x ∈ (lv (fc X.zs) b).Qp Bs.μ0 p := ((hR.h3) p x).2 hx'
      exact rowXE_part (lv (fc X.zs) b) hR.wf _ (X.gramE_unit cr b (hR.h2) (hR.h4pos.2.2 b)) X.κ hR.h4pos.1
        (fun j p v => X.lam j Bs.μ0 p v) (fun j p v => hR.h4pos.2.1 j Bs.μ0 p v) v hv
        (fun p q hpq x hx y hy => (hR.partsOrth) v hv p q hpq x hx y hy) p x hxQ y
    · exact absurd h hv

theorem scal_liftsR (hR : RowHyp X cr b) (hF : LiftHyp X cr b) (j : Bs.J) (t : Bs.Tup) (v : InfinitePlace K)
    (htv : t = Bs.μ0 ∨ v = Bs.v0) (p : Bs.Ix) :
    IsScalarOn ((lv (fc X.zs) b).XT j t) ((X.data cr b).XW j) v ((X.data cr b).θ j t) ((X.data cr b).Zpart j t p)
      ((X.data cr b).lam j t p v) := by
  intro x hx y
  have hx' : X.tC cr b j t (cpt Bs.v0.embedding x) ∈ X.Wp j p := by
    have h : (X.liftMat cr b j t).mulVec x ∈ X.WpK b j p := hx
    rwa [mem_WpK, key_lift X cr b (hF.h5) (hF.ratTh)] at h
  change Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin (X.dW b j))) (X.XW b j) v ((X.liftMat cr b j t).mulVec x) ((X.liftMat cr b j t).mulVec y) = _
  rw [majAt_gram (X.XW b j) v (X.bW b j v) ((hF.kForm) j v).1 rfl]
  by_cases hv : v = Bs.v0
  · subst hv
    have hn : ((X.nP b : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hR.h4pos.2.2 b).ne'
    have he := (hF.ewNorm) j (X.wC b j Bs.v0 (cpt Bs.v0.embedding ((X.liftMat cr b j t).mulVec x)))
      (X.wC b j Bs.v0 (cpt Bs.v0.embedding ((X.liftMat cr b j t).mulVec y)))
    change ⟪X.w0C b j (cpt Bs.v0.embedding ((X.liftMat cr b j t).mulVec x)),
      X.w0C b j (cpt Bs.v0.embedding ((X.liftMat cr b j t).mulVec y))⟫_ℂ = _ at he
    rw [key_lift X cr b (hF.h5) (hF.ratTh), key_lift X cr b (hF.h5) (hF.ratTh),
      (hF.thmA) j t p x hx' y] at he
    change ⟪X.wC b j Bs.v0 (cpt Bs.v0.embedding ((X.liftMat cr b j t).mulVec x)),
      X.wC b j Bs.v0 (cpt Bs.v0.embedding ((X.liftMat cr b j t).mulVec y))⟫_ℂ = _
    apply mul_left_cancel₀ hn
    rw [← he]
    dsimp only [CxData.data]
    push_cast
    ring
  · rcases htv with rfl | h
    · exact (hF.galD) j v hv p x hx' y
    · exact absurd h hv

def rowsOfR (hR : RowHyp X cr b) (hF : LiftHyp X cr b) (hpos : (lv (fc X.zs) b).Pos) (hprov : (lv (fc X.zs) b).Proviso)
    (htypes : (lv (fc X.zs) b).Types) (hh0 : X.H0) (hl1d : (X.data cr b).DimensionsOfPartsAgree) : IndefRows (lv (fc X.zs) b) where
  toIndefData := X.data cr b
  pos := hpos
  proviso := hprov
  types := htypes
  h0 := hh0
  frames := ⟨(X.XE_specR cr b hR).1, fun j v => frame_gram_unit _ ((hF.kForm) j v).1, hF.mLat⟩
  l1a := by
    refine ⟨fun p => ?_, fun j p => ?_⟩
    · change ((lv (fc X.zs) b).Qp Bs.μ0 p).map (X.rowMat cr b Bs.μ0).mulVecLin = X.Ep cr b p
      rw [X.rowMat_base cr b (hR.h2), Matrix.mulVecLin_one, Submodule.map_id]
      ext x
      rw [mem_Ep]
      exact (hR.h3) p x
    · change ((lv (fc X.zs) b).Zp j Bs.μ0 p).map (X.liftMat cr b j Bs.μ0).mulVecLin = X.WpK b j p
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        rw [Matrix.mulVecLin_apply, mem_WpK, key_lift X cr b (hF.h5) (hF.ratTh)]
        exact ((hF.h3W) j p x).1 hx
      · intro hy
        obtain ⟨x, rfl⟩ := (X.liftMat_bij cr b (hF.kForm) (hF.ewNorm) (hR.h4pos.2.2 b) (hF.h5) (hF.ratTh) j Bs.μ0).2 y
        refine ⟨x, ?_, rfl⟩
        rw [mem_WpK, key_lift X cr b (hF.h5) (hF.ratTh)] at hy
        exact ((hF.h3W) j p x).2 hy
  l1c := ⟨fun t => X.rowMat_bij cr b (hR.h2) (hR.ratMu) t,
    fun j t => X.liftMat_bij cr b (hF.kForm) (hF.ewNorm) (hR.h4pos.2.2 b) (hF.h5) (hF.ratTh) j t, hR.h4pos.1,
    fun j t p v => hR.h4pos.2.1 j t p v, fun t v htv p => X.scal_rowsR cr b hR t v htv p,
    fun j t v htv p => X.scal_liftsR cr b hR hF j t v htv p⟩
  l1d := hl1d

def colsOfR (hR : RowHyp X cr true) (hpos : (lv (fc X.zs) true).Pos) (hh0 : X.H0) (Y : CxCol (fc := fc) X)
    (N : IndefNum Bs) (hl6 : (X.data cr true).L6 N) (hl1b : (X.colOf cr Y).PairingFactorsThroughPeriods) (hl1e : (X.colOf cr Y).L1e) :
    IndefColsR (lv (fc X.zs) true) (fc X.zs).Dc (fc X.zs).Sp N where
  toIndefData := X.data cr true
  pos := hpos
  h0 := hh0
  frames := (X.XE_specR cr true hR).1
  l1a := fun p => by
    change ((lv (fc X.zs) true).Qp Bs.μ0 p).map (X.rowMat cr true Bs.μ0).mulVecLin = X.Ep cr true p
    rw [X.rowMat_base cr true hR.h2, Matrix.mulVecLin_one, Submodule.map_id]
    ext x
    rw [mem_Ep]
    exact hR.h3 p x
  l1c := ⟨fun t => X.rowMat_bij cr true hR.h2 hR.ratMu t, hR.h4pos.1, fun j t p v => hR.h4pos.2.1 j t p v,
    fun t v htv p => X.scal_rowsR cr true hR t v htv p⟩
  l6 := hl6
  col := X.colOf cr Y
  l1b := hl1b
  l1e := hl1e

def cxPkgR (cf : ConvFace Bs) (Y : CxCol (fc := fc) X) (C CH : ℝ) (hst : X.zs.Stable) (hin : X.zs.InBlock)
    (hR0 : X.RowHyp cr false) (hF0 : X.LiftHyp cr false) (hpos : ∀ b, (lv (fc X.zs) b).Pos)
    (hprov : (lv (fc X.zs) false).Proviso) (htypes : (lv (fc X.zs) false).Types) (hh0 : X.H0)
    (hl1d : (X.data cr false).DimensionsOfPartsAgree) (hl3 : (X.data cr false).L3 ((fc X.zs).Z.num C CH))
    (hon : (X.data cr false).ON ((fc X.zs).Z.num C CH)) (hR1 : X.RowHyp cr true)
    (hl6 : (X.data cr true).L6 ((fc X.zs).Z.num C CH)) (hl1b : (X.colOf cr Y).PairingFactorsThroughPeriods) (hl1e : (X.colOf cr Y).L1e)
    (huntw : (X.data cr false).Untwisted ((fc X.zs).Z.num C CH))
    (hpass : Passage ((fc X.zs).Z.num C CH) (X.data cr false) (X.data cr true))
    (hfun0 : (X.data cr false).FUN ((fc X.zs).Z.num C CH)) (hconv : IndefConv Bs X.μ cf)
    (hB : HeckeAll cf (X.data cr false)) (hCc : HeckeRows cf (X.data cr true)) : IndefPkgR A fc cf C CH where
  Zs := X.zs
  stable := hst
  inBlock := hin
  core :=
    { base := { toIndefRows := X.rowsOfR cr false hR0 hF0 (hpos false) hprov htypes hh0 hl1d, l3 := hl3, on := hon }
      cols := X.colsOfR cr hR1 (hpos true) hh0 Y _ hl6 hl1b hl1e
      extra := { untw := huntw, level := ⟨rfl, rfl, rfl⟩, passage := hpass, fun0 := hfun0 } }
  conv := hconv
  heckeB := hB
  heckeC := hCc

end CxData

end Formalism.IndefR.Cx
end
end

section

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem eq_zero_of_mem_range_adjoint {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] (T : E →ₗ[ℂ] F) {w : E}
    (hw : w ∈ LinearMap.range (LinearMap.adjoint T)) (h : T w = 0) : w = 0 := by
  obtain ⟨z, rfl⟩ := hw
  have : ⟪LinearMap.adjoint T z, LinearMap.adjoint T z⟫_ℂ = 0 := by
    rw [LinearMap.adjoint_inner_left, h, inner_zero_right]
  exact inner_self_eq_zero.1 this

namespace CxData

variable {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A) {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (b : Bool)

def uQ (t : Bs.Tup) : Fin ((lv (fc X.zs) b).dQ t) → X.FC t :=
  fun k => X.jR t (cr.toR X.zs b t (Pi.single k 1))

theorem iC_eq_comp (t : Bs.Tup) (c : Fin ((lv (fc X.zs) b).dQ t) → ℂ) :
    X.iC cr b t c = X.Θ t (lin (X.uQ cr b t) c) := by

  simp only [iC, uQ, lin_apply, map_sum, map_smul]

theorem lin_uQ_cpt (t : Bs.Tup) (x : Fin ((lv (fc X.zs) b).dQ t) → K) :
    lin (X.uQ cr b t) (cpt Bs.v0.embedding x) = X.jR t (cr.toR X.zs b t x) := by
  have hx : x = ∑ k, x k • (Pi.single k 1 : Fin ((lv (fc X.zs) b).dQ t) → K) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hx]

  simp only [map_sum, map_smul, LinearMap.map_smulₛₗ, lin_apply, uQ, cpt]

theorem gram_uQ (hIso : X.IsoR cr b) (t : Bs.Tup) :
    Matrix.gram ℂ (X.uQ cr b t) = ((X.nP b : ℝ) : ℂ) • metOf ((lv (fc X.zs) b).XQ t Bs.v0) := by
  have hs : ∀ i, (fun j => Bs.v0.embedding ((Pi.single i (1 : K) : Fin ((lv (fc X.zs) b).dQ t) → K) j)) =
      (Pi.single i 1 : Fin ((lv (fc X.zs) b).dQ t) → ℂ) := by
    intro i; funext j; by_cases h : j = i <;> simp [h]
  ext i k
  rw [Matrix.gram_apply, uQ, uQ, hIso t, Formalism.L2.DIV.majAt_eq, hs, hs, Matrix.smul_apply, smul_eq_mul]
  congr 1
  simp [Matrix.mulVec_single, dotProduct, Pi.single_apply]

theorem lin_uQ_injective (hW : (lv (fc X.zs) b).WF) (hn : 0 < X.nP b) (hIso : X.IsoR cr b) (t : Bs.Tup) :
    Function.Injective (lin (X.uQ cr b t)) := by
  refine lin_injective (Matrix.linearIndependent_of_posDef_gram ?_)
  rw [X.gram_uQ cr b hIso t]
  exact (metOfSpec _ _ (hW.XQ_quot t Bs.v0).1).1.smul (Complex.zero_lt_real.mpr hn)

end CxData


open CxData in
theorem cutRows {Bs : DefBase K} {A : DefAmb Bs} {X : CxData A} {fc : DefSub A → DefFace Bs} (cr : Crd A fc)
    (cv : CrdV A) (b : Bool) : X.CutRows cr cv b := by
  intro hW hpos hIso hZ hV0' hRat hDn hUp hB hParts
  have hV0 : ∀ t x, X.jR t (cr.toR X.zs b t x) ∈ X.V0C cv b t :=
    fun t x => Submodule.subset_span ⟨_, hV0' t x, rfl⟩
  have hadj : ∀ t c, lin (X.uQ cr b t) c ∈ LinearMap.range (LinearMap.adjoint (X.Θ t)) := by
    intro t c
    rw [lin_apply]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hZ t _)
  have hv0 : ∀ t c, lin (X.uQ cr b t) c ∈ X.V0C cv b t := by
    intro t c
    rw [lin_apply]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hV0 t _)
  have hinj : ∀ t, Function.Injective (X.iC cr b t) := by
    intro t c c' h
    apply X.lin_uQ_injective cr b hW (hpos.2.2 b) hIso t
    rw [← sub_eq_zero, ← map_sub]
    refine eq_zero_of_mem_range_adjoint (X.Θ t) ?_ ?_
    · rw [map_sub]; exact sub_mem (hadj t c) (hadj t c')
    · rw [map_sub, map_sub, ← X.iC_eq_comp cr b, ← X.iC_eq_comp cr b, h, sub_self]
  have hrange : ∀ t, LinearMap.range (X.iC cr b t) = X.EEl b := by
    intro t
    apply le_antisymm
    · rintro _ ⟨c, rfl⟩
      rw [X.iC_eq_comp cr b]
      exact hDn t ⟨_, hv0 t c, rfl⟩
    · rw [← hParts.2]
      refine iSup_le fun p => ?_
      intro e he
      have hc : (0 : ℝ) < X.κ Bs.v0 * ∏ j, X.lam j t p Bs.v0 :=
        mul_pos (hpos.1 _) (Finset.prod_pos fun j _ => hpos.2.1 j t p Bs.v0)
      have h1 : LinearMap.adjoint (X.Θ t) e ∈ LinearMap.range (LinearMap.adjoint (X.Θ t)) ⊓ X.V0C cv b t :=
        ⟨⟨e, rfl⟩, hUp t ⟨e, he.2, rfl⟩⟩
      rw [← hRat t] at h1
      have h2 : Submodule.span ℂ (Set.range fun x : Fin ((lv (fc X.zs) b).dQ t) → K => X.jR t (cr.toR X.zs b t x)) ≤
          LinearMap.range (lin (X.uQ cr b t)) := by
        rw [Submodule.span_le]
        rintro _ ⟨x, rfl⟩
        exact ⟨cpt Bs.v0.embedding x, X.lin_uQ_cpt cr b t x⟩
      obtain ⟨c', hc'⟩ := h2 h1
      refine ⟨(((X.κ Bs.v0 * ∏ j, X.lam j t p Bs.v0 : ℝ) : ℂ))⁻¹ • c', ?_⟩
      have hc0 : (((X.κ Bs.v0 * ∏ j, X.lam j t p Bs.v0 : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast hc.ne'
      rw [X.iC_eq_comp cr b, map_smul, map_smul, hc', hB t p e he, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  refine ⟨⟨hinj Bs.μ0, fun t => ⟨hinj t, by rw [hrange, hrange]⟩, hrange Bs.μ0⟩, ?_⟩
  intro t p x hx y
  rw [X.iC_eq_comp cr b, X.lin_uQ_cpt cr b] at hx ⊢
  rw [X.iC_eq_comp cr b, X.lin_uQ_cpt cr b]
  have hEl : X.Θ t (X.jR t (cr.toR X.zs b t x)) ∈ X.EEl b := hDn t ⟨_, hV0 t x, rfl⟩
  have hBB := hB t p _ ⟨hx, hEl⟩
  have hw : LinearMap.adjoint (X.Θ t) (X.Θ t (X.jR t (cr.toR X.zs b t x))) =
      (((X.κ Bs.v0 * ∏ j, X.lam j t p Bs.v0 : ℝ) : ℂ)) • X.jR t (cr.toR X.zs b t x) := by
    rw [← sub_eq_zero]
    refine eq_zero_of_mem_range_adjoint (X.Θ t) (sub_mem ⟨_, rfl⟩ (Submodule.smul_mem _ _ (hZ t x))) ?_
    rw [map_sub, map_smul, hBB, sub_self]
  rw [← LinearMap.adjoint_inner_left, hw, inner_smul_left, hIso t x y, Complex.conj_ofReal]
  push_cast
  ring

end Formalism.IndefR.Cx
end
end

section

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx.PrincipalLevelLattice

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A) {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (b : Bool)

def principalHermitianLattice : Formalism.BasicNotions.HLat K := toHLat (X.XE cr b) (X.data cr b).RR

def jEEx (σ : K →+* ℂ) : (Fin ((lv (fc X.zs) b).dQ Bs.μ0) → K) →ₛₗ[σ] X.EE :=
  (X.iC cr b Bs.μ0).comp (cptL σ _)

variable {X b} {c : ℂ →+* ℂ} {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable (X b)

theorem frame_at_base_place_eq_gram : (X.XE cr b) Bs.v0 = frameOf (X.gramE cr b) := by
  show rowXE _ _ _ _ Bs.v0 = _
  simp [rowXE, rowFrame, spliceFrame]

theorem frames (hW : (lv (fc X.zs) b).WF) (h2 : X.H2 cr b) (hp : X.H4pos) :
    ∀ v, IsUnit ((principalHermitianLattice X cr b).X v).det :=
  (rowXE_spec (Df := lv (fc X.zs) b) hW _ (X.gramE_unit cr b h2 (hp.2.2 b)) X.κ hp.1
    (fun j p v => X.lam j Bs.μ0 p v) (fun j p v => hp.2.1 j Bs.μ0 p v)).1

theorem majorant_at_base_place_eq_inner (h2 : X.H2 cr b) (hn : 0 < X.nP b) (x y : Fin ((lv (fc X.zs) b).dQ Bs.μ0) → K) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) (X.XE cr b) Bs.v0 x y =
      (((X.nP b)⁻¹ : ℝ) : ℂ) * ⟪jEEx X cr b Bs.v0.embedding x, jEEx X cr b Bs.v0.embedding y⟫_ℂ := by
  have hli : LinearIndependent ℂ (fun i => X.iC cr b Bs.μ0 (Pi.single i 1)) :=
    li_of_lin_injective (by rw [lin_basis]; exact h2.1)
  rw [majAt_gram_smul (X.XE cr b) Bs.v0 _ hli _ (inv_pos.mpr hn) (frame_at_base_place_eq_gram X cr b), lin_basis]
  rfl

end Formalism.IndefR.Cx.PrincipalLevelLattice

end
end
