module

public import Formalism.SharpRestriction.GlobalSchurBounds.Bundle001
public import Formalism.SizeWindowBrackets.SChain
public import Formalism.SizeWindowBrackets.Bundle002
public import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
public import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
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

namespace Formalism.MainNotions

open Formalism.BasicNotions

section AtRecord

variable {D : D7} (L : SizeData₂ D)

def ThickSetDensity : Prop := L.sc.x ^ (-L.sc.eps) ≤ (D.host.T2.card : ℝ) / D.R.n

variable {L}

def ChBadp_at (X : G.Inst D L) : Prop :=
  ∑ p ∈ largeOrderResiduePrimes L, Real.log p / p * ((badTops X p).card : ℝ) ≤ (D.host.TT.card : ℝ) * L.sc.x ^ (-2 + L.sc.eps)

variable (L)


open Classical in
def cands (K : G.Consts) : Finset ℕ := (Finset.range ⌈L.sc.X'⌉₊).filter (fun p => G.Cand D L K p)

variable {L}


open Classical in
def ChW_at (X : G.Inst D L) (K : G.Consts) : Prop :=
  ∑ p ∈ cands L K, Real.log p / p *
      ((if L.sc.x ^ (-L.sc.eps) < G.Sig X K (G.aL L) (G.bL L) p then 2 else 0) +
        4 * G.Sig X K (G.aL L) (G.bL L) p) ≤ L.sc.x ^ (-9 : ℝ)

end AtRecord

section Family

variable {eps : ℝ} (Fm : FamP eps)

def ThickSetDensityEventually : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ThickSetDensity (Fm.L x i)
def ChosenBadp : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ChBadp_at (Fm.Gx x i)

def ChosenWS : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, x ∈ Fm.Win → ∃ (i0 : Fm.Ix x) (av bv : ℕ → ℤ),
    (∀ t ∈ Fm.TTn x, aWin (Fm.L x i0) (av t) ∧ (Fm.L x i0).sc.b' ≤ (bv t : ℝ) ∧ (bv t : ℝ) ≤ Fm.bTop x) ∧
    (∃ i1 : Fm.Ix x, ∀ t : (Fm.D x i1).host.TT,
        (Fm.L x i1).aT t = av (t : (Fm.D x i1).R.A).val ∧
        (Fm.L x i1).bT t = bv (t : (Fm.D x i1).R.A).val) ∧
    ∀ i : Fm.Ix x, (∀ t : (Fm.D x i).host.TT,
        (Fm.L x i).aT t = av (t : (Fm.D x i).R.A).val ∧
        (Fm.L x i).bT t = bv (t : (Fm.D x i).R.A).val) → ChW_at (Fm.Gx x i) Fm.GK

def Chosen7 (CH C0 C5 c6 : ℝ) : Prop :=
  ThickSetDensityEventually Fm ∧ ChosenTT Fm ∧ ChosenBadp Fm ∧ ChosenWS Fm ∧ ChosenQD Fm C5 ∧ ChosenThin Fm c6 ∧
    ChosenProviso Fm C0 ∧ ChosenCode Fm C0 CH

def WeightVectorSmallSharesSeven (C0 CH : ℝ) : Prop := ∃ C5 c6 : ℝ, 0 < C5 ∧ 0 < c6 ∧ Chosen7 Fm CH C0 C5 c6

end Family

end Formalism.MainNotions

end
end

section

noncomputable section

namespace Formalism.MainNotions

open Formalism.BasicNotions Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost

instance (D : D7) : Nonempty D.what₂.Word := ⟨D.u₀⟩

def hval (φ : Formalism.HC.Frame) (h : φ.A) : ℕ := Formalism.HC.Frame.A.val h

def sgnZ (s : ℤˣ) : ZMod 2 := if s = 1 then 0 else 1

def gcode (φ : Formalism.HC.Frame) (g : φ.GG) : (ZMod 2 × ZMod 2) × ℕ :=
  ((sgnZ g.1.2, sgnZ g.1.1), Formalism.HC.Frame.A.val (φ.iotaInv g.2))

def mcode (φ : Formalism.HC.Frame) (g : E0 × φ.A) : (ZMod 2 × ZMod 2) × ℕ := (g.1, hval φ g.2)

def recOf {φ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ) : (ZMod H.condN)ˣ →* Multiplicative (E0 × φ.A) where
  toFun u := Multiplicative.ofAdd
    ((Multiplicative.toAdd (sgn2 (H.art u).1.2), Multiplicative.toAdd (sgn2 (H.art u).1.1)), φ.iotaInv (H.art u).2)
  map_one' := by
    simp only [Prod.snd_one, Prod.fst_one, map_one]
    rfl
  map_mul' u v := by
    simp only [Prod.snd_mul, Prod.fst_mul, map_mul]
    rfl

def arithOf {φ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ) : ArithData φ.A := cftData H.q H.d (recOf H)

section
variable {eps : ℝ} (Fm : FamP eps) (x : ℝ) (φ : Formalism.HC.Frame) (m f q d : ℕ)

def TiePts (pt : φ.A → Fm.Ix x) (av bv : ℕ → ℤ) : Prop :=
  ∀ u0 : φ.A,
    (Fm.D x (pt u0)).R.toFrame = φ ∧ (Fm.D x (pt u0)).R.m = m ∧ (Fm.D x (pt u0)).R.f = f ∧
    (Fm.D x (pt u0)).host.q = q ∧ (Fm.D x (pt u0)).host.d = d ∧
    (Fm.D x (pt u0)).host.u0.val = hval φ u0 ∧
    ∀ t : (Fm.D x (pt u0)).host.TT,
      (Fm.L x (pt u0)).aT t = av (t : (Fm.D x (pt u0)).R.A).val ∧
      (Fm.L x (pt u0)).bT t = bv (t : (Fm.D x (pt u0)).R.A).val

variable {φ m f}

def TieGlobal (pt : φ.A → Fm.Ix x) {Top : Type}
    (Dd : Data φ.A (fun u0 => (Fm.D x (pt u0)).what₂.Word) Top m f) (Xpp η X' : ℝ) : Prop :=
  ∀ u0 : φ.A,
    Dd.a = (Fm.L x (pt u0)).sc.a ∧ Dd.b = (Fm.L x (pt u0)).sc.b ∧ Dd.b' = (Fm.L x (pt u0)).sc.b' ∧
    Dd.k = ((Fm.D x (pt u0)).R.k : ℝ) ∧ Dd.L = (Fm.L x (pt u0)).sc.L ∧ Dd.La = (Fm.L x (pt u0)).La ∧
    Dd.B0 = (Fm.L x (pt u0)).B0 ∧ Dd.Nc = (Fm.L x (pt u0)).Nc ∧
    Dd.gam = Real.eulerMascheroniConstant ∧ Dd.LpL = (Fm.L x (pt u0)).logDerivativeAtOne ∧
    Dd.v = (Fm.D x (pt u0)).host.v ∧
    Dd.lg = Real.log (((Fm.D x (pt u0)).host.g 0 : ℝ) * ((Fm.D x (pt u0)).host.g 1 : ℝ)) ∧
    Dd.logGam = Real.log (GamL (Fm.L x (pt u0))) ∧
    Xpp = (Fm.L x (pt u0)).sc.X'' (Fm.D x (pt u0)).R.n ∧ η = (Fm.L x (pt u0)).etaSz ∧
    X' = (Fm.L x (pt u0)).sc.X'

def TieLocal (pt : φ.A → Fm.Ix x) {Top : Type}
    (Dd : Data φ.A (fun u0 => (Fm.D x (pt u0)).what₂.Word) Top m f) : Prop :=
  ∀ u0 : φ.A,
    (∀ u : (Fm.D x (pt u0)).what₂.Word,
      Dd.d u0 u = (((Fm.D x (pt u0)).div.Nu u).rank : ℝ) ∧
      Dd.T u0 u = (((Fm.D x (pt u0)).mem u).A.T : ℝ) ∧
      Dd.muN u0 u = ((Fm.D x (pt u0)).div.Nu u).mu ∧
      Dd.muMaxN u0 u = ((Fm.D x (pt u0)).div.Nu u).muMax ∧
      Dd.h u0 u = (Fm.D x (pt u0)).div.h u ∧
      Dd.muM u0 u = (((Fm.D x (pt u0)).fm u).lat 0).mu ∧
      Dd.muMaxM u0 u = (((Fm.D x (pt u0)).fm u).lat 0).muMax ∧
      ∀ j : Fin m, Dd.EeJ u0 u j =
        ∑ w ∈ (Fm.L x (pt u0)).supp, SizeData₂.sz w ((Fm.L x (pt u0)).E u (j.val + 1) w)) ∧
    Dd.muCC u0 = (Fm.D x (pt u0)).div.RR.muDual ∧
    Dd.muMinCC u0 = (Fm.D x (pt u0)).div.RR.muMinDual ∧
    Dd.Fo u0 = (Fm.L x (pt u0)).Fo ∧ Dd.Ga u0 = (Fm.L x (pt u0)).Ga ∧
    Dd.Ta u0 = ∑ w ∈ (Fm.L x (pt u0)).supp, SizeData₂.sz w ((Fm.L x (pt u0)).tau w) ∧
    Dd.IO u0 = ∑ w ∈ (Fm.L x (pt u0)).supp,
      SizeData₂.lwP w * ((Fm.D x (pt u0)).what₂.places.ramIdx w : ℝ) * (Fm.L x (pt u0)).io w ∧
    Dd.del u0 = (Fm.D x (pt u0)).what₂.delp

def TieArith (pt : φ.A → Fm.Ix x) (av : ℕ → ℤ) (D : ArithData φ.A) (ell : AddChar (E0 × φ.A) ℂ → ℂ)
    (TT T2 : Finset φ.A) (a : φ.A → ℝ) (w : φ.A → Fin m → E0 × φ.A → ℝ) : Prop :=
  (∀ h, h ∈ TT ↔ hval φ h ∈ Fm.TTn x) ∧
  (∀ u0 h, h ∈ T2 ↔ ∃ s ∈ (Fm.D x (pt u0)).host.T2, h = φ.dig s) ∧
  (∀ h, a h = (av (hval φ h) : ℝ)) ∧
  (∀ u0 (j : Fin m) (g : E0 × φ.A) (τ : (Fm.D x (pt u0)).what₂.Tau),
    gcode (Fm.D x (pt u0)).R.toFrame (((Fm.D x (pt u0)).eTau τ : (Fm.D x (pt u0)).R.Psi) : (Fm.D x (pt u0)).R.GG)
      = mcode φ g → w u0 j g = wj (Fm.D x (pt u0)) (j.val + 1) τ) ∧
  (∀ ψ : AddChar (E0 × φ.A) ℂ, ψ ≠ 0 → ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    (∀ n : ℕ, n ≠ 0 → χ (n : ZMod N) = primVal D ψ n) → ell ψ = GlobalTheoryTheory.logDerivativeAtOne χ)

end

def ChainTied {eps : ℝ} (Fm : FamP eps) (eD eL K cHH eK CL x : ℝ) : Prop :=
  ∃ (i0 : Fm.Ix x) (m f : ℕ) (pt : (Fm.D x i0).R.A → Fm.Ix x) (av bv : ℕ → ℤ)
    (Top : Type) (_ : Fintype Top)
    (Dd : Data (Fm.D x i0).R.A (fun u0 => (Fm.D x (pt u0)).what₂.Word) Top m f) (C : Consts) (Xpp : ℝ)
    (ell : AddChar (E0 × (Fm.D x i0).R.A) ℂ → ℂ) (N : ℕ) (TT T2 : Finset (Fm.D x i0).R.A) (a : (Fm.D x i0).R.A → ℝ)
    (w : (Fm.D x i0).R.A → Fin m → E0 × (Fm.D x i0).R.A → ℝ) (eT : Top ≃ TT)
    (eP : Fin f ≃ PhiSet (H := (Fm.D x i0).R.A)) (η X' θ : ℝ),
    TiePts Fm x (Fm.D x i0).R.toFrame m f (Fm.D x i0).host.q (Fm.D x i0).host.d pt av bv ∧
    TieGlobal Fm x pt Dd Xpp η X' ∧ TieLocal Fm x pt Dd ∧
    TieArith Fm x pt av (arithOf (Fm.D x i0).host.toHostRaw) ell TT T2 a w ∧
    Dd.x = x ∧ Dd.ε = eps ∧ C.eDiv ≤ eD ∧ C.eLoss ≤ eL ∧ C.cHH ≤ cHH ∧
    Ident Dd (arithOf (Fm.D x i0).host.toHostRaw) N ell TT a w eT eP ∧
    Formalism.LFunctionChainParameters.LChain.SizeData₂ Dd C Xpp ∧
    ErrWindows Dd C Xpp eK K ∧
    BNBounds Dd T2 ∧
    GrowthInequalityRemainingHyps (arithOf (Fm.D x i0).host.toHostRaw) ell N TT T2 a w x eps Dd.b Dd.b' η X' θ CL ∧
    CostWindows x (fPl (Fm.D x i0).R.A) Dd.b η θ ∧
    RestSize eps x (Fintype.card (Fm.D x i0).R.A) TT.card T2.card m Dd.b Dd.k Dd.a

end Formalism.MainNotions

end
end

section

noncomputable section

namespace Formalism.MainNotions.product_first_zeroth_parts

open Formalism.BasicNotions Classical NumberField

section Gen

variable {R : Ranks} {LL : Type} [Field LL] [NumberField LL] [StarRing LL] {embLL : LL →+* ℂ}
  {Pl : Rows.Places LL} {Tau : Type} [Fintype Tau] {hc : Tau → HCParam R}
  {C : ColumnChain R Tau hc} {A : ColumnsAtT R C} {P : PeriodMap R C}
  (M : MemberForms LL embLL Pl Tau hc C A P)

end Gen

section Fm

variable (D : D7) (u : D.what₂.Word)

end Fm

section Tw

variable (D : D7)

variable {D}

variable (D)

structure PendTw (u : D.what₂.Word) (μ : D.what₂.Tup) where

  clsLat : letI := D.host.cmStar; ∀ i, (D.chTw u μ).cls i → Submodule (𝓞 D.host.E) (D.sp.X i).V
  clsLat_lat : letI := D.host.cmStar; ∀ i c, Submodule.IsLattice D.host.E (clsLat i c)

  detCls : ∀ i, (D.chTw u μ).cls i → D.Dt

  xi : D.Dt →* ℂˣ
  xi_fin : ∃ n : ℕ, 0 < n ∧ ∀ x, xi x ^ n = 1
  trueColumnChoices_heckeChar_reference_eq_one : μ = D.what₂.mu0 → xi = 1

  rhoDet_eq_inv_muTilde_chiD_pow : ∀ i (c : (D.chTw u μ).cls i),
    (D.chTw u μ).rhoDet i c = (((D.muTil (i + 1) (detCls i c) * xi (detCls i c))⁻¹ *
      (D.chiD (detCls i c)) ^ (-(((D.R.N (i + 1)) / 2 : ℕ) : ℤ)) : ℂˣ) : ℂ)
  rhoDetPrime_eq_muTilde_mul_chi_pow : ∀ i (c : (D.chTw u μ).cls (i + 1)),
    (D.chTw u μ).rhoDet' i c = ((D.muTil (i + 1) (detCls (i + 1) c) * xi (detCls (i + 1) c) *
      (D.chiD (detCls (i + 1) c)) ^ ((((D.R.N i) / 2 : ℕ) : ℤ)) : ℂˣ) : ℂ)

  c0 : (D.mem u).C.cls 0 ≃ (D.chTw u μ).cls 0
  y0 : (D.mem u).C.Y 0 ≃ (D.chTw u μ).Y 0
  zero_class_lattice_eq : ∀ c, clsLat 0 (c0 c) = D.clsLat u 0 c
  zero_class_det_eq : ∀ c, detCls 0 (c0 c) = D.detCls u 0 c

  zero_identification_is_identity : ∀ φ c y, D.e0Tw u μ φ (c0 c) (y0 y) = φ c y

variable {D}

def colTw (u : D.what₂.Word) (μ : D.what₂.Tup) (x : Vl D u 0) : (D.chTw u μ).cls D.R.m → (D.chTw u μ).Y D.R.m → ℂ :=
  (D.chTw u μ).col (D.e0Tw u μ ((D.fm u).emb 0 x))

def TwistedT5ColumnBound (T : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (C : ℝ) : Prop :=
  ∀ w, OverT D u w →
    ∃ e : ℕ, (e : ℝ) ≤ D.R.m * (4 * ∑ τ, (Wt D u τ : ℝ) + C * D.R.f * D.R.N D.R.m) +
        ∑ v ∈ VV D u w, ((D.R.t : ℝ) + 1 + 2 * Wt D u ((D.fm u).tauOf w v) + C * D.R.N D.R.m) *
          ((D.R.m : ℝ) * (D.R.m + 1) / 2) ∧
      ∀ x ∈ Nlam D u w, ∃ y ∈ (T.fm u μ).S D.R.m w, (T.fm u μ).emb D.R.m y = tpow D u e • colTw u μ x

def TupleChainSharpColumnValuation (Dx : DivX D) (T : TwForms D) (u : D.what₂.Word) : Prop :=
  ∀ w : D.what₂.places.Pl, D.what₂.places.resChar w = (D.mem u).A.T →
    ∀ μ, D.what₂.places.resChar w ∉ Dx.Qp μ → ∀ x ∈ LT.Nlam D u w,
      Formalism.MainNotions.WeilJacquetShalikaLaw.ColGeTw T u μ w x (-((D.R.m : ℝ) * EatT D u w))

end Tw

section Fam

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

end Fam

section Ref

open Formalism.BasicNotions.DV

variable {D : D7}

end Ref

end Formalism.MainNotions.product_first_zeroth_parts
end
end

section

noncomputable section

namespace Formalism.MainNotions.StandardLattice

open NumberField Formalism.BasicNotions Finset Formalism.MainNotions.S
open scoped TensorProduct

def eqvFn {G : Type} [Group G] (Γ K : Subgroup G) (V : Type) [AddCommGroup V] [Module ℂ V]
    (a : Γ →* Module.End ℂ V) (ψ : K →* ℂˣ) : Submodule ℂ (G → V) where
  carrier := {φ | ∀ (γ : Γ) (x : G) (κ : K), φ (γ * x * κ) = ((ψ κ)⁻¹ : ℂˣ) • a γ (φ x)}
  add_mem' := by
    intro φ φ' h h' γ x κ
    simp only [Pi.add_apply, map_add (f := _), smul_add, h γ x κ, h' γ x κ]
  zero_mem' := by
    intro γ x κ
    simp
  smul_mem' := by
    intro c φ h γ x κ
    simp only [Pi.smul_apply, map_smul, h γ x κ]
    rw [smul_comm]

abbrev GAf (D : D7) : Type :=
  letI := D.host.cmStar
  ↥(Formalism.UG.UPts D.sp.cm.sig D.sp.gram0 (IsDedekindDomain.FiniteAdeleRing (𝓞 D.host.F) D.host.F))

def GF (D : D7) : Subgroup (GAf D) :=
  letI := D.host.cmStar
  (Formalism.UG.ratPts D.sp.cm.sig D.sp.gram0 (IsDedekindDomain.FiniteAdeleRing (𝓞 D.host.F) D.host.F)).subgroupOf
    (Formalism.UG.UPts D.sp.cm.sig D.sp.gram0 (IsDedekindDomain.FiniteAdeleRing (𝓞 D.host.F) D.host.F))

def KPi (D : D7) (Lv : LevelData D) (u : D.what₂.Word) : Subgroup (GAf D) :=
  letI := D.host.cmStar
  (Lv u).U.subgroupOf
    (Formalism.UG.UPts D.sp.cm.sig D.sp.gram0 (IsDedekindDomain.FiniteAdeleRing (𝓞 D.host.F) D.host.F))

def colFn (D : D7) (Lv : LevelData D) (u : D.what₂.Word) (V : Type) [AddCommGroup V] [Module ℂ V]
    (a : GF D →* Module.End ℂ V) (ψ : KPi D Lv u →* ℂˣ) : Submodule ℂ (GAf D → V) :=
  eqvFn (GF D) (KPi D Lv u) V a ψ

structure ColRep (D : D7) (Lv : LevelData D) (u : D.what₂.Word) where
  H : D.what₂.Tau → Type
  [nacg : ∀ ρ, NormedAddCommGroup (H ρ)]
  [ips : ∀ ρ, InnerProductSpace ℂ (H ρ)]
  π : ∀ ρ, Matrix (Fin D.R.k) (Fin D.R.k) ℂ → (H ρ →L[ℂ] H ρ)
  π_type : ∀ ρ, IsHCTypeU D.R.k (uColR D u ρ) (π ρ)
  B : D.what₂.Tau → Matrix (Fin D.R.k) (Fin D.R.k) ℂ
  B_spec : letI := D.host.cmStar; ∀ ρ, (B ρ).conjTranspose * B ρ = D.sp.gram0.map (embOf D ρ)
  a : GF D →* Module.End ℂ (⨂[ℂ] ρ, H ρ)
  a_spec : ∀ (γ : GF D) (γ0 : GL (Fin D.R.k) D.host.E),
    (γ : GAf D).1 = Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F)
      (IsDedekindDomain.FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ0 →
    ∀ v : ∀ ρ, H ρ, a γ (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ
      (fun ρ => π ρ (B ρ * (γ0 : Matrix (Fin D.R.k) (Fin D.R.k) D.host.E).map (embOf D ρ) * (B ρ)⁻¹) (v ρ))
  ψ : KPi D Lv u →* ℂˣ

attribute [instance] ColRep.nacg ColRep.ips

abbrev ColRep.V {D : D7} {Lv : LevelData D} {u : D.what₂.Word} (X : ColRep D Lv u) : Type := ⨂[ℂ] ρ, X.H ρ

section Fam

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

end Fam

end Formalism.MainNotions.StandardLattice
end
end
