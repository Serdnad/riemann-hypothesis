module

public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.Bundle003
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Formalism.PieriBlockIdeals.Bundle006
public import Formalism.SharpRestriction.Divisibility.JumpSets
public import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds

namespace GlobalTheory.ShareOn

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {U C : Type} [Group U] [MulAction U C]

def sub (M : TwoLevels E r U C) (H : Subgroup U) : TwoLevels E r H C :=
  { M with
    tr := fun u c => M.tr u c
    tr_herm := fun u => M.tr_herm u
    tr_Λ := fun u => M.tr_Λ u
    tr_L' := fun u => M.tr_L' u
    tr_conj := fun u => M.tr_conj u
    tr_mul := fun u v => M.tr_mul u v
    tr_faithful := fun u c h1 h2 => Subtype.ext (M.tr_faithful u c h1 h2) }

def IsPullRep (M : TwoLevels E r U C) (la : Wt M.Ψ r) (ρ : Representation ℂ U (M.cusp la)) : Prop :=
  ∃ a : U → C → ℂˣ, ∀ (h : U) (F : C → Frame M.Ψ r → ℂ) (hF : F ∈ M.SS la) (c : C) (x : M.dom),
    ((ρ h⁻¹ ⟨M.res F, Submodule.subset_span ⟨F, hF, rfl⟩⟩ : M.cusp la) : C → M.dom → ℂ) c x = (a h c : ℂ) * M.pull h F c x.1

def Ranks (M : TwoLevels E r U C) (ka : Wt M.Ψ r) (s : ℕ) (ep c : ℝ) : Prop :=
  Module.Finite ℂ (M.cusp ka) ∧ Module.Finite ℂ (M.cusp (ka + 2 • deMul M.Ψ r M.p0 s)) ∧
    (1 - ep) * finrank ℂ (M.cusp ka) ≤ finrank ℂ (M.cusp (ka - deMul M.Ψ r M.p0 s)) ∧
    (finrank ℂ (M.cusp (ka + 2 • deMul M.Ψ r M.p0 s)) : ℝ) ≤ c * finrank ℂ (M.cusp (ka - deMul M.Ψ r M.p0 s)) ∧
    Module.Finite ℂ (M.cusp (ka - deMul M.Ψ r M.p0 s))

def ArchOne (X : Data E r) (L Fp : Wt X.Ψ r) (T : ℕ) : Prop :=
  ∃ Xa : ArchInM X, Xa.L = L ∧ Xa.Fp = Fp ∧ Xa.T = T ∧ GlobalTheory.Shares.Margins X Xa ∧ Nonempty (FlatM X Xa)

def ArchOn (M : TwoLevels E r U C) (ka : Wt M.Ψ r) (T : ℕ) : Prop :=
  ∃ L Fp : Wt M.Ψ r, ka = Fp + T • L ∧ GapsGe M.p0 L 1 ∧ PairGe L (1.9 * T) ∧
    GapsGe M.p0 (Fp - kLog M.Ψ r - (M.dimY + 2) • L) 0 ∧ PairGe (Fp - kLog M.Ψ r - (M.dimY + 2) • L) 1 ∧
    ∀ c, ArchOne (M.comp c).toData (castWt (M.comp_Ψ c) L) (castWt (M.comp_Ψ c) Fp) T

def sOf (M : TwoLevels E r U C) : ℕ := 2 * r + 50 * r ^ 2 * M.dimX + 2

theorem even_sOf (M : TwoLevels E r U C) : Even (sOf M) := ⟨r + 25 * (r ^ 2 * M.dimX) + 1, by unfold sOf; ring⟩

theorem le_sOf (M : TwoLevels E r U C) : 2 * r + 50 * r ^ 2 * M.dimX + 1 ≤ sOf M := Nat.le_succ _

end Model

section Point

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

def HalfUnip (H : Subgroup p.P.Gp) : Prop :=
  ∃ k : Fin 2, ∀ g ∈ H, ∀ v : D.nd.PlG k,
    Formalism.MainNotions.ArithmeticCylinders.IsUniUp (((p.R.eG.trans p.cG) g ⟨k, v⟩ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g k)))

def ModelAt (T : ℕ) : Prop :=
  ∃ (C : Type) (_ : Finite C) (_ : MulAction p.P.Gp C) (M : TwoLevels D.host.E D.R.r p.P.Gp C) (ka : Wt M.Ψ D.R.r)
    (ρ : Representation ℂ p.P.Gp (M.cusp ka)) (σ : D.what₂.LL →+* ℂ)
    (f : (Fin (p.R.toRealDat.nW i) → D.what₂.LL) →ₛₗ[σ] M.cusp ka),
    IsPullRep M ka ρ ∧ (∀ g v, ρ g (f v) = f ((p.R.toRealDat.FW i).ρ g v)) ∧
    (LinearIndependent ℂ fun k => f (Pi.single k 1)) ∧ Submodule.span ℂ (Set.range f) = ⊤ ∧
    (∀ H, HalfUnip p H → LevelHyp (sub M H)) ∧ M.Ψ.card = D.R.f ∧
    ((M.p0 = 0 ∨ M.p0 = D.R.r) ∨ (0 < M.p0 ∧ M.p0 < D.R.r ∧ ArchOn M ka T))

def ShareW (y : ℝ) : Prop :=
  (1 - y) * (p.R.toRealDat.nW i : ℝ) ≤ (Nat.card p.P.P0 : ℝ) * finrank D.what₂.LL (spType p.R.toRealDat p.F.lv2 i)

def BadW (del : ℝ) : Prop :=
  (finrank D.what₂.LL (spType p.R.toRealDat p.F.lv2 i ⊓ LinearMap.ker (eGood p.R.toRealDat i) : Submodule D.what₂.LL _) : ℝ) ≤
    del * finrank D.what₂.LL (spType p.R.toRealDat p.F.lv2 i)

end Point

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigOn

end GlobalTheory.ShareOn

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT

open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.BigTop

namespace GlobalTheory.Fc.Ind

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}

@[reducible] def rowSideOfCompatibleThetaPair (P : RowSideFamily ex) : IndefiniteRowSideFullHecke ex where
  Gp := P.Gp
  Pl0 := P.Pl0
  I0 := P.I0
  T := P.T
  A3 := P.A3
  P0 := P.P0
  ψ0 := P.ψ0
  Ps := P.Ps
  ψs := P.ψs
  Zs := P.Zs
  S0 := P.S0
  S1 := P.S1
  Dc := P.Dc
  Sp := P.Sp
  C := P.C
  NuC := P.NuC
  I := P.I
  JA := P.JA
  JM := P.JM
  div := P.tied.div
  amb0 := P.tied.amb0
  mjH := P.tied.mjH
  cen0 := P.tied.cen0

abbrev zscOf (P : RowSideFamily ex) (Del h0 : ℕ) (c : ℝ) : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3 :=
  (rowSideOfCompatibleThetaPair P).zsc Del h0 c

abbrev PtP : Type 1 := ∀ (D : D7) (O : Obj D) (c : ℝ), PtAt O.ex c → Prop

end GlobalTheory.Fc.Ind

end
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts HidaSetting WInputsLink h0)

namespace GlobalTheory.ExpTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def LIncl {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type} (B : BlockDat K G Pl0)
    (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (w : HeightOneSpectrum (𝓞 K)) (J : ℕ) : Prop :=
  ∀ z ∈ B.cutZ ℓ Z, (((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 K) ^ J) • z ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (B.delZ ℓ Z)

def Covers {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type} (B : BlockDat K G Pl0)
    (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (w : HeightOneSpectrum (𝓞 K)) {ι : Type} {N : ℕ} {lam : ι → ℕ → ℕ} {I : Type}
    (X : I → HidaSetting ι N lam) : Prop :=
  ∀ J : ℕ, (∀ i, (X i).Incl (Formalism.EigenvalueLevelCeiling.plc w) J) → LIncl B ℓ Z w J

def reFr {ι : Type} (W : Wts ι) (fr : ℕ → ι → ι) (cj : ℕ → ι → Bool) : Wts ι := { W with fr := fr, cj := cj }

variable {D : D7}

structure Dict (L : SizeData₂ D) (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau) : Prop where
  k : P.k = D.R.k
  m : P.m = D.R.m
  t : P.t = D.R.t
  f : P.f = D.R.f
  card : Nat.card D.what₂.Tau = P.f
  Nr : P.Nr = (Vc D j).rank
  x : P.x = L.sc.x
  log : P.L = L.sc.x ^ L.sc.eps
  b : P.b = L.sc.b
  lam : ∀ τ, ∃ c : ℤ, ∀ a : Fin (Vc D j).rank,
    (W.lam τ a : ℤ) = (Formalism.IndefR.Bridge.lamLdef (D := D) (Vc D j).rank ((j : ℕ) + 1) τ).w a + c
  forced : ∀ τ, Formalism.IndefR.Bridge.IsLamPrime (Formalism.IndefR.Bridge.lamLdef (D := D) (Vc D j).rank ((j : ℕ) + 1) τ) ((j : ℕ) + 1) τ
  box : ∀ τ a, a < P.Nr → 0 ≤ W.U P τ a ∧ W.U P τ a ≤ (h0 P : ℤ)
  thick : W.T2.card ≤ D.host.T2.card
  special : W.Sp = Formalism.MainNotions.JumpSetsAlt.excSet D
  big : ∀ i, P.h < (D.host.g i : ℝ)

def NumOk {ι : Type} (P : Par) (W : Wts ι) : Prop :=
  P.Hyp ∧ P.Large ∧ W.Ok P ∧ ∃ X' A : ℝ, Formalism.CohomologicalDescent.LargeParameterEstimates.Rows P X' A ∧ Formalism.CohomologicalDescent.LargeParameterEstimates.Big P.L P.x X' A

section Point

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)

abbrev blk (j : Fin D.R.m) (t : p.P.T) := p.P.A3.A.fam.L j t

abbrev lvlL := p.P.A3.A.fam.lvlA p.P.P0 p.P.ψ0

abbrev subZ (j : Fin D.R.m) (t : p.P.T) : Submodule D.what₂.LL (blk p j t).S.Forms :=
  (p.P.A3.fam3.toSub2 (p.R.toCx3 p.F).zs).Zl j t


open Classical in
def ModelAt (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : Prop :=
  ∃ (fr : ℕ → D.what₂.Tau → D.what₂.Tau) (cj : ℕ → D.what₂.Tau → Bool) (I : Type) (X : I → HidaSetting D.what₂.Tau P.Nr W.lam),
    Covers (blk p j (p.R.mu w)) (lvlL p) (subZ p j (p.R.mu w)) w X ∧
      ∀ i, ¬ IsUnit ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : (X i).O) ∧ WInputsLink P (reFr W fr cj) (X i) (Formalism.EigenvalueLevelCeiling.plc w)

end Point


end GlobalTheory.ExpTie

end
end
