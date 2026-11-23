module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle017
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle018
public import Formalism.LocalToGlobal.HermitianForms.Bundle011
public import Formalism.LocalToGlobal.HermitianForms.Bundle006
public import Formalism.LocalToGlobal.GroupLattices.StdSubAtOfRing
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Formalism.LocalToGlobal.HilbertRowConditions.TiedEMt
public import Formalism.LocalToGlobal.KernelLattices.Bundle001
public import Formalism.LocalToGlobal.KernelLattices.Bundle004
public import Formalism.LocalToGlobal.KernelLattices.Bundle003
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle005
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle001
public import Formalism.LocalToGlobal.GlobalTheory.LinkTiesOm
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle005
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace GlobalTheory.Core.Rk.SWQ

open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW
open Formalism.UG (IsUnifV qV Ov ordL diagJ)
open GlobalTheory.LFun (KGL toCompl IsSplitChart)

section Local

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {m n N : ℕ}

def IntM {ι κ : Type} (x : Matrix ι κ (w.adicCompletion E)) : Prop := ∀ i j, x i j ∈ Ov E w

def mob (q r : ℕ) : ℂ := (-1) ^ r * (q : ℂ) ^ (r * (r - 1) / 2)

def cOne (q : ℕ) (z : ℂˣ) (σ : ℂ) (r : ℕ) : ℂ := mob q r * (z : ℂ) ^ r * (q : ℂ) ^ (-(σ * r))



end Local

section Adelic

variable {D : D7} {q : FinPl D} {w : HeightOneSpectrum (𝓞 D.host.E)}

def cw (h : w.under (𝓞 D.host.F) = q) : AE D →+* w.adicCompletion D.host.E := (toCompl h).comp (compFin D.host.F D.host.E q)

def offM (q : FinPl D) {m n : ℕ} (x : Mx D m n) : Mx D m n :=
  x - algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleFin q 1)) • x

end Adelic

end GlobalTheory.Core.Rk.SWQ

end
end

section

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MiTop

section Alg

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)
  {fc : DefSub A → DefFace Bs}

def Anchored (eV : ∀ t, (Fin ((fc X.zs).Df1.nV t) → K) →ₗ[K] A.FR t) (sEE : X.EE →ₗ⋆[ℂ] (fc X.zs).Sp.HH)
    (V : X.EE →ₗ[ℂ] X.EE) (U : ∀ u, Matrix (Fin ((fc X.zs).Dc.a u)) (Fin ((fc X.zs).Dc.a u)) ℂ)
    (c : (fc X.zs).Dc.Mem → Bs.Tup → ℂ) : Prop :=
  ∀ u, ∃ p b : ℂ, p ≠ 0 ∧ b ≠ 0 ∧ ∀ t (φ : Fin ((fc X.zs).Dc.a u) → K) (F : Fin ((fc X.zs).Df1.nV t) → K),
    c u t * Bs.v0.embedding ((fc X.zs).Dc.Pt u t φ F) * b =
      p * ⟪sEE (V (X.Θ t (X.jR t (eV t F)))), (fc X.zs).Sp.Pu u ((U u).mulVec (cpt Bs.v0.embedding φ))⟫_ℂ

def UnitAt (c : (fc X.zs).Dc.Mem → Bs.Tup → ℂ) : Prop :=
  (∀ u t, c u t ≠ 0) ∧ ∀ u w (k : K), Bs.v0.embedding k = c u (X.μ w) / c u Bs.μ0 → vw w k = 0

end Alg

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex)

abbrev rJ : Set (GA D (D.sp.Y 0)) :=
  levS (Yc D 0) (W.Q.Rl.βY 0) (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true))

abbrev rChi : GA D (D.sp.Y 0) → ℂ :=
  Formalism.IndefR.Lev.levChi (Yc D 0) (W.Q.Rl.βY 0) (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true))

def rowOf (e : W.Q.Rl.HE.H) : SmT (W.Q.Rl.MY 0) →ₗ[ℂ] (GA D (Yc D 0) → ℂ) := PiTensorProduct.lift (W.Q.Rl.HE.e e)

def rowAt (t : W.P.T) (F : Fin ((W.Q.F.fc (cxW W).zs).Df1.nV t) → D.what₂.LL) :
    SmT (W.Q.Rl.MY 0) →ₗ[ℂ] (GA D (Yc D 0) → ℂ) :=
  rowOf W (W.Q.Rl.Th t (W.Q.Rl.jX t (W.Q.F.eV (cxW W).zs t F)))

abbrev F0 (u : D.what₂.Word) : Formalism.L2.Forms.Forms0 D u := (W.R.T.cols.forms u).to0

structure BotDat (u : D.what₂.Word) where
  B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)
  b : GA D (D.sp.Y 0)
  a₀ : GA D (D.sp.X 0)
  a : GA D (D.sp.X 0)
  k : GA D (D.sp.Y 0)

variable {W}

variable (W)

structure BotHyp : Prop where
  hyp : HypAt W
  pins : RealPins W.Q
  see : SeeEx W.Q
  used : ∀ t : W.P.T, Formalism.IndefR.RecTie.Used0 D (W.P.I.tup t)
  idE : GlobalTheory.Core.Mi.IdE W.S.X
  gap : GlobalTheory.Count.GapGe W.S.X.B (100 * (D.R.r : ℝ) ^ 4)
  fin : Formalism.L2.SG.PackageTie2.FinX W.S.Y

end GlobalTheory.MiTop

namespace GlobalTheory.MiTop

def PuNZ (D : D7) : Prop :=
  ∀ u, ∃ φ : (D.mem u).A.Mram, D.s.Pu u ((D.s_Cu u).symm ⟨φ.1, φ.2.1⟩) ≠ 0

end GlobalTheory.MiTop

end
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw
open scoped TensorProduct Classical

namespace GlobalTheory.AdForm.TwTest
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι} {Ch : ℕ → Type}
  {A : TwDat I l Z u a Ch}

theorem cosetIn_eq_empty {j : ℕ} (h : j + 1 ≠ B.R.m) (p : PtAt B.R I.sel (I.tup a) (I.cst a) u j) : cosetIn p = fun _ => ∅ := by
  have h1 : p.1.2 = ∅ := by
    have := p.2
    rw [ysAt_ys_of_ne I.sel (I.tup a) (I.cst a) h] at this
    exact this
  funext P
  ext z
  simp [cosetIn, h1]

theorem chartIndex_injective_offLastStep (hA : A.Is) {j : ℕ} (hj : j ≤ B.R.m) (h : j + 1 ≠ B.R.m) : Function.Injective (A.b0 j) := fun α β e =>
  hA.chart_ext j hj α β e (by rw [cosetIn_eq_empty h, cosetIn_eq_empty h])

theorem subsingleton_top (hA : A.Is) : Subsingleton (Ch B.R.m) :=
  ⟨fun α β => chartIndex_injective_offLastStep hA le_rfl (by omega) (by rw [Idx.eq_top (A.b0 _ α) le_rfl, Idx.eq_top (A.b0 _ β) le_rfl])⟩


section Pin
variable {ψ : AddChar (AF (I.rec7 l Z).host.F) ℂ} {θ : InfFam (I.rec7 l Z)}
    {x : ∀ j, DefSp ((I.rec7 l Z).sp.X j)} {vac : ∀ j, WO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) → ℂ} {c₀ : ℕ → ℂ}
    {kom kom' : ∀ j, Om ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1))}
    {dd dd' : ∀ j, Ch j → Ch (j + 1) → WO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) →₀ ℂ}
    {w w' : ∀ j, Ch j → Ch (j + 1) → ℂ} {Ram Ram' : ∀ j, Set (ColT I l u a j)}
    {rd rd' : ∀ j, Ch j → ColT I l u a j → (I.chain l u a).Y j → GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) → ℂ} {cK : ℕ → ℂ}

end Pin

end GlobalTheory.AdForm.TwTest
end
end

section

noncomputable section

namespace GlobalTheory.Core.Cls

open Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2 NumberField IsDedekindDomain Matrix Formalism.UG

def LowerTie {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}
    (Tf : Forms.FormsTiedSym D u Ch chOf) : Prop :=
  IsUnit (Forms.bZ u Tf.til.z0).det → ∀ (ψ : (D.mem u).P.Wz) (c : (D.fm u).clsP)
    (P : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ),
    P ∈ Forms.CSpan ((D.fm u).lam D.R.m) →
    (∀ s, Tf.eWz ψ c s =
      Forms.fnOf _ (Forms.shiftOf (Forms.lamT u D.R.m)) (Forms.mZ u Tf.til.z0) P ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s)) →
    Tf.valP.eW ((D.mem u).P.lowerMap ψ) c = Forms.fnOf _ (Forms.shiftOf (Forms.sgT u)) 1 (Ker.brTen D u P)

def RootsG (D : D7) : Prop :=
  ∀ i, (∃ ζ : D.what₂.LL, IsPrimitiveRoot ζ (D.host.g i)) ∧ ∃ ζ : D.what₂.LL, IsPrimitiveRoot ζ (D.host.g i - 1)

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}

structure SelC (ex : Extra D L hT Gi Gl K Y cX) : Type 1 where

  host : Host.HostTied D

  real : Theta.RealTied D

  cols : Forms.ColsTiedSym D

  full : Forms.ColsFullS cols

  extra : Forms.ColsExtraTiedS full ex

  cf : Host.CharFrame D

  tp : Host.TupTied D cf ex.nch

  chrVal : Host.ValLL0 D cf

  chrDt : Host.DtTied D cf

  roots : RootsG D

  tw : Forms.SymmetricTwistedColumnsAtPrimes tp cols ex.tw

  emt : Rows.EMtTied D cols tw

  g : G.GroupCompatibilityAll D hT ex.cmp

  herm_eq : g.herm = full.1.to0

  forms_eq : g.forms = fun u => (cols.forms u).to0

  beOn : ∀ u, Ker.BeOnTie D u

  lower : ∀ u, LowerTie (cols.forms u)

  ambMetric : ∀ u, Rk.AmbMetric D u ex.amb

  ambLattice : ∀ u, Rk.AmbLattice D u ex.amb

structure SelB (ex : Extra D L hT Gi Gl K Y cX) : Type 1 extends SelC ex where

  ker : Ker.KerEntTied ex

  crd : ∀ (u : D.what₂.Word) i, i ≤ D.R.m → GL (Fin (D.R.N i)) D.host.E

  crd_gram : ∀ u i (hi : i ≤ D.R.m),
    cT (Forms.sigD D : D.host.E →+* D.host.E) (crd u i hi).1 * (crd u i hi).1 = Forms.gramN D i hi

  crd_lat : ∀ u i (hi : i ≤ D.R.m) (x : Fin (D.R.N i) → D.host.E),
    x ∈ Forms.selfDualLatticeCoords D i hi ↔ ∀ a, ((crd u i hi).1 *ᵥ x) a ∈ (algebraMap (𝓞 D.host.E) D.host.E).range

  ker_sharp : ∀ μ, (ker.cst μ).sharp = true

  ker_frm : ∀ u μ i (hi : i ≤ D.R.m) (y : (D.chTw u μ).Y i) (τ : D.what₂.Tau),
    (ker.O u μ).frm i y τ = Forms.atInf (Forms.embT D) (crd u i hi).1 τ * (Forms.twYS tw.ch cols.forms u μ i hi y).1 τ

  aaUnit : ker.AAUnit

  unfAll : ker.UnfAll

  adapted : ker.Adapted

  top : ker.TopPinned

  chTie : ker.ChTie

  memSide : ker.MemSideU

  mtTw : ker.MtTwTie

  om : Formalism.L2.GlobalTheoryTheory.OmegaCompatible D ker.δ

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {ex : Extra D L hT Gi Gl K Y cX}

end GlobalTheory.Core.Cls

end
end
