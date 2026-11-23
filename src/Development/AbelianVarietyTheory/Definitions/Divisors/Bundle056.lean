module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle337
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle033
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle039
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle011
public import Formalism.LocalToGlobal.IndefiniteReal.RealRecPins
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NMjT
public import Formalism.LocalToGlobal.Divisibility.PsiWeilOfAbsNorm
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
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
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.ConstRatio (Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.SqTower

variable {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData Lc sc}

abbrev TriG (G : GridData Lc sc) (i j : Fin D.R.m) :=
  Tri T (G.V (.grid (i + 1) (j + 1))) (G.V (.grid i j)) (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j)))

def TopGrid (W : G.Weil) (i j : Fin D.R.m) (X : TriG G i j) : Prop :=
  X.rA.Λ = G.Λ (.grid (i + 1) (j + 1)) ∧ X.rA'.Λ = G.Λ (.grid i j) ∧
    X.rW.Λ = GlobalTheory.Doubling.sumLat finSumFinEquiv (G.Λ (.grid i (j + 1))) (G.Λ (.grid (i + 1) j)) ∧
    X.rA.s = W.cart (.grid (i + 1) (j + 1)) ∧ X.rA'.s = W.cart (.grid i j) ∧
    ∀ (AV : Fr (G.V (.grid i (j + 1)))) (AV₁ : Fr (G.V (.grid (i + 1) j))), IsGridFr W _ AV → IsGridFr W _ AV₁ →
      X.rW.s = (frSum AV AV₁).cart

def RegConst (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (c : ℂ) : Prop :=
  ∀ M : Vol G, M.Is t → ∀ Θ Θ', IsMatched B t ρ i j Θ Θ' → ∀ g g₁, ∃ z, zdeg z ≠ 0 ∧ SquareConv W M Θ Θ' z g g₁ ∧
    zdeg z * ∫ u in M.fd _, kerBig W Θ g g₁ u ∂M.ν _ = c * ∫ u in M.fd _, translates z (kerSmall W Θ' g g₁) u ∂M.ν _

end GlobalTheory.SqTower

end
end

section

noncomputable section

namespace GlobalTheory.DefPt

open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.Frames
  GlobalTheory.CompHt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical

section Point

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

abbrev Mats (Dw : Datum H) (S : Type) : Type := ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S

def part (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → ℕ := fun τ i => a (τ, i)

def Reads (Z : Comp Xo c) (y₀ : FrPt Xo c c.F) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (x : TIdx (part Dw a) → c.F) (f : Rul Xo c) :
    Prop :=
  f ∈ suppOn Z ∧ ∀ (S : Type) [CommRing S] [Algebra c.F S] (z y : FrPt Xo c S) (Y : Mats Dw S) (s : S),
    (∀ τ, IsUnit (Y τ).det) → IsUnit s → FrMap (Algebra.ofId c.F S) y₀ z → FrChg (fun τ => (Y τ)ᵀ) s z y →
      evR Xo c f y = s ^ n * tval (part Dw a) (fun I => algebraMap c.F S (x I)) Y

def LocFr (y₀ : FrPt Xo c c.F) (w : HeightOneSpectrum (𝓞 c.F)) (a : c.F) (B : Mats Dw c.F) : Prop :=
  a ≠ 0 ∧ (∀ τ, (B τ).det ≠ 0) ∧
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa w T.V io e → letI := io.toAlgebra
      ∀ y z : FrPt Xo c T.Fr, Integral T io y → FrMap (Algebra.ofId c.F T.Fr) y₀ z → y.x = z.x →
        ∃ (Y : Mats Dw T.V) (u : T.Vˣ), (∀ τ, IsUnit (Y τ).det) ∧
          FrChg (fun τ => ((B τ).map io * (Y τ).map (algebraMap T.V T.Fr))ᵀ) (io a * algebraMap T.V T.Fr u) z y

def ArchFr (y₀ : FrPt Xo c c.F) (σ : c.F →+* ℂ) (N : ℝ) (X : Mats Dw ℂ) : Prop :=
  0 < N ∧ (∀ τ, (X τ).det ≠ 0) ∧
    ∀ z y : FrPt Xo c (CAt σ), FrMap (Algebra.ofId c.F (CAt σ)) y₀ z → FrChg (S := CAt σ) (fun τ => (X τ)ᵀ) 1 z y →
      GlobalTheory.LamT.IsMetric y N fun _ => 1

structure PtData (Z : Comp Xo c) : Type where

  y₀ : FrPt Xo c c.F
  on : LiesOn Z y₀
  only : ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), LiesOn Z y → y.x = spMap (algebraMap c.F S) ≫ y₀.x

  a : HeightOneSpectrum (𝓞 c.F) → c.F

  B : HeightOneSpectrum (𝓞 c.F) → Mats Dw c.F
  loc : ∀ w, LocFr y₀ w (a w) (B w)
  fin : {w | ¬ (a w = 1 ∧ B w = 1)}.Finite

  N : (c.F →+* ℂ) → ℝ

  X : (c.F →+* ℂ) → Mats Dw ℂ
  arch : ∀ σ, ArchFr y₀ σ (N σ) (X σ)

namespace PtData

variable {Z : Comp Xo c} (P : PtData Z)

def degLie (τ : E →+* ℂ) : ℝ := detDeg (fun w => P.B w τ) fun σ => P.X σ τ

def degTh : ℝ := lineDeg (fun σ => (Real.sqrt (P.N σ))⁻¹) fun w => (vAdd w (P.a w) : ℝ)

def matA (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (w : HeightOneSpectrum (𝓞 c.F)) :
    Matrix (TIdx (part Dw a)) (TIdx (part Dw a)) c.F := fibA (part Dw a) (P.a w ^ n) (P.B w)

def matY (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (σ : c.F →+* ℂ) :
    Matrix (TIdx (part Dw a)) (TIdx (part Dw a)) ℂ := fibY (part Dw a) ((Real.sqrt (P.N σ))⁻¹ ^ n) (P.X σ)

end PtData

variable {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ)

def FibreAt (Z : Comp Xo c) (G : WTZ E) (s : ℝ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (_ : Nonempty ι) (L : Submodule (𝓞 c.F) (ι → c.F))
    (Y : (c.F →+* ℂ) → Matrix ι ι ℂ) (φ : (ι → c.F) →ₗ[c.F] Rul Xo c),
    Submodule.IsFullLattice c.F L ∧ (∀ σ, (Y σ).det ≠ 0) ∧ s ≤ slope_sq (matNorm Y) L / 2 ∧ Function.Injective φ ∧
    LinearMap.range φ = cuspOn U Z G ∧ (∀ x ∈ L, ∀ w, ∀ v ∈ valSet Xo c (algCls Xo c) w, 0 ≤ v (φ x)) ∧
    ∀ σ x, ∀ z ∈ framesOn (U (goodOf c σ)) Z, homN (U (goodOf c σ)) ξ G (φ x) z ≤ matNorm Y σ x

def defBound (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (c₁ : ℝ) : ℝ :=
  (∑ τ : Psi H, (((size (part Dw a τ.1) : ℝ) / Dw.p + (n : ℝ) / 2) * c₁ - Real.log (dim (part Dw a τ.1)) / 2)) +
    (n : ℝ) * ((Fintype.card (Psi H) : ℝ) * Dw.p) * (Real.log (2 * Real.pi) / 4 - GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E / 2)

structure DefCase : Prop where
  q : Dw.q = 0
  p : 1 ≤ Dw.p
  good : ∀ p : ℕ, p.Prime → l.GoodAt p
  A : l.A = 1
  geo : FnAlgClosed (Xo := Xo) (c := c)
  unf : ∀ σ, GoodEmb c σ → IsUnf (U σ)
  xi : ∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = ξ


variable (Xo c) in
def FreePt {G : Type} [Group G] (lev : G → (Dw.La →ₗ[𝓞 E] Dw.La) × (Dw.La →ₗ[𝓞 E] Dw.La)) : Prop :=
  ∀ (g : G) (k : Type) [Field k] [Algebra c.F k] (y y' : FrPt Xo c k), levR (lev g) y y' → y'.x = y.x → g = 1

end Point

section Eigen

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) {G : Type} [Group G]
  (lev : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La)) (χ : G →* (c.F)ˣ)


set_option synthInstance.maxHeartbeats 400000 in
def eigSub : Submodule c.F (Rul Xo c) :=
  ⨅ g : G, LinearMap.ker (actLev (Xo := Xo) c lev g - ((χ g : (c.F)ˣ) : c.F) • (LinearMap.id : Rul Xo c →ₗ[c.F] Rul Xo c))

def eigLat (W : WTZ D.host.E) : Submodule (𝓞 c.F) (cuspW Xo c U W) :=
  latW U W ⊓ ((eigSub lev χ).comap (cuspW Xo c U W).subtype).restrictScalars (𝓞 c.F)

end Eigen

end GlobalTheory.DefPt

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.EX GlobalTheory.EX.OB

namespace GlobalTheory.Fc.Ind

attribute [local instance] Formalism.BasicNotions.Host.cmStar

protected abbrev zsc {D : D7} {O : Obj D} (P : RowSideFamily O.ex) (Del h0 : ℕ) (c : ℝ) :
    DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3 :=
  GlobalTheory.Fc.zsc P Del h0 c


set_option genInjectivity false in
set_option genSizeOfSpec false in
structure Part (D : D7) (O : Obj D) (c : ℝ) : Type 1 where
  R : Formalism.L2.RecT O.ex
  S : Formalism.L2.SG.SpectralTiesReal.STiesR R
  P : RowSideFamily O.ex
  pin : RowSideDetermined R.T P
  DH : {p : ℕ × ℕ // D.s.Del = (p.1 : ℚ) ∧ O.L.etaSz = (D.R.m : ℝ) * (p.2 : ℝ)}
  Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)
  Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)
  ok1 : P.A3.fam3.Ok3 1
  B : RealTB R P Dcf Spf (GlobalTheory.Fc.zsc P DH.1.1 DH.1.2 c) S
  Rr : RealRec B.Q
  psi : PsiPPTie D P.P0 P.ψ0 P.Ps P.ψs P.I.eG
  pins : RealPins B.Q
  muDef : ∀ C CH : ℝ, (B.Q.Rl.toCx3 B.Q.F).MuDef B.Q.F.cr (B.Q.Rl.num B.Q.F C CH) B.Q.Rl.mu
  recPins : RealRecPins pins Rr

def PFire : BdP Part := fun _ _ _ b =>
  b.B.Q.Rl.toRealDat.ExAt ∧ JEvBar b.B.T b.B.Q.Rl.toRealDat b.B.κ ∧ GeoAct b.B.T b.B.Q.Rl.toRealDat b.B.κ b.B.v₀ ∧
    EvInj b.B.T b.B.Q.Rl.toRealDat b.B.v₀

def PRB : BdP Part := fun _ _ _ b => RowsB b.B

def PNmj : BdP Part := fun _ O _ b => NX.NMjT b.B.Q b.B.Q.cG b.B.Q.Sx b.B.Q.nexp O.ex.nch

def L3 (C CH : ℝ) : BdP Part := fun _ _ _ b => ((b.B.Q.Rl.toCx3 b.B.Q.F).data b.B.Q.F.cr false).L3 (b.B.Q.Rl.num b.B.Q.F C CH)

def ON (C CH : ℝ) : BdP Part := fun _ _ _ b => ((b.B.Q.Rl.toCx3 b.B.Q.F).data b.B.Q.F.cr false).ON (b.B.Q.Rl.num b.B.Q.F C CH)

def L6 (C CH : ℝ) : BdP Part := fun _ _ _ b => ((b.B.Q.Rl.toCx3 b.B.Q.F).data b.B.Q.F.cr true).L6 (b.B.Q.Rl.num b.B.Q.F C CH)

def FUN (C CH : ℝ) : BdP Part := fun _ _ _ b => ((b.B.Q.Rl.toCx3 b.B.Q.F).data b.B.Q.F.cr false).FUN (b.B.Q.Rl.num b.B.Q.F C CH)

variable {Bd : BdT}

def Ev {𝒜 : FamClass} (σ : RawSel Bd 𝒜) {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (q : BdP Bd) : Prop :=
  ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, q _ _ _ (σ Fm hc x hx i)

def EvW (q : BdP Bd) (𝒜 : FamClass) (σ : RawSel Bd 𝒜) : Prop :=
  Closed (W3 𝒜) fun Fm _ => ∀ hc : W3 𝒜 Fm, Ev σ Fm (w3_a hc) q

def EvWC (prem : ∀ {eps : ℝ}, FamP eps → Prop) (q : ℝ → ℝ → BdP Bd) (𝒜 : FamClass) (σ : RawSel Bd 𝒜) : Prop :=
  Closed (W3 𝒜) fun Fm CH => ∀ hc : W3 𝒜 Fm, prem Fm → ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ C, C0 ≤ C → Ev σ Fm (w3_a hc) (q C CH)

theorem ev_of_atAll {𝒜 : FamClass} {σ : RawSel Bd 𝒜} {q : BdP Bd} (h : AtAll q 𝒜 σ) {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) :
    Ev σ Fm hc q := ⟨0, fun x hx _ i => h Fm hc x hx i⟩

end GlobalTheory.Fc.Ind


end
end

section

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal

namespace GlobalTheory.ResidueEisenstein

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def ScalesBy (σ : E →ₐ[F] E) {n k : ℕ} (J : Matrix (Fin n) (Fin n) E) (X : Matrix (Fin n) (Fin k) E) (p : GAd σ J)
    (β : GL (Fin k) (AF F ⊗[F] E)) : Prop := (matHom _ σ J p).1 * adMat F X = adMat F X * β.1

structure DataJ (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ} (X Y : Matrix (Fin n) (Fin (r + 1)) E)
    (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ) : Prop where
  cm : IsCMExt F E σ
  herm : IsHermND σ J
  witt : IsWittFrame σ J X Y
  lat : Submodule.IsFullLattice E L
  iwa : ∀ g, ∃ p β, ScalesBy σ J X p β ∧ ∃ k ∈ levelAll σ J L a, g = p * k
  ht : ∀ p β, ScalesBy σ J X p β → ∀ k ∈ levelAll σ J L a, h (p * k) = absE F E (Matrix.GeneralLinearGroup.det β)

def IsRepsJ (σ : E →ₐ[F] E) {n k : ℕ} (J : Matrix (Fin n) (Fin n) E) (X : Matrix (Fin n) (Fin k) E) (T : Set (ratPts σ J)) :
    Prop :=
  ∀ γ : ratPts σ J, ∃! t, t ∈ T ∧ ∃ β, ScalesBy σ J X (γ * t⁻¹ : ratPts σ J).1 β

structure IsFlowJ (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ} (X Y : Matrix (Fin n) (Fin (r + 1)) E)
    (b : ℝ → GAd σ J) : Prop where
  cont : Continuous b
  add : ∀ s t, b (s + t) = b s * b t
  onX : ∀ t, ∃ β, ScalesBy σ J X (b t) β ∧ (absE F E (Matrix.GeneralLinearGroup.det β) : ℝ) = Real.exp t
  mem : ∀ t, b t ∈ GlobalTheory.StdPar.levi σ J X Y {Fin.last r}
  comm : ∀ t, ∀ m ∈ GlobalTheory.StdPar.levi σ J X Y {Fin.last r}, b t * m = m * b t

end GlobalTheory.ResidueEisenstein

end
end
