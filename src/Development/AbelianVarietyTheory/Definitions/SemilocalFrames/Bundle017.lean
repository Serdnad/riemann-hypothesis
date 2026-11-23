module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle016
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle045
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle015
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

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.UG NumberField IsDedekindDomain Matrix Formalism.L2.SG.HidaSetting Formalism.L2.SG.ColDict
open Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct

namespace GlobalTheory.St.G.LinkCheck

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
  (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F)

theorem embA_rat (hι : GlobalTheory.St.IsAdeleIso X ιA) (x : Fin (D.R.N 0) → D.host.E) :
    embA X wt ιA (fun j => inclE (F := D.host.F) (Ad D.host.F) (x j)) =
      incl X.B.I (X.crd (∑ j, x j • qFr wt j)) := by
  have h1 : ∀ a : D.host.E, ιA.symm (inclE (F := D.host.F) (Ad D.host.F) a) =
      inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm a) := by
    intro a
    rw [RingEquiv.symm_apply_eq, hι.1, RingEquiv.apply_symm_apply]
  funext i
  simp [embA, qA, incl, HidaSetting.crd, crdOf, h1, Finset.sum_apply]

end GlobalTheory.St.G.LinkCheck

end
end

section

noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc

namespace GlobalTheory.Unfold

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev GV (D : D7) : Type := (VS D).V ≃ₗ[D.host.E] (VS D).V

abbrev LV (D : D7) : Type := Submodule (𝓞 D.host.E) (VS D).V

def Adapt {T : D.host.E} (g : GV D) (F G : LFlag (D.sp.Y 0) D.R.rS T) : Prop :=
  g ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧ ∀ a : Fin (D.R.rS + 1), g (frame F a) - frame G a ∈ Xflag G a.val

def Aut0 {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (Λ : LV D) : Set (GV D) :=
  {a | Adapt a F F ∧ Formalism.HermitianLatticesTheory.gmap a Λ = Λ}

section Base

variable {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T')

def H0 : Set (GV D) :=
  {h | h ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧ (∀ a, h (frame F a) = frame F a) ∧ ∀ a, h (frame F' a) = frame F' a}

def gdat (Λ : LV D) : LV D × LV D × Set ((VS D).V × (VS D).V) :=
  (Lsub Λ F, Lsub Λ F',
    {p | ∃ l' ∈ Lrep Λ F', ∃ l ∈ Lrep Λ F, p.1 - l' ∈ Xsp F' ∧ p.2 - l ∈ Xsp F ∧ l - l' ∈ NgX Λ (gS D) F F'})

def LRel (Λ₁ Λ₂ : LV D) : Prop := ∃ h ∈ H0 F F', gdat F F' (Formalism.HermitianLatticesTheory.gmap h Λ₁) = gdat F F' Λ₂

def stabL (Λ : LV D) : Set (GV D) := {h | h ∈ H0 F F' ∧ gdat F F' (Formalism.HermitianLatticesTheory.gmap h Λ) = gdat F F' Λ}

end Base

def KeyEq {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') (Λ : LV D) (γ₁ γ₂ : GV D) : Prop :=
  (∃ n ∈ NRat F, ∃ n' ∈ NRat F', γ₂ = n * γ₁ * n') ∧
    IotaCompat Λ F (mapLF γ₁ F') (mapLF γ₂ F') (γ₂ * γ₁⁻¹) (gS D)

section Local

variable (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS)

def Ext (p : PlF D) (g : GV D) (g' : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) : Prop := ∀ x, g' (baseChange₂ D p x) = baseChange₂ D p (g x)

def Based (Tn T'n : ℕ) (F : LFlag (D.sp.Y 0) D.R.rS (Tn : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (T'n : D.host.E)) : Prop :=
  ∀ p, (FP p).A.f = (fun a => frFac Z.δ p a • baseChange₂ D p (frame F a)) ∧
    (FP p).B.f = (fun a => frFac Z.δ p a • baseChange₂ D p (frame F' a)) ∧
    (FP p).A.T = (Tn : (D.s.atP p).Fp) ∧ (FP p).B.T = (T'n : (D.s.atP p).Fp)

abbrev Dat : Type := ∀ p : PlF D, LocNG.Datum (FP p)

variable {Z FP}

def LocOver (Λ : LV D) (y : Dat Z FP) : Prop :=
  Submodule.IsLattice D.host.E Λ ∧
    ∀ p, ∃ τ : Loc.Term (Vp D p) (Z.M p) D.R.rS, LocNG.IsTermOver (FP p) (y p) τ ∧ τ.abelian₂ = lattice₂ D Z.M p Λ

def RMoves (h : GV D) (y y' : Dat Z FP) : Prop :=
  ∀ p, ∃ g', Ext p h g' ∧ LocNG.Datum.Moves g' (y p) (y' p)

def InGen (d y : Dat Z FP) : Prop :=
  (∀ p, LocNG.Datum.Rel (d p) (y p)) ∧ {p | y p ≠ d p}.Finite

variable {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T')

def GRel (y y' : Dat Z FP) : Prop := ∃ h ∈ H0 F F', RMoves h y y'

def stabY (y : Dat Z FP) : Set (GV D) := {h | h ∈ H0 F F' ∧ RMoves h y y}

def massA (d : Dat Z FP) : ℝ≥0∞ :=
  ∑' o : Quot (GRel (Z := Z) (FP := FP) F F'), if InGen d o.out then (((stabY F F' o.out).encard : ℝ≥0∞))⁻¹ else 0

end Local

section Terms

variable {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word}
  (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))

def TG (t : TauC Y u u') (Λ : LV D) : Prop :=
  ∃ g, Adapt g (lf D (X.Fu u)) F ∧ Adapt g t.frame F' ∧ Λ = Formalism.HermitianLatticesTheory.gmap g t.lam

def key (t : TauC Y u u') := ((Y.tO u u').rowOf t, nmlOf Y u u' t)

def ClsRow {Cl : Type} (TS : Set (TauC Y u u')) (cls : TauC Y u u' → Cl) : Prop :=
  ∀ t ∈ TS, ∀ t' ∈ TS, nmlOf Y u u' t = nmlOf Y u u' t' →
    (cls t = cls t' ↔ (Y.tO u u').rowOf t = (Y.tO u u').rowOf t')

def LocClosed (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (TS : Set (TauC Y u u')) : Prop :=
  ∀ t t' Λ Λ', TG F F' t Λ → TG F F' t' Λ' →
    (∀ p, ∃ h ∈ (FP p).UW0, LocNG.img h (lattice₂ D Z.M p Λ) = lattice₂ D Z.M p Λ') → t ∈ TS → t' ∈ TS

end Terms

end GlobalTheory.Unfold
end
end

section

noncomputable section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc
namespace GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Obj
variable {D : D7} {X : HidaSetting D}

def DbL (D : D7) (j : ℕ) (δ : ℕ → D.host.E) : ℝ := ∏ l ∈ k2ends D j δ, ((Nloc (ddS D) D.R.rS l (δ l) : ℚ) : ℝ)

def AmpAt (large₂ : SizeData₂ D) (Y : Full X) (u : D.what₂.Word) (CH Cs C : ℝ) : Prop :=
  ∀ t ∈ relSet Y u, ‖(Y.tO u u).vec t‖ ≤
    Formalism.L2.SG.TermOp.wt t * Real.sqrt (dpiC X u) * (omT t * k2a large₂ CH Cs C (jT t) (labT t))

def PairsAt (large₂ : SizeData₂ D) (Y : Full X) (u : D.what₂.Word) (CH Ch Cp : ℝ) : Prop :=
  ∀ j' ∈ Finset.Icc 1 D.R.rS, ∀ j'' ∈ Finset.Icc 1 D.R.rS, ∀ (δ' δ'' : ℕ → D.host.E) (S : Finset (GTu Y u × GTu Y u)),
    (∀ p ∈ S, p ∈ (Y.tO u u).allPairs (relSet Y u) ∧ jT p.1 = j' ∧ jT p.2 = j'' ∧ labT p.1 = δ' ∧ labT p.2 = δ'') →
    ∑ p ∈ S, (Formalism.L2.SG.TermOp.wt p.1 * Formalism.L2.SG.TermOp.wt p.2) * (omT p.1 * omT p.2) ≤
      massC Y u * (k2e large₂ CH Ch Cp j' δ' * k2e large₂ CH Ch Cp j'' δ'')
end Obj

def TypeP : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, 0 < cb → 0 < cT → ∃ CH Ch Cp : ℝ, 0 ≤ CH ∧ 0 ≤ Ch ∧ 0 ≤ Cp ∧ ∀ Cs : ℝ, Cp + 4 ≤ Cs →
    ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C → ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
      ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.BasicNotions.Ties D →
        Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → ConcTie X Y → TypeAt large₂ Y u CH Cs C Ch Cp

def AmpP : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, 0 < cb → 0 < cT → ∃ CH : ℝ, 0 ≤ CH ∧ ∀ Cs : ℝ, 0 ≤ Cs →
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C → ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
      ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.BasicNotions.Ties D →
        Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → ConcTie X Y → AmpAt large₂ Y u CH Cs C

def PairsP : Prop :=
  ∀ Cg cb Cw cT CT C0 CH : ℝ, 0 ≤ CH → ∃ Ch Cp : ℝ, 0 ≤ Ch ∧ 0 ≤ Cp ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → ConcTie X Y → PairsAt large₂ Y u CH Ch Cp

def NFExC : Prop :=
  ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Std D large₂ → ∀ t ∈ relSet Y u,
    ∃ N, AdT t N ∧ N.j = jT t ∧ N.T = Tu D u

def LabC : Prop :=
  ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Std D large₂ → ∀ (t : GTu Y u) N, AdT t N →
    N.j = jT t ∧ N.T = Tu D u ∧ N.Del = k2Del D (jT t) (labT t) ∧ N.Db = DbL D (jT t) (labT t) ∧
      GlobalTheory.DegAsm.lab (F0 X u) (Ft t) (jT t) = fun l => star (labT t l)

def PerRowC : Prop :=
  ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Std D large₂ →
    ∀ (W : Submodule D.host.E (VS D).V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W), GlobalTheory.DegAsm.IsEmb (F0 X u) HW W.subtype →
    ∀ (Λ : Submodule (𝓞 D.host.E) (VS D).V) (j' j'' : ℕ) (δ' δ'' : ℕ → D.host.E) (S : Finset (GTu Y u × GTu Y u)),
      (∀ p ∈ S, p ∈ (Y.tO u u).allPairs (relSet Y u) ∧ p.1.lam = Λ ∧ jT p.1 = j' ∧ jT p.2 = j'' ∧ labT p.1 = δ' ∧
        labT p.2 = δ'') →
      ENNReal.ofReal (∑ p ∈ S, wRow D (X.Fu u) p.1.lam' * (omT p.1 * omT p.2)) ≤
        ∑ x ∈ Finset.Icc 1 ⌊k2Del D j' δ'⌋₊, ∑ x' ∈ Finset.Icc 1 ⌊k2Del D j'' δ''⌋₊,
          (((GlobalTheory.DegCnt.Trip HW (gS D) (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ) D.R.rS x x').encard : ℕ∞) : ℝ≥0∞) *
            ENNReal.ofReal (GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j' δ') (DbL D j' δ') (NT D u) x *
              GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j'' δ'') (DbL D j'' δ'') (NT D u) x')

def ProdC : Prop :=
  ∀ Cs : ℝ, 0 ≤ Cs → ∃ C₁ : ℕ, 1 ≤ C₁ ∧ ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (C : Choice X 1)
    (CH : ℝ), Std D large₂ → 0 ≤ CH → 40 * D.R.rS ^ 4 ≤ D.R.k → 5 * D.R.rS ≤ D.R.k → ∀ t ∈ relSet Y u, ∀ hj : jT t ≤ D.R.rS, 1 ≤ jT t →
    ∃ (De : D.what₂.Tau → ℝ) (P : ℝ), 0 < P ∧ k2Del D (jT t) (labT t) = P ^ 2 ∧
      (∀ τ, GlobalTheory.Amp.DeOK D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u τ) (gamT C t τ) (De τ)) ∧
      ∏ τ, GlobalTheory.Amp.degBd D.R.k D.R.rS (jT t) (C₁ * D.R.k * D.R.rS) (H1C large₂ CH) (De τ)
          (GlobalTheory.Amp.Dj D.R.k D.R.rS hj (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u τ) (gamT C t τ))
          (GlobalTheory.Amp.sgV D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u τ) (gamT C t τ) (H1C large₂ CH)) ≤
        (16 * Real.pi * Real.exp 1 / D.R.k) ^ (jT t * (D.R.k - 1 - jT t) * D.R.f) * (P ^ (D.R.k - 1 - jT t))⁻¹ *
          (8 * D.R.rS * H1C large₂ CH) ^ (80 * D.R.rS ^ 4 * D.R.f) * k2S D (H1C large₂ CH) (jT t) (labT t) ^ (-(Cs * D.R.k))
end GlobalTheory.TypeAsm
end
end
