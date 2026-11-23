module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle064
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle068
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle027
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle022
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle065
public import Development.AbelianVarietyTheory.Counterexamples.HeckeCharacterExamples.PeriodBoundOfPlaceBound
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle022
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle030
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle558
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle034
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle012
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle378
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle574
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle571
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle035
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle037
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle033
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle014
public import Formalism.UnipotentAdelicQuotients.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle429
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle450
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle306
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsWt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemLevelTypeFormsOfUniversalCoeffReading
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle092
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle135
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle056
import Formalism.SharpRestriction.GlobalSchurBounds.QuadraticLogDerivCongr
import Formalism.SharpRestriction.GlobalSchurBounds.Bundle004

@[expose] public section

section



section
set_option genSizeOfSpec false
set_option genInjectivity false
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam
variable {D : D7}
section Real
variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex)
def QAllAlt (PP : Pl D.host.E) : Prop := ∃ t, PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t
structure PackageHypotheses : Prop where
  bot : _root_.GlobalTheory.MiTop.BottomHypotheses W
  lev : _root_.GlobalTheory.MiS.LevelHypothesis W
  ex : (_root_.GlobalTheory.Fam.pk_z W).ExAt
  hTop : ∀ t, LinearMap.range ((_root_.GlobalTheory.Fam.pk_z W).cX.toMap (_root_.GlobalTheory.Fam.pk_z W).prX ∘ₗ ((_root_.GlobalTheory.Fam.pk_z W).HX t).e) =
    MultT (_root_.GlobalTheory.Fam.pk_z W).θ (_root_.GlobalTheory.Fam.pk_z W).MX (levS _ (_root_.GlobalTheory.Fam.pk_z W).βX ((_root_.GlobalTheory.Fam.pk_z W).datXt t)) (levChi _ (_root_.GlobalTheory.Fam.pk_z W).βX ((_root_.GlobalTheory.Fam.pk_z W).datXt t))
  gap : GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D
  fin : Finite W.P.T
  sel : ∀ PP PP', _root_.GlobalTheory.Fam.QAllAlt W PP → _root_.GlobalTheory.Fam.QAllAlt W PP' → (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') → PP = PP'
  aa : ∀ PP : Pl D.host.E, (_root_.GlobalTheory.Fam.QAllAlt W PP ∨ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ∨ ∃ u, (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) →
    ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal
variable {W} {u : D.what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u)
structure FamilyCharacter.RowOK : Prop where
  meas : GeoMeas (_root_.GlobalTheory.Fam.pk_z W) f.g
  last : f.c.VolLast
  x : ∀ j, j ≤ D.R.m → (f.g.x j).Is
  row : ∀ t, (f.row t).Is
  same : ∀ t t', (f.row t).Same (f.row t')
structure FamilyCharacter.ColOK : Prop where
  kom : ∀ t j, j < D.R.m → IsWeilDatumO (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1)) ((f.col t).kom j)
  ker : ∀ t j, j < D.R.m → ∀ α γ, ((f.t t).ker j α γ).Is f.c.ψ f.c.θ (f.c.x j) (f.c.x (j + 1))
  e : ∀ t j α, ∀ g ∈ ((f.col t).e j α).support, g ∈ GfC (Yc D j)
  eT : ∀ t n h β, ∀ g ∈ ((f.col t).eT n h β).support, g ∈ GfC D.sp.X'
  stabK : ∀ t j, j < D.R.m → ∀ ψ ∈ (f.col t).Ram j, (f.t t).K j ψ ∈ (f.col t).Ram (j + 1)
  stabS : ∀ t j, j ≤ D.R.m → ∀ ψ ∈ (f.col t).Ram j, (f.col t).S j ψ ∈ (f.col t).Ram j
structure CommutingVectorTie (v : VCom f.c) : Prop where
  b : ∀ j, v.b j = f.g.b j
  bT : v.bT = f.g.bT ∧ v.NT = f.g.LT
  gP : ∀ p, p ∈ v.gP ↔ ∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)
  tP : ∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal
  moves : ∀ j, j < D.R.m → ∀ P : GlobalTheory.FinPl.Pl D → Prop, (∀ p, P p → p ∉ v.gP) →
    GlobalTheory.FinPl.Moves (Yc D j) (f.g.b j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) (v.N j) P
  movesT : ∀ P, GlobalTheory.FinPl.Moves D.sp.X' f.g.bT (_root_.GlobalTheory.Fam.pk_z W).ΛX f.g.LT P
  Ψ : ∀ j, j + 1 < D.R.m → ∃ o, GlobalTheory.FinPl.CombAt (· ∈ v.gP) o ∧ ∀ P a a', v.Ψ j P a a' = comb f.c.ψ _ _ o
    ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (a * f.g.b j, a' * f.g.b (j + 1)) (pureTensorO f.c.ψ f.c.θ (Yc D j) (Yc D (j + 1))
      (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) ((_root_.GlobalTheory.Fam.pk_z W).vac j) P))
  ΨT : ∀ j h, ∃ o, GlobalTheory.FinPl.CombAt (· ∈ v.gP) o ∧ ∀ P, v.ΨT j h P = comb f.c.ψ _ _ o
    (omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (pureTensorO f.c.ψ f.c.θ (Yc D (j + 1)) D.sp.X'
      (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb (_root_.GlobalTheory.Fam.pk_z W).MX) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) P))
  nz : (∀ j, j + 1 < D.R.m → ∃ P, v.Ψ j P 1 1 ≠ 0) ∧ ∀ j h, ∃ P, v.ΨT j h P ≠ 0
def IsDivisorGlobal (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (j : ℕ) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (Λ : GlobalTheory.FinPl.Lat V)
    (β : GL (Fin V.rank) (Lev.EAf D)) (vac : WO (Yc D j) V → ℂ) (d : WO (Yc D j) V →₀ ℂ) : Prop :=
  GlobalTheory.FinPl.CombAt (fun p => ∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) d ∧
    IsStepVecOf (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D j) V (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart M) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) Λ ((_root_.GlobalTheory.Fam.pk_z W).βY j) β
      (datY _ D.R.r D.R.t j (r_le_Y j) (_root_.GlobalTheory.Fam.pk_z W).Pg ∅ (_root_.GlobalTheory.Fam.complexLevelStructure W) (_root_.GlobalTheory.Fam.pk_z W).chi (fun _ => 1) Frm.B) ((_root_.GlobalTheory.Fam.pk_z W).chi (j + 1)) ∅ (fun _ => 1) vac
      (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ d vac)
def IsDivisorRational (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (t : W.P.T) (j : ℕ) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (Λ : GlobalTheory.FinPl.Lat V)
    (β : GL (Fin V.rank) (Lev.EAf D)) (vac : WO (Yc D j) V → ℂ) (d : WO (Yc D j) V →₀ ℂ) : Prop :=
  GlobalTheory.FinPl.CombAt (fun p => ∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) d ∧
    IsStepVecOf (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D j) V (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart M) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) Λ ((_root_.GlobalTheory.Fam.pk_z W).βY j) β
      (datY _ D.R.r D.R.t j (r_le_Y j) ∅ ((_root_.GlobalTheory.Fam.pk_z W).Q t) (LevelP.triv _ _ _) (_root_.GlobalTheory.Fam.pk_z W).chi ((_root_.GlobalTheory.Fam.pk_z W).xiR t) Frm.B) ((_root_.GlobalTheory.Fam.pk_z W).chi (j + 1))
      ((_root_.GlobalTheory.Fam.pk_z W).Q t) ((_root_.GlobalTheory.Fam.pk_z W).xiR t) vac (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ d vac)
def RationalVectorCondition {t : W.P.T} (w : VTup (f.t t)) : Prop :=
  (∀ j, j + 1 < D.R.m → ∀ d, _root_.GlobalTheory.Fam.IsDivisorRational W t j ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j) d →
    ∀ g, GlobalTheory.FinPl.Vac f.c.ψ _ _ ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) (· ∈ w.Q) g →
      (f.t t).om j (f.g.b j, f.g.b (j + 1)) (comb f.c.ψ _ _ d g) =
        comb f.c.ψ _ _ (w.eQ j) ((f.t t).om j (f.g.b j, f.g.b (j + 1)) g)) ∧
  ∀ j h d, _root_.GlobalTheory.Fam.IsDivisorRational W t (j + 1) (_root_.GlobalTheory.Fam.pk_z W).MX (_root_.GlobalTheory.Fam.pk_z W).ΛX (_root_.GlobalTheory.Fam.pk_z W).βX (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) d →
    ∀ g, GlobalTheory.FinPl.Vac f.c.ψ _ _ ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).ΛX (· ∈ w.Q) g →
      (f.t t).omT j h (f.g.b (j + 1), f.g.bT) (comb f.c.ψ _ _ d g) =
        comb f.c.ψ _ _ (w.eQT j h) ((f.t t).omT j h (f.g.b (j + 1), f.g.bT) g)
structure LocalGroupReading {v : VCom f.c} {n : ℕ} (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg) : Prop where
  idem : ∀ i, Formalism.L2.NTheta.IsIdemAt (G i).q.e (pl i).1 ∧ (G i).q.v = (pl i).1.under (𝓞 D.host.F)
  mu : ∀ i j, 1 ≤ j → j ≤ D.R.m → (ofSplit (G i).q).IsComp (Lift.chrStep (_root_.GlobalTheory.Fam.pk_z W).mu0 (_root_.GlobalTheory.Fam.pk_z W).eta j).1⁻¹ ((G i).S.μ j)
  frame : ∀ i j c (hc : j + c = (G i).s + 1), ∃ e : Ix (Fin D.R.k ⊕ Fin ((G i).s + 1)) (Fin D.R.t) j ≃ Fin (Yc D j).rank,
    GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e ∧ MovedTo (ofSplit (G i).q) (Yc D j) (f.g.b j) ((_root_.GlobalTheory.Fam.pk_z W).βY j)
      ((((G i).FY j c hc).β * (((G i).S.T (Fin D.R.t)).bas j c hc).val).submatrix id
        fun a => stdOrd (Fin D.R.k) (Fin D.R.t) j c hc (e.symm a))
  frameTop : ∀ i, ∃ e : Ix (Fin D.R.k ⊕ Fin ((G i).s + 1)) (Fin D.R.t) ((G i).s + 2) ≃ Fin D.sp.X'.rank,
    GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e ∧ MovedTo (ofSplit (G i).q) D.sp.X' f.g.bT (_root_.GlobalTheory.Fam.pk_z W).βX ((G i).FT.β.submatrix id e.symm)
  lev : ∀ (g : ∀ PP : (_root_.GlobalTheory.Fam.pk_z W).Pg, GL (Fin D.R.r) (kP PP.1)),
    (g ∈ (_root_.GlobalTheory.Fam.complexLevelStructure W).H ↔ ∀ i, ∃ x : (G i).S.P.J, ∀ (a b : Fin D.R.k ⊕ Fin ((G i).s + 1)) (a' b' : Fin D.R.r),
      a'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ a → b'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ b → ∀ z : 𝓞 D.host.E,
        Ideal.Quotient.mk (pl i).1.asIdeal z = (g (pl i)).val a' b' →
        valuation (G i).k ((x : GL (Fin D.R.k ⊕ Fin ((G i).s + 1)) (G i).k).val a b - (ofSplit (G i).q).pr (z : D.host.E)) < 1) ∧
    ∀ (hg : g ∈ (_root_.GlobalTheory.Fam.complexLevelStructure W).H) (x : ∀ i, (G i).S.P.J), (∀ i (a b : Fin D.R.k ⊕ Fin ((G i).s + 1)) (a' b' : Fin D.R.r),
      a'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ a → b'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ b → ∀ z : 𝓞 D.host.E,
        Ideal.Quotient.mk (pl i).1.asIdeal z = (g (pl i)).val a' b' →
        valuation (G i).k ((x i : GL (Fin D.R.k ⊕ Fin ((G i).s + 1)) (G i).k).val a b - (ofSplit (G i).q).pr (z : D.host.E)) < 1) →
      (_root_.GlobalTheory.Fam.complexLevelStructure W).chi ⟨g, hg⟩ = ∏ i, (G i).S.P.lam (x i)
end Real
section True
open GlobalTheory.Mem GlobalTheory.Mem.Col2
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX}
structure ValidRealPackage (W : _root_.GlobalTheory.MiS.RealPackAlt ex) : Prop where
  ok : I.Ok
  pins : Nonempty (TC.Pins B X)
  tw : I.IsTw
  std : Nonempty (I.StdC l Z W.R.T.cols)
  chr : ∀ j : Fin B.R.m, ChrEq ((_root_.GlobalTheory.Fam.pk_z W).mu0 ((j : ℕ) + 1)) (I.C.mu0 j)
  top : _root_.GlobalTheory.Fam.LeadingReadStatement W
end True
end GlobalTheory.Fam
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.GalLoc
theorem twistedAt_atMem_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ _ _ _ _ => ∃ v, TwistedAt (w.D Z) v := by
  intro hL
  refine GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun K B f T _ w Z Wt p0 t nch n xd c _ _ _ => ?_
  obtain ⟨v, hv⟩ := GlobalTheory.Survey.PeriodBoundOfPlaceBound.exists_place (w.D Z) (B.host.g 0) (B.host.g_prime 0)
  have hW := GlobalTheory.Mem.Top.Bl.Model3.type_mem t v 0 hv
  exact ⟨v, (GlobalTheory.Mem.Top.V4.Model.mem_iff t.mu v).1 hW⟩
end GlobalTheory.GalLoc
end
end

section



section
noncomputable section
namespace GlobalTheory.NRows.AtPt
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl
  GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.Fc NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
def OverNEAlt (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) : Prop :=
  ∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.defaultExtension hL K B f T w Z Wt p0 t nch n xd c)
def membershipLocation (P : _root_.GlobalTheory.HeightCounting.Up.LayPAlt hL) : V4.Slot := fun K X f T _ =>
  ∀ w Z Wt p0 t nch n xd c, Nonempty (_root_.GlobalTheory.HeightCounting.defaultExtension hL K X.B f T w Z Wt p0 t nch n xd c) → Nonempty (RXs t) → ColPin w →
    P K X.B f T w Z Wt p0 t nch n c
abbrev WitnessAtPoint (P : _root_.GlobalTheory.HeightCounting.Up.LayPAlt hL) {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : WPt p.s K) : Prop :=
  P K q.B q.f q.T q.w q.Z q.x.Wt _ q.x.what₂ _ q.x.n q.core_data_of_point
theorem lgSlotG_memSlot' {P : _root_.GlobalTheory.HeightCounting.Up.LayPAlt hL} (h : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL P) (Q : V4.Slot) : LargeBaseConditionG KPx Q (_root_.GlobalTheory.NRows.AtPt.membershipLocation P) :=
  EvG.imp h fun _ _ _ _ _ hK => large₂.imp hK fun _ _ _ _ H kp _ _ _ _ _ _ _ _ => H kp
section
variable {N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL} {S : SExt} {Γ : GeoP} {P : _root_.GlobalTheory.HeightCounting.Up.LayPAlt hL}
theorem exists_wPt_entC_atWit_of_heq (hN : _root_.GlobalTheory.NRows.AtPt.OverNEAlt N) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {D : D7}
    (hP : ∀ w Z Wt p0 t nch n xd c, Nonempty (_root_.GlobalTheory.HeightCounting.defaultExtension hL K B f T w Z Wt p0 t nch n xd c) → Nonempty (RXs t) → ColPin w →
      P K B f T w Z Wt p0 t nch n c)
    (e : w.D Z = D) (O : Obj D) {O' : Obj2 (w.D Z)} (hO : HEq (ofObj O) O') (x : Wit (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K w Z O') (hx : EntC x.ker) :
    ∃ q : WPt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K, q.Is D O ∧ EntC q.x.ker ∧ _root_.GlobalTheory.NRows.AtPt.WitnessAtPoint (p := _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) P q := by
  subst e
  obtain rfl := eq_of_heq hO
  exact ⟨⟨B, f, T, w, Z, O, x⟩, rfl, hx, hP w Z _ _ _ _ _ _ x.nx.1 (hN _ _ _ _ _ _ _ _ _ _ _ _ _ x.nx.2) ⟨x.rx⟩ x.pin⟩

theorem exists_wit_pt_alt (hN : _root_.GlobalTheory.NRows.AtPt.OverNEAlt N) (H : WitMv (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}
    {Z : w.Lt}
    (hP : ∀ w Z Wt p0 t nch n xd c, Nonempty (_root_.GlobalTheory.HeightCounting.defaultExtension hL K B f T w Z Wt p0 t nch n xd c) → Nonempty (RXs t) → ColPin w →
      P K B f T w Z Wt p0 t nch n c)
    {O : Obj2 (w.D Z)} (x : Wit (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K w Z O) (hx : EntC x.ker) (Y : Lay (w.D Z)) (hY : layObj Y = O) (p : LedPart K.C Y) :
    ∃ q : WPt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K, q.Is p.pt.D (Obj.ofPt p.pt) ∧ EntC q.x.ker ∧ _root_.GlobalTheory.NRows.AtPt.WitnessAtPoint (p := _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) P q := by
  obtain ⟨y, hy⟩ := H K B f T w Z O x (nPrime p.L) p.ht hx
  exact _root_.GlobalTheory.NRows.AtPt.exists_wPt_entC_atWit_of_heq hN hP (Db.D_setDivZ w Z (nPrime p.L) p.ht) (Obj.ofPt p.pt)
    (hY ▸ heq_of_eq (pointObj_pt p)) y hy

theorem exists_wPt_entC_atWit (hN : _root_.GlobalTheory.NRows.AtPt.OverNEAlt N) (H : WitMv (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) {K : Ctx} (β : BPt K)
    (hβ : β.Is (sAnd (IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) (_root_.GlobalTheory.NRows.AtPt.membershipLocation P))) :
    ∃ q : WPt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K, q.Is β.D β.O ∧ EntC q.x.ker ∧ _root_.GlobalTheory.NRows.AtPt.WitnessAtPoint (p := _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) P q :=
  positionOf_ind (P := GoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) (R := fun K X f T c => _root_.GlobalTheory.NRows.AtPt.membershipLocation P K X f T c →
      ∀ (Y : Lay X.toD7) (_ : layObj Y = c.O) (p : LedPart K.C Y),
      ∃ q : WPt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K, q.Is p.pt.D (Obj.ofPt p.pt) ∧ EntC q.x.ker ∧ _root_.GlobalTheory.NRows.AtPt.WitnessAtPoint (p := _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) P q)
    (fun _ _ _ _ _ _ _ g hP => g.1.elim fun b hb => _root_.GlobalTheory.NRows.AtPt.exists_wit_pt_alt hN H hP (b.wit g.2) hb)
    hβ.1 hβ.2 β.Y β.hY β.p
theorem memSlot_entry_of_atWit (hN : _root_.GlobalTheory.NRows.AtPt.OverNEAlt N) (H : WitMv (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) {r : ∀ D : D7, Obj D → Prop}
    (hr : ∀ K (q : WPt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K), EntC q.x.ker → _root_.GlobalTheory.NRows.AtPt.WitnessAtPoint (p := _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) P q → r (q.w.D q.Z) q.O) {Bd : BdT} (Lk : LkT Bd) :
    RowE (sAnd (IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) (_root_.GlobalTheory.NRows.AtPt.membershipLocation P)) Lk fun _ D O _ _ => r D O :=
  RowE.of_all fun _ K β _ _ _ hβ _ => let ⟨q, a, b, c⟩ := _root_.GlobalTheory.NRows.AtPt.exists_wPt_entC_atWit hN H β hβ; of_is a (hr K q b c)
end
theorem lg1_entry_of_atWit {N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL} {S : SExt} {Γ : GeoP} {P : _root_.GlobalTheory.HeightCounting.Up.LayPAlt hL} (h : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL P) (hN : _root_.GlobalTheory.NRows.AtPt.OverNEAlt N)
    (H : WitMv (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) {r : ∀ D : D7, Obj D → Prop}
    (hr : ∀ K (q : WPt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K), EntC q.x.ker → _root_.GlobalTheory.NRows.AtPt.WitnessAtPoint (p := _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) P q → r (q.w.D q.Z) q.O) {Bd : BdT} (Lk : LkT Bd) :
    Lg1 KPx (IsBuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) (IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) fun U => RowE U Lk fun _ D O _ _ => r D O :=
  linkedBundleProperty_after_largeBaseCoreProperty (_root_.GlobalTheory.NRows.AtPt.lgSlotG_memSlot' h _) (_root_.GlobalTheory.NRows.AtPt.memSlot_entry_of_atWit hN H hr Lk)
end GlobalTheory.NRows.AtPt
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.HeightCounting.Up.PendLayer
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
theorem atMem_mono {p q : _root_.GlobalTheory.HeightCounting.Up.LayPAlt hL} (h : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL p)
    (hpq : ∀ K B f T w Z Wt p0 t nch n c, p K B f T w Z Wt p0 t nch n c → q K B f T w Z Wt p0 t nch n c) : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL q :=
  EvG.imp h fun _ _ _ _ _ hK => large₂.imp hK fun B f T _ H kp w Z Wt p0 t nch n xd c a b d =>
    hpq _ B f T w Z Wt p0 t nch n c (H kp w Z Wt p0 t nch n xd c a b d)
theorem atMem_and' {p q : _root_.GlobalTheory.HeightCounting.Up.LayPAlt hL} (h : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL p) (h' : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL q) :
    _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun K B f T w Z Wt p0 t nch n c => p K B f T w Z Wt p0 t nch n c ∧ q K B f T w Z Wt p0 t nch n c :=
  EvG.imp (EvG.inter h h') fun _ _ _ _ _ hK => large₂.imp (large₂.inter hK.1 hK.2) fun _ _ _ _ H kp w Z Wt p0 t nch n xd c a b d =>
    ⟨H.1 kp w Z Wt p0 t nch n xd c a b d, H.2 kp w Z Wt p0 t nch n xd c a b d⟩
theorem atMem_mono_of_colPin {q : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), w.Lt → Prop}
    (h : EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), q B f T w Z) :
    _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ B f T w Z _ _ _ _ _ _ => q B f T w Z :=
  EvG.imp h fun _ _ _ _ _ hK => large₂.imp hK fun _ _ T _ H kp w Z _ _ _ _ _ _ _ _ _ _ => H kp T w Z
end GlobalTheory.HeightCounting.Up.PendLayer
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.GalLoc
theorem atMem_and' {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p q : _root_.GlobalTheory.HeightCounting.Up.LayPAlt hL} (hp : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL p) (hq : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL q) :
    _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun K B f T w Z Wt p0 t nch n c => p K B f T w Z Wt p0 t nch n c ∧ q K B f T w Z Wt p0 t nch n c := by
  refine (hp.inter hq).imp fun K _ _ _ _ H => ?_
  refine (H.1.inter H.2).imp fun B f T _ H => ?_
  intro hK w Z Wt p0 t nch n xd c hE hX hC
  exact ⟨H.1 hK w Z Wt p0 t nch n xd c hE hX hC, H.2 hK w Z Wt p0 t nch n xd c hE hX hC⟩
theorem atMem_mono {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p q : _root_.GlobalTheory.HeightCounting.Up.LayPAlt hL} (hp : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL p)
    (h : ∀ K B f T w Z Wt p0 t nch n xd c, Nonempty (_root_.GlobalTheory.HeightCounting.defaultExtension hL K B f T w Z Wt p0 t nch n xd c) →
      p K B f T w Z Wt p0 t nch n c → q K B f T w Z Wt p0 t nch n c) : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL q := by
  refine hp.imp fun K _ _ _ _ H => ?_
  refine H.imp fun B f T _ H => ?_
  intro hK w Z Wt p0 t nch n xd c hE hX hC
  exact h K B f T w Z Wt p0 t nch n xd c hE (H hK w Z Wt p0 t nch n xd c hE hX hC)
end GlobalTheory.GalLoc
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.HeightCounting.Up.LocEx
theorem atMem_mono {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p q : _root_.GlobalTheory.HeightCounting.Up.LayPAlt hL} (h : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL p)
    (hpq : ∀ K B f T w Z Wt p0 t nch n c, p K B f T w Z Wt p0 t nch n c → q K B f T w Z Wt p0 t nch n c) : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL q :=
  EvG.imp h fun _ _ _ _ _ hK => large₂.imp hK fun B f T _ H kp w Z Wt p0 t nch n xd c a b d =>
    hpq _ B f T w Z Wt p0 t nch n c (H kp w Z Wt p0 t nch n xd c a b d)
end GlobalTheory.HeightCounting.Up.LocEx
end
end
end

section



section
noncomputable section
namespace GlobalTheory.NRows.AtLayer
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top
  GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
theorem atMem_mono_of_colPin {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {P : Ctx → ∀ B : Base, Fr B.toPre → TwDat B → Prop} {p q : _root_.GlobalTheory.HeightCounting.Up.LayPAlt hL}
    (hP : EvLgG P) (h : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL p)
    (hpq : ∀ K B f T, P K B f T → KPx B f → ∀ w Z Wt p0 t nch n xd c, Nonempty (_root_.GlobalTheory.HeightCounting.defaultExtension hL K B f T w Z Wt p0 t nch n xd c) →
      Nonempty (RXs t) → ColPin w → p K B f T w Z Wt p0 t nch n c → q K B f T w Z Wt p0 t nch n c) : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL q :=
  EvG.imp (EvG.inter hP h) fun _ _ _ _ _ hK => large₂.imp (large₂.inter hK.1 hK.2) fun B f T _ H kp w Z Wt p0 t nch n xd c a b d =>
    hpq _ B f T H.1 kp w Z Wt p0 t nch n xd c a b d (H.2 kp w Z Wt p0 t nch n xd c a b d)
end GlobalTheory.NRows.AtLayer
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.PinLayer

theorem pinAt_of_side_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch}
    (a : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL D cf nch tp) (hG : GlobalTheory.Published.GreenCuspidal) (hT : TypesTrue D.ntypes cf.P cf.W) (hval : ValLL0 D cf)
    (rep' : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (hrep : HEq a.nt.rep rep')
    (hinj : ∀ σ σ', (rep' σ).Iso (rep' σ') → σ = σ') (hE : Elem D) (hcheb : GlobalTheory.RowTie.ChebSplit D.nd)
    (labc : LabConj a.nt.D a.nt.A.wdT)
    (zeta : ∀ k, a.nt.A.grp.ζ k = @GlobalTheory.GLq.LabelDatum.gen _ ⟨a.nt.D.host.g_prime k⟩ (@GlobalTheory.Mem.TypePl.labDat (a.nt.D.host.g k) ⟨a.nt.D.host.g_prime k⟩)) :
    ∃ P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D, _root_.GlobalTheory.HeightCounting.Up.PinnedAtCharacterChoice a P := by
  rcases a with ⟨nt, all, chr_eq, host, frameN, chrN, chrGal, Pq', Pq_over, pq, jE_eq, mt_eq, Pq_eq, low', split, ratIn, ratIn_hL, ratIn_eig, ratIn_θ, depth⟩
  obtain ⟨⟨D0, cf0, jE, A, cg, au, rep, row, low, Pq, S, hLm, eig, θ, Bs, M, C0, tp0, ch, mt, big, L, Sp, Au, ss, heq⟩, pack⟩ := nt
  dsimp only at pack heq hrep labc zeta mt_eq ⊢
  subst heq
  cases pack
  cases hrep
  obtain ⟨Hk, hHk⟩ := _root_.GlobalTheory.FitHecke.heckeOpen_withLoc_alt D0 cf0 jE A low Pq S hLm eig θ Bs M C0 tp0 ch mt hE.star hE.int hE.split hcheb big L Sp Au
  obtain ⟨ty⟩ := _root_.GlobalTheory.HeightCounting.typesOpen_withLoc_alt D0 cf0 jE A low Pq S hLm eig θ Bs M C0 tp0 ch mt hE.star hE.int hE.split hcheb big L Sp Au ss
  obtain ⟨tw⟩ := _root_.GlobalTheory.T.side_multiplicity_character_alt D0 cf0 jE A low Pq S hLm eig θ Bs M C0 tp0 ch mt hE.star hE.int hE.split hcheb big L Sp Au
  obtain ⟨Γ, hΓ, -⟩ := GlobalTheory.T.exists_green_cuspidal_labelling_same_generators hG (withLoc L) (cfL L cf0) { A.grp with } hT zeta
  refine ⟨{ cf := cfL L cf0, C := chL L C0, tp := tpL L tp0, chr := tw.chrN, val := hval, Q_eq := ?Q, T := { A.wdT with }, lab := A.lab, cg := { cg with }, M := mtL L M, H := Hk, au := ?au, rep := rep, rep_inj := hinj, row := ?row, locW_eq := fun i i' σ w => (Au.locW i σ w).trans (Au.locW i' σ w).symm, jE := jE, ty := { ty with grp := Γ }, wd := { A.wd with }, wdOf := Au.wdOf }, ⟨rfl, rfl, HEq.rfl, HEq.rfl, eq_of_heq mt_eq, ?lab, hΓ, ?chiT⟩⟩
  case Q =>
    intro i
    have hm : i ∈ L.X.nd.locs (L.X.nd.j i) (L.X.nd.w i) := (L.X.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩
    exact (Sp.Q_eq _ _ i hm).trans (Sp.Qc_eq _ _)
  case au =>
    intro j h1 h2 π s σ h
    rw [hHk]
    exact au j h1 h2 π s σ h
  case row =>
    intro i
    refine ⟨fun σ s τ h => ?_, fun σ v w hvw Dv hα => ?_⟩
    · exact (congrArg (A.wdT.e s.w) (Au.locW i σ s.w)).trans (row.1 σ s τ h)
    · obtain ⟨α, h1, h2⟩ := row.2 σ v w hvw Dv hα
      exact ⟨α, h1, (Au.satW i σ w).trans h2⟩
  case lab =>
    exact GlobalTheory.T.weilDeligneLabels_all_places_of_fixed_and_conj _ _ A.lab labc
  case chiT =>
    exact A.chiT
end GlobalTheory.PinLayer
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PackageTie2
  GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.Cp
namespace GlobalTheory.CountRow
theorem row_counts_of_ties_alt : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → ∀ (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition),
    Row Q Lk (AtAll fun D _ _ _ => ∃ (X : HidaSetting D) (G : GoodOp X) (ι : D.s.HH ≃ₗᵢ[ℂ] HHX X),
      AutTie D X.B X.pl ∧ RowDictTie X G ι ∧ GlobalTheory.LabPin.LabTie X ι) → _root_.GlobalTheory.Fc.R1.CountsIrreducibilityConstants' Q Lk := by
  intro hSW Q Lk hrow
  obtain ⟨c30, -, h1, -, -, h4⟩ := GlobalTheory.CountConstants.count_constants_of_siegelWeil hSW
  obtain ⟨cIc, hc, H⟩ := GlobalTheory.T.irreducibilityRow_of_concreteAutomorphicData hSW GlobalTheory.rowsFinDim_link
  refine ⟨c30, cIc, h1, hc, hrow.imp fun 𝒜 σ _ hA => ⟨?_, ?_⟩⟩
  · exact Formalism.MainNotions.Pk.Closed.of_class fun Fm _ _ => h4 _ Fm
  · exact H (D3 3 𝒜) (fun Fm hw => hw.2.2.1)
      (Formalism.MainNotions.Pk.Closed.of_class fun Fm _ hw _ => ⟨0, fun x hx _ i => hA Fm (d3_a hw) x hx i⟩)
end GlobalTheory.CountRow
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.HeightCounting.Up

theorem sXd_all_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.ThetaDataExists hL := by
  intro hL
  refine StepW.of_all fun K B f T w _ _ _ P x l => ?_
  have hU : x.m.z.R.toRealDat.LUnif := x.m.intersectionNumber_baseChange.prim.unif
  have hW : x.m.z.R.toRealDat.models_HW := x.m.z.pins.char.base.models.HW
  have H := (GlobalTheory.ExportType.type_of_exportTie l.b.ser.ex hU hW).2.2.2
  exact ⟨⟨fun _ j _ => {_d | j ∈ Finset.Icc 1 (Dof x).R.m}, fun i j b a ha u =>
    sub_eq_zero.1 (LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 (H i j ha b a) u))⟩,
    fun i j b h1 h2 => Set.eq_univ_of_forall fun _ => Finset.mem_Icc.2 ⟨h1, h2⟩⟩
end GlobalTheory.HeightCounting.Up
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR
namespace GlobalTheory.Fc.Ind
theorem base_level_rows_eq_dimension_alt : ∀ (D : D7) (O : Obj D) (c : ℝ) (b : _root_.GlobalTheory.Fc.Ind.PointSummands D O c), _root_.GlobalTheory.Fc.Ind.summandDegreeZero D O c b := by
  intro D O c b
  have h1 : D.what₂.D0 = b.P.S0.D := GlobalTheory.rowSide_card_eq_of_coord O.ex.p0.s D.what₂.onb0 b.P.I.eRR0
  have key : ∀ (Z Z' : DefSub b.P.A3.fam3.amb3) (S : IndefData (b.P.A3.side3 b.P.P0 b.P.ψ0 Z))
      (S' : IndefData (b.P.A3.side3 b.P.P0 b.P.ψ0 Z')), Z = Z' → HEq S S' → S.D = S'.D := by
    intro Z Z' S S' h h'
    subst h
    cases eq_of_heq h'
    rfl
  have h2 := key _ _ _ _ b.B.Q.zs b.B.Q.s0
  have h3 := b.B.Q.zs
  unfold _root_.GlobalTheory.Fc.Ind.summandDegreeZero
  rw [h1, ← h2, ← h3]
  rfl
end GlobalTheory.Fc.Ind
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc
namespace GlobalTheory.Fc.R1.ZLAt
theorem lPrj_surj_at_alt {D : D7} {O : Obj D} {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition D O c) (k : Fin D.R.m) :
    Function.Surjective (Formalism.L2.DIV.lPrj D b.P.A3.A b.P.P0 b.P.ψ0 (b.P.A3.fam3.toSub2 b.P.Zs) k b.P.A3.A.μ0).mulVec :=
  GlobalTheory.Mem.LiftProjOnto.lPrj_surjective D b.P.Gp b.P.Pl0 b.P.T b.P.A3.A b.P.P0 b.P.ψ0 (b.P.A3.fam3.toSub2 b.P.Zs) k
    b.P.A3.A.μ0 _ _ _ b.C.ok1.ok2 (b.P.tied.div.mt.forms k b.P.A3.A.μ0)
theorem zL_of_hPA : ∀ (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition), _root_.GlobalTheory.Fc.R1.SlotPrimitivityCondition Q Lk → _root_.GlobalTheory.Fc.R1.SlotZeroLocusCondition Q Lk := by
  intro Q Lk _
  refine Row.of_sel fun 𝒜 σ _ => ?_
  refine ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ hc => ⟨0, fun x hx _ _ i k => ?_⟩⟩⟩
  exact _root_.GlobalTheory.Fc.R1.ZLAt.lPrj_surj_at_alt (σ Fm (GlobalTheory.Cp.d3_a hc) x hx i) k
end GlobalTheory.Fc.R1.ZLAt
end
end
