module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RootsOfUnityRingLeWittIntegers
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle031
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle402
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle034
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.OntoAlong
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle043
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle017
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NHkRow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle029
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle551
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSameData
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle066
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle033
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle054
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle048
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle055
public import Formalism.LocalToGlobal.Bundle001
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle056
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.EtaClosed
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle316
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowRatW
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Formalism.LocalToGlobal.IndefiniteRealisationChoice
import Formalism.SharpRestriction.GlobalSchurBounds.QuadraticLogDerivCongr
import Formalism.SharpRestriction.GlobalSchurBounds.Bundle004

@[expose] public section

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
noncomputable section
namespace GlobalTheory.HeightCounting.FitTwExp

theorem exists_twOpen_expRel_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D' : D7) (b : _root_.GlobalTheory.HeightCounting.NormChoiceConstructed hL D'), Elem b.D → GlobalTheory.RowTie.ChebSplit b.D.nd → ∃ Tw : TwOpen (withLoc b.L) (chL b.L b.C) (cfL b.L b.cf) (tpL b.L b.tp) (mtL b.L b.M) b.low, ExpRel b.L b.Bs.exp Tw.exp := by
  intro hL D' b hE hC
  obtain ⟨Tw⟩ := _root_.GlobalTheory.HeightCounting.FitTw.nonempty_twOpen_alt b.D b.cf b.jE b.A b.low b.Pq b.S b.hL b.eig b.θ b.Bs b.M b.C b.tp b.ch b.mt hE.star hE.int hE.split hC b.big b.L b.Sp b.Au
  refine ⟨{ Tw with exp := GlobalTheory.HeightCounting.FitTw.expL b.L b.Bs.exp, ch := GlobalTheory.HeightCounting.FitTw.chSideL b.Sp b.ch }, ?_⟩
  exact
    { tau := fun h => h
      pl := fun _ _ _ _ _ _ _ _ _ => rfl
      reads := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => h }
end GlobalTheory.HeightCounting.FitTwExp
end
end
end

section



section
noncomputable section
namespace GlobalTheory.HeightCounting
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice _root_.Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
  Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option genInjectivity false
set_option genSizeOfSpec false

structure HeightCountingBaseData (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (cf : CharFrame D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) : Type 1 where
  host : HostTied D
  jE : D.host.E →+* Qb
  frame : ∀ x, jE x = host.fr.j x
  A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE
  cg : _root_.GlobalTheory.HeightCounting.CGTrueT hL D A.wdT
  au : _root_.GlobalTheory.HeightCounting.AutomorphicSideRealised hL D A.wdT A.au
  row : _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL D rep (fun σ w => A.wdT.e w (A.row.locR σ w)) A.row.satR
  fr : OmFrame D
  fr_jE : fr.jE = jE
  pht : PhtOn A.wd fr fun _ _ _ _ => True
  depth : RowDepth D rep
  elem : Elem D
  val : ValLL0 D cf
  labc : LabConj D A.wdT
  zeta : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; A.grp.ζ k = (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen
  omax : Function.Injective D.what₂.OtoLL ∧ ∃ F : Subfield D.what₂.LL, ∀ x, x ∈ D.what₂.OtoLL.range ↔ x ∈ F ∧ IsIntegral ℤ x
section Rows
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {C : Formalism.L2.Pj.CoreJ D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat3 D A3 C.Q.c.F}
  {F : Face3 D A3} {X0 : BaseLevelRowSide D} (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) {cf : CharFrame D}
variable {Y cG}
structure SettingsFormsData (a : _root_.GlobalTheory.HeightCounting.HeightCountingBaseData hL D cf (repOf Y)) (n : InRat Y cG)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) : Type 1 where
  Bs : SideB D cf a.A.row (lowAll D) Pq n.S n.In.hL n.In.eig n.In.θ
  Sb_le : ∀ i, n.In.Sb ⊆ D.ntw.S0 i
  rootsOfUnityRing_le_wittIntegers : ∀ i, OverSet D (D.ntw.S0 i) (insert (D.ntw.l i) (lowAll D))
  lam : ∃ Z : GlobalTheory.LamTie.LamDat D, Z.Ok ∧ Z.Teich ∧ Z.C = cf ∧ Z.q0 = AbsolutelyIrreducibleSpan.q0 D ∧ GlobalTheory.LamTie.IsLamTieFull D.ntw Z
variable (g : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1)
structure SeriesData (a : _root_.GlobalTheory.HeightCounting.HeightCountingBaseData hL D cf (repOf Y)) (n : InRat Y cG) (PV : ∀ i : Fin D.R.m, principalLevelFrame.RowPsi (Vc D i) D.R.nV)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) : Type 1 extends toSettingsFormsState : _root_.GlobalTheory.HeightCounting.SettingsFormsData a n Pq where
  YS : NExpRealS R cG n.S
  eF : YS.eF = Bs.eF
  fi : ∀ i x, HEq ((YS.fi i).e x) x
  ser : SerAt YS g.v₀ Bs.exp PV cf Pq
  tau : TauTrue Bs.exp
structure ModuliPointsData (a : _root_.GlobalTheory.HeightCounting.HeightCountingBaseData hL D cf (repOf Y)) (n : InRat Y cG) (PV : ∀ i : Fin D.R.m, principalLevelFrame.RowPsi (Vc D i) D.R.nV)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) : Type 1 extends toSeriesState : _root_.GlobalTheory.HeightCounting.SeriesData g a n PV Pq where
  geo : Nonempty (GlobalTheory.GeoTie.ThetaTie YS g.fw D.nth)
variable {g}
structure HeightCountingCharacterData {a : _root_.GlobalTheory.HeightCounting.HeightCountingBaseData hL D cf (repOf Y)} {n : InRat Y cG} {xi : D.what₂.Tup → HChar D.host.E}
    {Q : D.what₂.places.Pl → Finset (PlE D.host)} (m : InMt Y cf xi Q)
    {Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host} (b : _root_.GlobalTheory.HeightCounting.ModuliPointsData g a n m.ad.PV Pq)
    (k : D.what₂.places.Pl → ℕ) (psi : D.what₂.places.Pl → HChar D.host.E) : Type 1 where
  ch : NChoice D
  tp : TupTied D cf ch
  xi_eq : tp.xi = xi
  psi_eq : tp.psi = psi
  Q_eq : ch.Q = Q
  k_eq : ∀ w, TwistedAt D w → ch.k' w = k w
  side : ChoiceSide D cf m.M b.Bs.exp ch tp
  ok : ∀ w, TwistedAt D w → IntegralHeckeForms.TwOK (ch.twI w) (ch.k' w) (ch.Q w) ((ch.psi' w).comp (D.ntw.art (ch.twI w) (ch.Q w)))
  th : EMtTheta Y b.YS ch
structure RealExpansionExtraData {nch : NChoice D} {tp : TupTied D cf nch} {a : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL D cf nch tp} (r : _root_.GlobalTheory.Mem.Top.Bl.NormRealisationData a R F cG Y)
    (g : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1) (xd : ThData D) : Type 1 where
  ad : MtAd Y a.all.gal.mt
  fi : ∀ i x, HEq ((r.nexp.fi i).e x) x
  hecke : NExpHeckeRowX R cG _ r.nexp r.hecke fun _ => LinearMap.id
  cHk : ∀ i b P, ∃ u : (D.ntw.O i)ˣ, r.hecke.cHk i b 1 P = algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) u
  eig : ∃ Sb e, (∀ i, Sb ⊆ D.ntw.S0 i) ∧ HEq a.nt.eig e ∧ EigAd Y Sb e
  ser : SerAt r.nexp g.v₀ a.all.exp ad.PV cf a.Pq
  tau : TauTrue a.all.exp
  geo : Nonempty (GlobalTheory.GeoTie.ThetaTie r.nexp g.fw D.nth)
  ok : ∀ w, TwistedAt D w → IntegralHeckeForms.TwOK (nch.twI w) (nch.k' w) (nch.Q w) ((nch.psi' w).comp (D.ntw.art (nch.twI w) (nch.Q w)))
  th : EMtTheta Y r.nexp nch
  xd : XdAll xd
  large : GlobalTheory.CoefDuty.Large D
  labc : LabConj a.nt.D a.nt.A.wdT
  zeta : ∀ k, haveI : Fact (a.nt.D.host.g k).Prime := ⟨a.nt.D.host.g_prime k⟩
    a.nt.A.grp.ζ k = (GlobalTheory.Mem.TypePl.labDat (a.nt.D.host.g k)).gen
  pht : ∃ fr : OmFrame a.nt.D, fr.jE = a.nt.jE ∧ PhtOn a.nt.A.wd fr fun _ _ _ _ => True
end Rows
open GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl in
def defaultExtension (hL : _root_.UpperTheory.Zero.LLC.RecTExists) : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL := fun _ _ _ _ w Z _ _ t _ _ xd c =>
  _root_.GlobalTheory.HeightCounting.RealExpansionExtraData (D := (w.st Z).toD7) c.row t.r.z.geo xd
end GlobalTheory.HeightCounting
end
end
end

section



section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
open Formalism.L2.Host (CharFrame HChar TupTied)
open GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug
namespace GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace Side
variable {D : D7} {nch : NChoice D} (s : Side D nch)
end Side
section Wit
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)}
def sideOf_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (t : RowsT K w Z Wt p0) {nch : NChoice (w.D Z)} (n : NchT w Z Wt nch)
    (c : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceCore hL t n) : Side (w.st Z).toD7 nch :=
  { G := _, Pl0 := _, I0 := _, T := _, A3 := _, J := t.r.z.core, R := t.r.z.R, P0 := t.r.z.F.P0, ψ0 := t.r.z.F.ψ0, cG := t.r.z.cG,
    v₀ := t.r.z.geo.v₀, S := _, YS := c.row.nexp, cf := GlobalTheory.Mem.Col2.TC.cf w.I w.l Z, tp := n.tp }
end Wit
def ExponentialNormChoice (hL : _root_.UpperTheory.Zero.LLC.RecTExists) : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL := fun _ _ _ _ _ _ _ _ t _ n xd c =>
  PLift ((_root_.GlobalTheory.PlugPt.sideOf_alt t n c).Export xd) × PUnit.{2}
structure ExtensionReading (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (𝒮 : Slots) : Type 2 where
  rd : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (p0 : BaseLevelRowSide (w.D Z))
    (t : RowsT K w Z Wt p0) (nch : NChoice (w.D Z)) (n : NchT w Z Wt nch) (xd : ThData (w.D Z)),
    𝒮.Nx K B f T w Z Wt p0 t nch n xd → _root_.GlobalTheory.Mem.Top.Bl.normChoiceOfExtension hL (_root_.GlobalTheory.PlugPt.ExponentialNormChoice hL) K B f T w Z Wt p0 t nch n xd
def HasExponent' {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (E : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) : Prop :=
  ∀ K B f T w Z Wt p0 t nch n xd c, E K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.PlugPt.ExponentialNormChoice hL K B f T w Z Wt p0 t nch n xd c)
def ExtensionReading.of {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (Rx : RPosition) {E : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL} (h : _root_.GlobalTheory.PlugPt.HasExponent' E) (Sx : SPosition) (Ox : OComponent₂) :
    _root_.GlobalTheory.PlugPt.ExtensionReading hL ⟨Rx, _root_.GlobalTheory.Mem.Top.Bl.normChoiceOfExtension hL E, Sx, Ox⟩ :=
  ⟨fun _ _ _ _ _ _ _ _ _ _ _ _ y => ⟨y.1, Classical.choice (h _ _ _ _ _ _ _ _ _ _ _ _ _ y.2)⟩⟩
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {𝒮 : Slots}
def sideOfWeightedPoint (ν : _root_.GlobalTheory.PlugPt.ExtensionReading hL 𝒮) {K : Ctx} (p : WPt 𝒮 K) : Side (p.w.D p.Z) p.O.ex.nch :=
  _root_.GlobalTheory.PlugPt.sideOf_alt p.x.what₂ p.x.n (ν.rd _ _ _ _ _ _ _ _ _ _ _ _ p.x.nx).1
def pinnedPointOfReading (ν : _root_.GlobalTheory.PlugPt.ExtensionReading hL 𝒮) : PinT 𝒮 BdPt := fun _ p _ b => ∃ kap lam err, sidePt b = (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).upd kap lam err
end GlobalTheory.PlugPt
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.HeightCounting GlobalTheory.TwInputs.Move GlobalTheory.HeightCounting.SideCopy
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem multiset_eq_of_esymm_pz (M M' : Multiset ℂ) (r : ℕ) (h1 : M.card = r) (h2 : M'.card = r)
    (h : ∀ k, 1 ≤ k → k ≤ r → M.esymm k = M'.esymm k) : M = M' := by
  have hp : (M.map fun a => Polynomial.X - Polynomial.C a).prod = (M'.map fun a => Polynomial.X - Polynomial.C a).prod := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm, Multiset.prod_X_sub_X_eq_sum_esymm, h1, h2]
    refine Finset.sum_congr rfl fun k hk => ?_
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp [Multiset.esymm]
    · rw [h k hk0 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]
  rw [← Polynomial.roots_multiset_prod_X_sub_C M, hp, Polynomial.roots_multiset_prod_X_sub_C]
private theorem multiset_eq_of_norm_pz (M M' : Multiset ℂ) (r : ℕ) (h1 : M.card = r) (h2 : M'.card = r) (q u : ℂ) (n : ℕ)
    (hq : q ≠ 0) (hu : u ≠ 0)
    (h : ∀ k, 1 ≤ k → k ≤ r → q ^ (k * (r - k) / 2) * (M.map fun a => a⁻¹ * u⁻¹ * (q ^ n)⁻¹).esymm k =
      q ^ (k * (r - k) / 2) * (M'.map fun a => a⁻¹ * u⁻¹ * (q ^ n)⁻¹).esymm k) : M = M' := by
  have hinj : Function.Injective fun a : ℂ => a⁻¹ * u⁻¹ * (q ^ n)⁻¹ := fun a b hab =>
    inv_injective (mul_right_cancel₀ (inv_ne_zero hu) (mul_right_cancel₀ (inv_ne_zero (pow_ne_zero _ hq)) hab))
  refine Multiset.map_injective hinj (multiset_eq_of_esymm_pz _ _ r (by rw [Multiset.card_map, h1])
    (by rw [Multiset.card_map, h2]) fun k a b => mul_left_cancel₀ (pow_ne_zero _ hq) (h k a b))
private theorem isRepOf_of_split_pz (D : D7) {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {n : ℕ} (π : D.naut.CG n) (s : ℝ)
    (hC : GlobalTheory.RowTie.ChebSplit D.nd) (ρ₁ ρ₂ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin n) (Qbar l))
    (h₂ : IsRepOf D l ι π s ρ₂)
    (c₁ : Continuous (fun g => ((ρ₁ g : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)))) (s₁ : IsSSRep ρ₁)
    (f₁ : ∀ᶠ w in Filter.cofinite, IsSplitPl D.host w → ∀ (B : ValuationSubring D.nd.Om) (σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om),
      IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) σ →
      ((ρ₁ σ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.map ι.toRingHom =
        galPol D.naut (D.naut.lpTw (D.naut.locG π w) s)) : IsRepOf D l ι π s ρ₁ := by
  obtain ⟨c₂, s₂, f₂⟩ := h₂
  have hfin := (Filter.eventually_cofinite.mp f₁).union (Filter.eventually_cofinite.mp f₂)
  have hcp := GlobalTheory.TwistLG.charpoly_eq_of_dense ρ₁ ρ₂ c₁ c₂ _ (hC hfin.toFinset).closure_eq (by
    rintro g ⟨w, hw, hs, B, hB, hg⟩
    rw [Set.Finite.mem_toFinset] at hw
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hw
    apply Polynomial.map_injective ι.toRingHom ι.injective
    rw [hw.1 hs B g hB hg, hw.2 B g hB hg])
  refine ⟨c₁, s₁, f₂.mono fun w hw B σ hB hσ => ?_⟩
  rw [hcp σ]
  exact hw B σ hB hσ
private theorem side_data_pz (D : D7) (cf : CharFrame D) (hCS : CharSide D cf) (Rw : RowSide D) (Sb : Finset (PlE D.host))
    (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (hE : GlobalTheory.TwInputs.EigTrue D cf Rw Sb eig) (S : RatDat D.ntw)
    (c : ∀ (i : D.ntw.Tw) (_b : Bool) (_P : PlE D.host), (D.ntw.O i)ˣ) (rowS : ∀ i, D.ntw.Sig i → D.what₂.FT)
    (hR : RowEig D S eig c rowS) (i : D.ntw.Tw) (s : D.ntw.Sig i)
    (hi : D.what₂.isot (D.ntw.jS i s) (rowS i s) ≠ ⊥) (hg : D.nd.goodRow (rowS i s)) (π : D.naut.CG D.R.r)
    (hπ : ∀ w, IsSplitPl D.host w → D.naut.locG π w = Rw.locR (rowS i s) w) (j : Fin D.R.m) (hj : j.1 + 1 = D.ntw.jS i s)
    (t : ℝ) (P : PlE D.host) (hP : IsSplitPl D.host P) (h1 : P ∉ Sb) (h2 : P ∉ D.ntw.S0 i) :
    ∃ M : Multiset ℂ, M.card = D.R.r ∧
      galPol D.naut (D.naut.lpTw (D.naut.locG (D.naut.tw π D.naut.etaTinv) P) t) =
        (((M.map (· * ((cf.eta.val P : ℂˣ) : ℂ))).map (· * ((normV P : ℕ) : ℂ) ^ ((t : ℝ) : ℂ))).map
          fun α => Polynomial.X - Polynomial.C α).prod ∧
      ∀ k, 1 ≤ k → k ≤ D.R.r → ∃ x : ↥D.LL0, embLL0 D x = ((normV P : ℕ) : ℂ) ^ (k * (D.R.r - k) / 2) * (M.map fun a =>
        a⁻¹ * (((cf.mu0 j).val P : ℂˣ) : ℂ)⁻¹ * (((normV P : ℕ) : ℂ) ^ (D.R.nV / 2))⁻¹).esymm k ∧
        algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (D.ntw.hEig i s k P) =
          algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (c i (D.ntw.side i s) P) ^ k *
            IsFractionRing.map (A := D.ntw.O0 i) (B := D.ntw.O i) (K := FractionRing (D.ntw.O0 i))
              (L := FractionRing (D.ntw.O i)) (D.ntw.O_inj i)
              ((if D.ntw.side i s then D.ntw.emb0 i else D.ntw.emb0b i) x) := by
  obtain ⟨hu, he⟩ := hE j (rowS i s) (by rw [hj]; exact hi) hg P hP h1
  rw [← hπ P hP] at hu he
  refine ⟨D.naut.frobEig (D.naut.locG π P), by rw [D.naut.frobEig_card _ hu, D.naut.locG_dim], ?_, fun k a b => ?_⟩
  · have hue : D.naut.unr (D.naut.locG D.naut.etaTinv P) := (D.naut.etaTinv_def P).1
    have hfe : D.naut.frobEig (D.naut.locG D.naut.etaTinv P) = {((cf.eta.val P : ℂˣ) : ℂ)} := by
      rw [hCS.frob _ P ((hCS.unr_iff _ P).1 hue), hCS.etaTinv, HChar.val_inv, inv_inv]
    have hd : D.naut.lpDim (D.naut.locG D.naut.etaTinv P) = 1 := D.naut.locG_dim _ P
    rw [galPol, D.naut.locG_tw, D.naut.frobEig_tw _ _ (D.naut.unr_char _ _ hd hu hue),
      D.naut.frobEig_char _ _ _ hu hue hd hfe]
  · refine ⟨eig (D.ntw.jS i s) (rowS i s) k P, ?_, hR i s k P a b hP h2⟩
    have := he k a b
    rw [hj] at this
    exact this
private theorem read_cancel_pz (D : D7) (i : D.ntw.Tw) (b : Bool) (u : (D.ntw.O i)ˣ) (k : ℕ) (x y : ↥D.LL0)
    (h : algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) u ^ k *
        IsFractionRing.map (A := D.ntw.O0 i) (B := D.ntw.O i) (K := FractionRing (D.ntw.O0 i))
          (L := FractionRing (D.ntw.O i)) (D.ntw.O_inj i) ((if b then D.ntw.emb0 i else D.ntw.emb0b i) x) =
      algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) u ^ k *
        IsFractionRing.map (A := D.ntw.O0 i) (B := D.ntw.O i) (K := FractionRing (D.ntw.O0 i))
          (L := FractionRing (D.ntw.O i)) (D.ntw.O_inj i) ((if b then D.ntw.emb0 i else D.ntw.emb0b i) y)) : x = y :=
  RingHom.injective _ (RingHom.injective _ (mul_left_cancel₀ (pow_ne_zero _ (u.isUnit.map _).ne_zero) h))
theorem UpperTheory.galoisRep_transport_of_copyAll_alt :
    GlobalTheory.Published.GlobalArtinReciprocity → ∀ {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}, CopyAll D D' ι e → ∀ {cf : CharFrame D} {cf' : CharFrame D'}, SameFrame cf cf' → CharSide D cf → ∀ (Rw : RowSide D) (jE' : D'.host.E →+* Qb) (A' : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D' cf' jE'), RowCusp D Rw → GalEx D' → GlobalTheory.RowTie.ChebSplit D'.nd → ∀ (Sb : Finset (PlE D.host)) (Sb' : Finset (PlE D'.host)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (eig' : ℕ → D'.what₂.FT → ℕ → PlE D'.host → ↥D'.LL0), GlobalTheory.TwInputs.EigTrue D cf Rw Sb eig → GlobalTheory.TwInputs.EigTrue D' cf' A'.row Sb' eig' → ∀ (S : RatDat D.ntw) (S' : RatDat D'.ntw) (c : ∀ (i : D.ntw.Tw) (_b : Bool) (_P : PlE D.host), (D.ntw.O i)ˣ) (c' : ∀ (i : D'.ntw.Tw) (_b : Bool) (_P : PlE D'.host), (D'.ntw.O i)ˣ), SameUnits c c' → ∀ (rowS : ∀ i, D.ntw.Sig i → D.what₂.FT) (rowS' : ∀ i, D'.ntw.Sig i → D'.what₂.FT), RowEig D S eig c rowS → RowEig D' S' eig' c' rowS' → RhoSpec D Rw rowS → (∀ i s, D'.what₂.isot (D'.ntw.jS i s) (rowS' i s) ≠ ⊥ ∧ D'.nd.goodRow (rowS' i s)) → RhoSpec D' A'.row rowS' := by
  intro hGA D D' ι e h cf cf' hF hCS Rw jE' A' hRC hGal hCh Sb Sb' eig eig' hE hE' S S' c c' hU rowS rowS' hR hR' hρ hgood
  obtain ⟨r, rfl⟩ := h.cp.exists_rest
  intro i s
  refine ⟨(hgood i s).1, (hgood i s).2, fun π' hc hr hloc φ ιq hφ hι => ?_⟩
  obtain ⟨hi, hg, hspec⟩ := hρ i s
  have hjr := D.ntw.jS_range i s
  obtain ⟨π, pc, pr, ploc, -⟩ := hRC _ hjr.1 hjr.2 _ hi hg
  have hemb : ∀ x, (if D.ntw.side i s then D.ntw.emb0 i else D.ntw.emb0b i) (e x) =
      (if (overD D r).ntw.side i s then (overD D r).ntw.emb0 i else (overD D r).ntw.emb0b i) x := by
    intro x
    have e1 := eq_of_heq (h.cp.emb0 i i HEq.rfl x)
    have e2 := eq_of_heq (h.cp.emb0b i i HEq.rfl x)
    have e3 : (overD D r).ntw.side i s = D.ntw.side i s := rfl
    rw [e3]
    cases D.ntw.side i s
    · exact e2
    · exact e1
  have hι0 : ∀ x : ↥D.LL0, ιq (φ ((if D.ntw.side i s then D.ntw.emb0 i else D.ntw.emb0b i) x)) = embLL0 D x := by
    intro x
    obtain ⟨y, rfl⟩ := e.surjective x
    rw [hemb y, h.cp.embLL0_eq]
    exact hι y
  obtain ⟨c1, s1, f1⟩ := hspec π pc pr ploc φ ιq hφ hι0
  obtain ⟨ρ', hρ'⟩ := _root_.GlobalTheory.HeightCounting.TwistAny.exists_isRepOf_tw_alt hGA _ cf' jE' A' hGal _ ιq π' hc hr
  refine isRepOf_of_split_pz _ ιq _ _ hCh _ ρ' hρ' c1 s1 ?_
  have hmu : cf.mu0 = cf'.mu0 := eq_of_heq hF.mu0
  have heta : cf.eta = cf'.eta := eq_of_heq hF.eta
  have hcc : ∀ b P, c' i b P = c i b P := fun b P => eq_of_heq (hU i i b P P HEq.rfl HEq.rfl)
  have hj : (⟨D.ntw.jS i s - 1, by omega⟩ : Fin D.R.m).1 + 1 = D.ntw.jS i s := Nat.sub_add_cancel hjr.1
  filter_upwards [f1, Sb.eventually_cofinite_notMem, Sb'.eventually_cofinite_notMem,
    (D.ntw.S0 i).eventually_cofinite_notMem] with P hP n1 n2 n3 hs B σ hB hσ
  obtain ⟨M, m1, m2, m3⟩ := side_data_pz D cf hCS Rw Sb eig hE S c rowS hR i s hi hg π ploc _ hj
    ((1 - (D.R.nV : ℝ)) / 2) P hs n1 n3
  obtain ⟨M', m1', m2', m3'⟩ := side_data_pz _ cf' A'.chr A'.row Sb' eig' hE' S' c' rowS' hR' i s (hgood i s).1 (hgood i s).2
    π' hloc _ hj ((1 - (D.R.nV : ℝ)) / 2) P hs n2 n3
  have hq : ((normV P : ℕ) : ℂ) ≠ 0 := by
    have hn : normV P = Ideal.absNorm P.asIdeal := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
    exact Nat.cast_ne_zero.mpr fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.mp (hn ▸ h0))
  have hM : M = M' := by
    refine multiset_eq_of_norm_pz M M' D.R.r m1 m1' _ _ (D.R.nV / 2) hq
      ((cf.mu0 ⟨D.ntw.jS i s - 1, by omega⟩).val P).ne_zero fun k a b => ?_
    obtain ⟨x, x1, x2⟩ := m3 k a b
    obtain ⟨y, y1, y2⟩ := m3' k a b
    rw [← hmu] at y1
    rw [← hemb y, hcc] at y2
    have hxy : x = e y := read_cancel_pz D i _ _ k _ _ (x2.symm.trans y2)
    refine x1.symm.trans (Eq.trans ?_ y1)
    rw [hxy, h.cp.embLL0_eq]
  subst hM
  rw [← heta] at m2'
  exact (hP B σ hB hσ).trans (m2.trans m2'.symm)
end
end

section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.memberE_extensionWithAtProperty_of_evLgG : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP) (A : AtP), EvLgG A → MemberE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s → MemberE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL N A) S Γ).s :=
  _root_.GlobalTheory.Mem.LiteralAutomorphy.memberE_extensionWithAtProperty_of_memberE
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT Formalism.L2.Top3 Formalism.L2.Top4
theorem GlobalTheory.Top.closed_linkEta_of_duty : ∀ (𝒜 : FamClass)
    (sel : _root_.Formalism.L2.TwistSelection 𝒜)
    (hduty : ∀ {eps : ℝ} (Fm : FamP eps), 𝒜 Fm → Duty Fm), Closed (D3 3 𝒜) fun Fm _ => LinkEta Fm := by
  intro 𝒜 sel _
  refine Closed.of_class fun Fm _ hc => ?_
  obtain ⟨x0, hx0⟩ := _root_.Formalism.L2.Top3.tied_families_of_choice_alt (sel Fm (d3_a hc))
  refine Formalism.L2.linkEta_closed Fm ⟨max x0 (Fm.x1 + 1), fun x hx i => ?_⟩
  have h1 : Fm.x1 < x := lt_of_lt_of_le (lt_add_one _) ((le_max_right _ _).trans hx)
  obtain ⟨T⟩ := hx0 x h1 ((le_max_left _ _).trans hx) i
  exact ⟨T.n.gal.mt, T.n.cover, T.n.gal.hecke⟩
end
end

section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR.Links Formalism.IndefR.Cx
namespace Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}
structure IndefiniteRealisationNormalisationDegreeThree {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
    {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
    {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) : Prop where
  muDef : ∀ C CH : ℝ, (Q.Rl.toCx3 Q.F).MuDef Q.F.cr (Q.Rl.num Q.F C CH) Q.Rl.mu
namespace Pins3
variable {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
theorem muDef_iff_alt (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (C CH : ℝ) :
    (Q.Rl.toCx3 Q.F).MuDef Q.F.cr (Q.Rl.num Q.F C CH) Q.Rl.mu ↔
      ∀ w, w ∈ Q.Rl.twPl ↔ (Q.Rl.toCx3 Q.F).W1 Q.F.cr (Q.Rl.num Q.F C CH) w := by
  have ht := Q.charW.tup
  constructor
  · rintro ⟨_, _, _, h4⟩
    exact h4
  · intro h
    refine ⟨fun w hw => ht.mu_ne w ((h w).2 hw), fun w _ => ht.mu_conj w, fun w => ?_, h⟩
    show Q.Rl.mu w = _
    split_ifs with hw
    · rfl
    · exact ht.mu_off w fun hm => hw ((h w).1 hm)
theorem realPins3_iff_twPl_iff_W1 (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) :
    _root_.Formalism.IndefR.IndefiniteRealisationNormalisationDegreeThree Q ↔ ∀ w, w ∈ Q.Rl.twPl ↔ (Q.Rl.toCx3 Q.F).W1 Q.F.cr (Q.Rl.num Q.F 0 0) w :=
  ⟨fun h => (_root_.Formalism.IndefR.Pins3.muDef_iff_alt Q 0 0).1 (h.muDef 0 0), fun h => ⟨fun C CH => (_root_.Formalism.IndefR.Pins3.muDef_iff_alt Q C CH).2 h⟩⟩
end Pins3
namespace RealPins3
variable {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks}
theorem _root_.Formalism.IndefR.IndefiniteRealisationNormalisationDegreeThree.w1 (h : _root_.Formalism.IndefR.IndefiniteRealisationNormalisationDegreeThree Q) (C CH : ℝ) :
    ∀ w, (Q.Rl.toCx3 Q.F).W1 Q.F.cr (Q.Rl.num Q.F C CH) w → w ∈ Q.Rl.twPl :=
  fun w hw => (h.muDef C CH).2.2.2 w |>.2 hw
end RealPins3
end Formalism.IndefR
end
end
end

section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR.Links Formalism.IndefR.Cx
namespace Formalism.IndefR.NX
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}
  {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def RealExpansionMajorant (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (cG : Formalism.L2.DIV.G0 Q.Rl.Pg D.R.r ≃* G0g D.nd) (Sd : RatDat D.ntw)
    (Yr : NExpRealS Q.Rl cG Sd) (c : NChoice D) :
    Prop :=
  ∃ jD : ∀ j, (Y.MjH j).V →ₗ[D.what₂.LL] Sd.WL j,
    (∀ (i : Fin D.R.m) (x : (Y.MjH ((i : ℕ) + 1)).V)
      (y : Fin (Module.finrank D.what₂.LL (Q.Rl.toRealDat.WL Q.F.lv2 false i)) → D.what₂.LL),
      HEq ((P.JM.eW i).symm x) y → (Yr.fi i).e (jD ((i : ℕ) + 1) x) = jDL Q.Rl Q.F.lv2 i y) ∧
    Nonempty (NMjRR Q.Rl cG Sd Yr Y c jD)
end Formalism.IndefR.NX
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx NumberField
namespace GlobalTheory
theorem V0_map_iota_eq_top_of_real_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (Ks : Type) (_ : Field Ks) (_ : NumberField Ks) (_ : Algebra Ks D.what₂.LL) (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (s : ℕ), P.A3.fam3.Ok3 s → P.A3.fam3.TypesSep3 → PrimRows3 Q.Rl Q.F → (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤ := by
  intro D L hT Gi Gl K Y cX ex Rc P Dcf Spf Zscf S Ks _ _ _ Q s hOk hSep hPrim
  haveI : IsTotallyComplex D.what₂.LL := D.tcLL
  exact GlobalTheory.T.rowMap_surjective_of_primitiveRows D P.Gp P.Pl0 P.I0 P.T P.A3 Ks Q.Rl P.P0 P.ψ0 P.Ps P.ψs P.Zs P.S0 P.S1 ex.p0 P.Dc P.Sp P.C P.NuC P.I
    Dcf Spf Zscf s P.tied.div hOk hSep Q.charW hPrim Q.zs Q.s1
end GlobalTheory
end
end
