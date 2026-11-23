module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle031
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle012
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle017
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle030
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DecompositionInvariantsCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle013
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle014
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle005
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle003
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsLiftOfMemKO
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGaloisRepFamilyBounded
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimPartsAtIffBadAndOff
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle032
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle036
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle031
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle314
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EmbeddingClosedIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle030
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle037
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle040
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle041
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle123
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle038
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.Connected.Separation
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle016
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

section



section
noncomputable section
namespace GlobalTheory.Mem.Top.Bl
open Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.NX ReciprocityTheory.Gal
  NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.HeightCounting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option genInjectivity false in
set_option genSizeOfSpec false in

structure NAtData (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (cf : CharFrame D) (nch : NChoice D) (tp : TupTied D cf nch) :
    Type 1 where
  nt : _root_.GlobalTheory.HeightCounting.NormChoiceRealisation hL D cf nch tp
  all : _root_.GlobalTheory.HeightCounting.NAllCAlt D nch
  chr_eq : (⟨all.cf, all.tp⟩ : Σ c : CharFrame D, TupTied D c nch) = ⟨cf, tp⟩
  host : HostTied D
  frameN : ∀ x, all.gal.fr.jE x = host.fr.j x
  chrN : NCharTied D cf nch tp
  chrGal : NGalChrTied D cf nch tp
  Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host
  Pq_over : ∀ v, NG.OverPl (Pq v) v
  pq : ∀ i j b k Q ψ (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (hadm : NX.AdmTw D i k Q ψ),
    (all.exp.mtV i j b k Q ψ h1 h2 hadm).QP = qpOf D Pq Q ∧ (all.exp.mtV i j b k Q ψ h1 h2 hadm).DP = qpOf D Pq (D.ntw.pD i)
  jE_eq : HEq nt.jE all.gal.fr.jE
  mt_eq : HEq (mtL nt.L nt.M) all.gal.mt
  Pq_eq : HEq nt.Pq Pq
  low : 2 ∈ nt.low ∧ AbsolutelyIrreducibleSpan.q0 D ∈ nt.low ∧ (NumberField.discr D.host.E).natAbs.primeFactors ⊆ nt.low ∧
    (Ideal.absNorm D.host.ccK).primeFactors ⊆ nt.low
  split : GlobalTheory.SplitCoef.OSplit D
  ratIn : RatIn nt.D nt.S
  ratIn_hL : ratIn.hL = nt.hL
  ratIn_eig : ratIn.eig = nt.eig
  ratIn_θ : ratIn.θ = nt.θ
  depth : RowDepth nt.D nt.rep
section Rows
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
set_option genInjectivity false in
set_option genSizeOfSpec false in

structure NormRealisationData {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch}
    (a : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL D cf nch tp) (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) {X0 : BaseLevelRowSide D}
    (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) : Type 1 where
  kKs : Ks →+* ↥D.LL0
  hk : ∀ x : Ks, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap Ks D.what₂.LL x
  nexp : NExpRealS R cG (ratDatR R cG kKs hk)
  hecke : NExpRealH R cG (ratDatR R cG kKs hk) nexp
  grp : GrpTie D A3.A F.P0 F.ψ0 F.P1 F.ψ1 (R.eG.trans cG)
  rowLoc : _root_.Formalism.IndefR.principalLevelFrame.RowLocPinAlt a.all.gal.lp R.θ Y.PY (R.MY 0) (fun b => levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b)))
    (fun b => levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b))) (fun _ => R.e0) Y.eFT
  S_eq : HEq (ratL a.nt.L a.nt.S) (ratDatR R cG kKs hk)
  hL_eq : HEq a.nt.hL hecke.hL
  rep_eq : HEq a.nt.rep fun σ : D.what₂.FT => principalLevelFrame.rowRepR R.θ (Y.eFT σ)
end Rows
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B}
structure NormChoiceCore (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)}
    (t : RowsT K w Z Wt p0) {nch : NChoice (w.D Z)} (n : NchT w Z Wt nch) : Type 1 where
  a : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL (w.D Z) (TC.cf w.I w.l Z) nch n.tp
  row : _root_.GlobalTheory.Mem.Top.Bl.NormRealisationData (D := (w.st Z).toD7) a t.r.z.R t.r.z.F t.r.z.cG t.r.Y
  sel : Set.range a.Pq = Set.range w.I.sel
abbrev NormChoiceExtension (hL : _root_.UpperTheory.Zero.LLC.RecTExists) : Type 2 :=
  ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl)
    (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0) (nch : NChoice (w.D Z)) (n : NchT w Z Wt nch) (_ : ThData (w.D Z)),
    _root_.GlobalTheory.Mem.Top.Bl.NormChoiceCore hL t n → Type 1
def normChoiceOfExtension (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (E : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) : NCondition := fun K B f T w Z Wt p0 t nch n xd =>
  Σ c : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceCore hL t n, E K B f T w Z Wt p0 t nch n xd c
end GlobalTheory.Mem.Top.Bl
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.galois_family_local_global_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ w : D.what₂.places.Pl, ∃ (F : Finset (PlE D.host)) (Sy : Finset (PlE D.host → ℕ → ℂ)), ∀ (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)) (Sp : NdSpec A.pl M C big L.X L.T), _root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tp.tup Sp.iq L.Y L.C → ∀ (i : (withLoc L).nd.Loc) (x : (withLoc L).nd.X i), (withLoc L).nd.w i = w → ∃ c ∈ Sy, ∀ v, v ∉ F → ∀ k, GlobalTheory.CoefDuty.ptSys (withLoc L) i x v k = c v k := by
  first | exact @_root_.GlobalTheory.SysFin.ptSys_finite_alt | exact _root_.GlobalTheory.SysFin.ptSys_finite_alt | (intros; apply _root_.GlobalTheory.SysFin.ptSys_finite_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.lift_through_completion_iso_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (i : D.nd.Loc) (PI : D.naut.AV i) (k : Fin 2) (v : D.nd.PlG k) (s : SplitPlace D.host.E), s.w = D.naut.plGw k v → ∀ c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E, Continuous c → (∀ x : D.host.E, c (s.i x) = algebraMap D.host.E (s.w.adicCompletion D.host.E) x) → ∀ L : G0g D.nd → GAf D.host.E D.R.nV, IsTypeGroupBlockLift D D.R.nV L → ∀ F ∈ D.naut.typeV i PI, ∀ (h : GL (Fin D.R.r) (ZMod (D.host.g k))) (g : G0g D.nd), g ⟨k, v⟩ = h → (∀ kv, kv ≠ ⟨k, v⟩ → g kv = 1) → ∃ x : GAf D.host.E D.R.nV, TrivOutside {s.v} x ∧ IsLiftN h (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) ∧ NG.rt D.host.E D.R.nV (L g) ((P.M.loc i).real F) = NG.rt D.host.E D.R.nV x ((P.M.loc i).real F) := by
  first | exact @_root_.GlobalTheory.LiftOther.main_alt_alt | exact _root_.GlobalTheory.LiftOther.main_alt_alt | (intros; apply _root_.GlobalTheory.LiftOther.main_alt_alt <;> assumption)
end
end

section



section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

theorem _root_.GlobalTheory.T.split_bound_of_params_alt : GlobalTheory.Published.FontaineBcris → Formalism.GaloisCohomology.LocalFinitenessK → GlobalTheory.TwSys.Cheb → ∀ (D : D7) (L : SizeData₂ D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (R : KillingConditions.RowK) (C : NChoice D) (X : KillingConditions.HubData D) (c : ℝ) (CT : ℕ), GlobalTheory.HubX.Canon L HW R X → ParameterChoice' D L → 1 ≤ L.sc.L → 120 ≤ c → (CT : ℝ) ≤ L.sc.b → _root_.Formalism.MainNotions.AdmissibleParameterJ.AdmJAlt L → EmbeddingTypeJumps.ParametersPolynomiallyBounded L → _root_.Formalism.MainNotions.SumRepresentations.AdmAAlt D → _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → SumRepresentations.Conclusion42 D → SumRepresentations.ConclusionG5 D → SumRepresentations.ConclusionZ D → ResidualIrreducibleRankR D → GlobalTheory.SplitCoef.OSplit D → GlobalTheory.CoefDuty.TakenAll D → NChTie D C → GlobalTheory.PtCore.TriplesGood D → GlobalTheory.PtCore.SameTwist D C → GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.BlockCharParam D → GlobalTheory.HubX.MuUnr D → GlobalTheory.HubX.DepthZeroG D → (∀ i, GoodR D.nd i (X.r i)) ∧ (∀ i, EmbeddingTypeJumps.AtQD i → ∀ π ∈ D.nd.Zgood i, RestPt i (X.r i) (X.ρ i) π) ∧ EmbeddingTypeJumps.FontaineSubOfSumsAtDistinguishedPrimes X.r X.ρ ∧ KillingConditions.DataAD L HW X R ∧ GlobalTheory.HubX.CondCB L X c ∧ KillingConditions.ConstantColumnBound L X c ∧ (∃ M0 h0 : ℕ, GlobalTheory.HubX.JointCond_H0Wall D HW F X M0 h0) ∧ (∀ i, D.nd.l i ∉ TwistedPlaces.gset D → ∀ π ∈ D.nd.Zgood i, RestPt i (X.r i) (X.ρ i) π) ∧ (∀ i, KillingConditions.RangeAD L X.exc (D.nd.l i) → ∀ π, ∃ M0 h0 : ℕ, JointConditionTameBound D HW F i (X.r i) π M0 h0 (X.cB i)) ∧ (∀ i : D.nd.Loc, TwistedPlaces.TwLoc D i → D.nd.l i ∉ TwistedPlaces.gset D → KillingConditions.RangeAD L X.exc (D.nd.l i) → TwistedPlaces.SplitK D (D.nd.l i) → (∀ hJ : AdmissibleParameterJ.ConclusionJa D, EmbeddingTypes.hypDecl i (X.dc i) (Exists.choose hJ)) ∧ (∀ v ∈ placesOver D.host.E (D.nd.l i), v.asIdeal.ramificationIdx ℤ = 1) ∧ (∀ ep, EmbeddingTypes.ambTypeD (D := D) i ep) ∧ (∀ π ∈ D.nd.Zgood i, EmbeddingTypes.UnramifiedTrivialH1f (D := D) i (X.dc i) ∧ EmbeddingTypes.ambDual (D := D) i (X.ρ i) π (X.dc i) ∧ EmbeddingTypes.ambT2 (D := D) i (X.ρ i) π (X.dc i) ∧ EmbeddingTypes.ambW (D := D) i (X.ρ i) π (X.dc i) ∧ EmbeddingTypes.ambFil (D := D) i (X.r i) (X.ρ i) π (X.dc i) ∧ EmbeddingTypes.H1fFiniteRankTorsion (D := D) i (X.ρ i) π (X.dc i) ∧ LargeLevelLemmas.adm51 (D := D) i (X.r i) (X.ρ i) π ∧ ∃ M0 h0 : ℕ, GlobalTheory.HubX.DecompositionInvariantsCondition D HW i (X.ρ i) π (X.dc i) (X.c0 i) M0 h0) ∧ (∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), (D.nbr i w hw).Kw.1 ≤ Loc.MaximalUnramifiedExtension (D.nd.l i)) ∧ ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Ce : TruncatedSeriesCountingIdentities.CoefExt D i w hw), Ce.IsGood → ∀ x : D.nd.X i, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC Ce (rDuO D.nd i (X.r i) x)))) ∧ KillingConditions.SignatureChoiceCondition X.ρ C ∧ (∀ (i : D.nd.Loc) (k : Fin 2), TwistedPlaces.TwLoc D i → D.nd.l i = D.host.g k → HG D.nd D.naut i → GoodR D.nd i (X.r i) ∧ (∀ π ∈ D.nd.Z i, IsRhoOf D.nd i π (X.ρ i π) ∧ IsSSRep (rhoChiK D i (X.ρ i π))) ∧ ∃ (s S : ℕ) (sg : HeightOneSpectrum (𝓞 D.host.E) → Bool) (U : HeightOneSpectrum (𝓞 D.host.E) → Finset ℤ), X.eta + D.R.t + 1 < s ∧ CT * ((s + S) * (D.R.nV + 1) ^ 2 + (D.R.nV + 1) ^ 3) < D.host.g k ∧ PairedCharacterCondition.SignOK i sg ∧ PairedCharacterCondition.HostJ i (X.r i) X.eta s S sg U) ∧ (X.eta : ℝ) ≤ 2 * L.etaSz := by
  first | exact @_root_.GlobalTheory.HubX.Assembly.main_alt_alt | exact _root_.GlobalTheory.HubX.Assembly.main_alt_alt | (intros; apply _root_.GlobalTheory.HubX.Assembly.main_alt_alt <;> assumption)
end
end

section



section
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

abbrev _root_.GlobalTheory.T.LocalGlobalCompatibilityCMDatum' : Prop :=  ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : Formalism.BasicNotions.D7) (Γ : GlobalTheory.HeightCounting.GrpSide D) (k : Fin 2) (v : D.nd.PlG k) (χ : ((D.naut.plGw k v).adicCompletion D.host.E)ˣ →* ℂˣ) (hχ : IsSmoothChar χ) (u : ZMod (D.host.g k)), IsTame χ → _root_.GlobalTheory.PendOf.localLabelPolynomial hL D k v (Irr.ofDet 1 χ hχ) = Polynomial.X - Polynomial.C u → haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; resCard ((D.naut.plGw k v).adicCompletion D.host.E) = D.host.g k ∧ ∀ L : GlobalTheory.GLq.LabelDatum (D.host.g k), L.teich = D.ntypes.teichC k → L.gen = Γ.ζ k → ∃ θ : (ZMod (D.host.g k))ˣ →* ℂˣ, CharLift θ χ ∧ GlobalTheory.GLp.IsCharLab L θ u
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.HeightCounting.RowRhoInt
end GlobalTheory.HeightCounting.RowRhoInt
namespace GlobalTheory.HeightCounting.RowRhoInt
theorem twistEx_alt : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE),
    GalEx D → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (π : D.naut.CG D.R.r), D.naut.csd π → D.naut.ralg π →
      ∃ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.r) (Qbar l),
        IsRepOf D l ι (D.naut.tw π D.naut.etaTinv) ((1 - (D.R.nV : ℝ)) / 2) ρ := _root_.GlobalTheory.T.exists_galois_rep_of_cuspidal_alt
end GlobalTheory.HeightCounting.RowRhoInt
namespace GlobalTheory.HeightCounting.RowRhoInt
theorem core_data_of_point (hA : GlobalTheory.Published.GlobalArtinReciprocity) (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb)
    (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (hG : GalEx D) (hR : RowCusp D A.row) (hC : GlobalTheory.RowTie.ChebSplit D.nd)
    (l : ℕ) [Fact l.Prime] (j : ↥D.LL0 →+* PadicAlgCl l) (σ : D.what₂.FT)
    (hσ : ∃ k, 1 ≤ k ∧ k ≤ D.R.m ∧ D.what₂.isot k σ ≠ ⊥) (hg : D.nd.goodRow σ) :
    ∃ (L : Loc.FinExt l) (ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.r) (PadicAlgCl l)),
      Continuous (fun g => ((ρ g : GL (Fin D.R.r) (PadicAlgCl l)) : Matrix (Fin D.R.r) (Fin D.R.r) (PadicAlgCl l))) ∧
      (∀ g i k, ((ρ g : GL (Fin D.R.r) (PadicAlgCl l)) : Matrix (Fin D.R.r) (Fin D.R.r) (PadicAlgCl l)) i k ∈
        Formalism.L2.TwC.intOf l L.1) ∧
      ∀ π : D.naut.CG D.R.r, D.naut.csd π → D.naut.ralg π → (∀ w, IsSplitPl D.host w → D.naut.locG π w = A.row.locR σ w) →
        ∀ ι : Qbar l ≃+* ℂ, (∀ x, ι (j x) = embLL0 D x) →
          IsRepOf D l ι (D.naut.tw π D.naut.etaTinv) ((1 - (D.R.nV : ℝ)) / 2) ρ := by
  obtain ⟨k, hk1, hk2, hk⟩ := hσ
  obtain ⟨π₀, hc₀, hr₀, hl₀, hp₀⟩ := hR k hk1 hk2 σ hk hg
  obtain ⟨ι₀, hι₀⟩ := GlobalTheory.exists_padicAlgCl_ringEquiv_complex_comp_eq l ↥D.LL0 j (embLL0 D)
  have h0 : ∀ x, ι₀ (j x) = embLL0 D x := fun x => RingHom.congr_fun hι₀ x
  obtain ⟨ρG, hρG⟩ := _root_.GlobalTheory.HeightCounting.RowRhoInt.twistEx_alt hA D cf jE A hG l ι₀ π₀ hc₀ hr₀
  obtain ⟨L, P, hP⟩ := conjIntegral l (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om) D.R.r ρG hρG.1
  let ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.r) (PadicAlgCl l) := (MulAut.conj P⁻¹).toMonoidHom.comp ρG
  have hρ : ∀ g, ρ g = P⁻¹ * ρG g * P := fun g => by simp [ρ, MulAut.conj_apply]
  have hρ0 : IsRepOf D l ι₀ (D.naut.tw π₀ D.naut.etaTinv) ((1 - (D.R.nV : ℝ)) / 2) ρ :=
    isRepOf_conj D l ι₀ _ _ ρG ρ P hρ hρG
  refine ⟨L, ρ, hρ0.1, fun g i k => by rw [hρ]; exact hP g i k, fun π hc hr hl ι hι => ?_⟩
  have h1 := isRepOf_of_read D l ι₀ ι j h0 hι _ _ ρ hρ0 hp₀
  obtain ⟨ρ', hρ'⟩ := _root_.GlobalTheory.HeightCounting.RowRhoInt.twistEx_alt hA D cf jE A hG l ι π hc hr
  refine isRepOf_of_split D hC l ι _ _ _ ρ ρ' h1 hρ' (fun w hw => ?_)
  rw [D.naut.locG_tw, D.naut.locG_tw, hl₀ w hw, hl w hw]
end GlobalTheory.HeightCounting.RowRhoInt
namespace GlobalTheory.HeightCounting.RowRhoInt
section Pick
variable (hA : GlobalTheory.Published.GlobalArtinReciprocity) (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE)
  (hG : GalEx D) (hR : RowCusp D A.row) (hC : GlobalTheory.RowTie.ChebSplit D.nd)
open Classical in
def pickL_alt (l : ℕ) [Fact l.Prime] (j : ↥D.LL0 →+* PadicAlgCl l) (σ : D.what₂.FT) : Loc.FinExt l :=
  if h : GoodOcc D σ then (_root_.GlobalTheory.HeightCounting.RowRhoInt.core_data_of_point hA D cf jE A hG hR hC l j σ h.1 h.2).choose else ⟨⊥, inferInstance⟩
open Classical in
def padicRepresentationOfEmbedding (l : ℕ) [Fact l.Prime] (j : ↥D.LL0 →+* PadicAlgCl l) (σ : D.what₂.FT) :
    Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.r) (PadicAlgCl l) :=
  if h : GoodOcc D σ then (_root_.GlobalTheory.HeightCounting.RowRhoInt.core_data_of_point hA D cf jE A hG hR hC l j σ h.1 h.2).choose_spec.choose else 1
theorem pick_spec_alt (l : ℕ) [Fact l.Prime] (j : ↥D.LL0 →+* PadicAlgCl l) (σ : D.what₂.FT) (h : GoodOcc D σ) :
    Continuous (fun g => ((_root_.GlobalTheory.HeightCounting.RowRhoInt.padicRepresentationOfEmbedding hA D cf jE A hG hR hC l j σ g : GL (Fin D.R.r) (PadicAlgCl l)) :
      Matrix (Fin D.R.r) (Fin D.R.r) (PadicAlgCl l))) ∧
    (∀ g i k, ((_root_.GlobalTheory.HeightCounting.RowRhoInt.padicRepresentationOfEmbedding hA D cf jE A hG hR hC l j σ g : GL (Fin D.R.r) (PadicAlgCl l)) :
      Matrix (Fin D.R.r) (Fin D.R.r) (PadicAlgCl l)) i k ∈ Formalism.L2.TwC.intOf l (_root_.GlobalTheory.HeightCounting.RowRhoInt.pickL_alt hA D cf jE A hG hR hC l j σ).1) ∧
    ∀ π : D.naut.CG D.R.r, D.naut.csd π → D.naut.ralg π → (∀ w, IsSplitPl D.host w → D.naut.locG π w = A.row.locR σ w) →
      ∀ ι : Qbar l ≃+* ℂ, (∀ x, ι (j x) = embLL0 D x) →
        IsRepOf D l ι (D.naut.tw π D.naut.etaTinv) ((1 - (D.R.nV : ℝ)) / 2) (_root_.GlobalTheory.HeightCounting.RowRhoInt.padicRepresentationOfEmbedding hA D cf jE A hG hR hC l j σ) := by
  simp only [_root_.GlobalTheory.HeightCounting.RowRhoInt.pickL_alt, _root_.GlobalTheory.HeightCounting.RowRhoInt.padicRepresentationOfEmbedding, dif_pos h]
  exact (_root_.GlobalTheory.HeightCounting.RowRhoInt.core_data_of_point hA D cf jE A hG hR hC l j σ h.1 h.2).choose_spec.choose_spec
def bigOfStarStable (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) : Big D := fun l _ j =>
  ⟨⨆ σ : D.what₂.FT, ⨆ b : Bool, (_root_.GlobalTheory.HeightCounting.RowRhoInt.pickL_alt hA D cf jE A hG hR hC l (jSide D hstar l j b) σ).1, by
    haveI : ∀ σ b, FiniteDimensional ℚ_[l] ↥(_root_.GlobalTheory.HeightCounting.RowRhoInt.pickL_alt hA D cf jE A hG hR hC l (jSide D hstar l j b) σ).1 :=
      fun σ b => (_root_.GlobalTheory.HeightCounting.RowRhoInt.pickL_alt hA D cf jE A hG hR hC l (jSide D hstar l j b) σ).2
    haveI : ∀ σ : D.what₂.FT, FiniteDimensional ℚ_[l]
        ↥(⨆ b : Bool, (_root_.GlobalTheory.HeightCounting.RowRhoInt.pickL_alt hA D cf jE A hG hR hC l (jSide D hstar l j b) σ).1) :=
      fun σ => IntermediateField.finiteDimensional_iSup_of_finite
    exact IntermediateField.finiteDimensional_iSup_of_finite⟩
theorem pickL_jSide_le_cBig (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (l : ℕ) [Fact l.Prime]
    (j : ↥D.LL0 →+* PadicAlgCl l) (σ : D.what₂.FT) (b : Bool) :
    (_root_.GlobalTheory.HeightCounting.RowRhoInt.pickL_alt hA D cf jE A hG hR hC l (jSide D hstar l j b) σ).1 ≤ (_root_.GlobalTheory.HeightCounting.RowRhoInt.bigOfStarStable hA D cf jE A hG hR hC hstar l j).1 :=
  (le_iSup (fun b : Bool => (_root_.GlobalTheory.HeightCounting.RowRhoInt.pickL_alt hA D cf jE A hG hR hC l (jSide D hstar l j b) σ).1) b).trans
    (le_iSup (fun σ : D.what₂.FT => ⨆ b : Bool, (_root_.GlobalTheory.HeightCounting.RowRhoInt.pickL_alt hA D cf jE A hG hR hC l (jSide D hstar l j b) σ).1) σ)
end Pick
end GlobalTheory.HeightCounting.RowRhoInt
namespace GlobalTheory.HeightCounting.RowRhoInt
section HidaSetting
variable {D : D7} {cf : CharFrame D} {b0 b1 : Big D} {Sx : Finset (PlE D.host)} {T : TwR D.LL0 D.nd}
end HidaSetting


theorem rho_rows_alt : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE),
    GalEx D → RowCusp D A.row → GlobalTheory.RowTie.ChebSplit D.nd → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) →
    ∃ c1 : Big D, ∀ (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T),
      (∀ (l : ℕ) [Fact l.Prime] j, (c1 l j).1 ≤ (b0 l j).1) →
      ∃ rho : RhoFam D T, (∀ i σ b, Continuous fun g =>
          ((rho i σ b g : GL (Fin D.R.r) (T.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (T.O0 i))) ∧
        ∀ i σ b, (∃ j, 1 ≤ j ∧ j ≤ D.R.m ∧ D.what₂.isot j σ ≠ ⊥) → D.nd.goodRow σ →
        ∀ π : D.naut.CG D.R.r, D.naut.csd π → D.naut.ralg π → (∀ w, IsSplitPl D.host w → D.naut.locG π w = A.row.locR σ w) →
        ∀ (φ : FractionRing (T.O0 i) →+* Qbar (T.l i)) (ι : Qbar (T.l i) ≃+* ℂ),
          (∀ z : ℤ_[T.l i], φ (algebraMap (T.O0 i) _ (algebraMap ℤ_[T.l i] (T.O0 i) z)) =
            algebraMap ℚ_[T.l i] (Qbar (T.l i)) (z : ℚ_[T.l i])) →
          (∀ x : ↥D.LL0, ι (φ ((if b then T.emb0 i else T.emb0b i) x)) = embLL0 D x) →
          IsRepOf D (T.l i) ι (D.naut.tw π D.naut.etaTinv) ((1 - (D.R.nV : ℝ)) / 2)
            (mapRep (φ.comp (algebraMap (T.O0 i) (FractionRing (T.O0 i)))) (rho i σ b)) := by
  intro hA D cf jE A hG hR hC hstar
  refine ⟨_root_.GlobalTheory.HeightCounting.RowRhoInt.bigOfStarStable hA D cf jE A hG hR hC hstar, fun b0 b1 Sx T Sp hc => ?_⟩
  classical
  have hmem : ∀ (i : T.Tw) (σ : D.what₂.FT) (b : Bool) (h : GoodOcc D σ) g k k',
      ((_root_.GlobalTheory.HeightCounting.RowRhoInt.padicRepresentationOfEmbedding hA D cf jE A hG hR hC (T.l i) (jSide D hstar (T.l i) (Sp.j0 i) b) σ g : GL (Fin D.R.r) (PadicAlgCl (T.l i))) :
        Matrix (Fin D.R.r) (Fin D.R.r) (PadicAlgCl (T.l i))) k k' ∈ Formalism.L2.TwC.intOf (T.l i) (Sp.K0 i).1 := by
    intro i σ b h g k k'
    exact intOf_mono (((_root_.GlobalTheory.HeightCounting.RowRhoInt.pickL_jSide_le_cBig hA D cf jE A hG hR hC hstar (T.l i) (Sp.j0 i) σ b).trans
      (hc (T.l i) (Sp.j0 i))).trans (Sp.ringSpec_baseExtension_lowerBound i))
      ((_root_.GlobalTheory.HeightCounting.RowRhoInt.pick_spec_alt hA D cf jE A hG hR hC (T.l i) _ σ h).2.1 g k k')
  let rho : RhoFam D T := fun i σ b =>
    if h : GoodOcc D σ then
      mapRep (Sp.eO0 i).symm.toRingHom (restrictRep (Formalism.L2.TwC.intOf (T.l i) (Sp.K0 i).1)
        (_root_.GlobalTheory.HeightCounting.RowRhoInt.padicRepresentationOfEmbedding hA D cf jE A hG hR hC (T.l i) (jSide D hstar (T.l i) (Sp.j0 i) b) σ) (hmem i σ b h))
    else 1
  have hemb : ∀ i, Topology.IsEmbedding (fun x : T.O0 i => kap Sp i (algebraMap (T.O0 i) (FractionRing (T.O0 i)) x)) :=
    fun i => (GlobalTheory.CoefEmbed.embedding_closed_integral (T.l i) (T.O0 i) (T.twistBaseCoefficientRing_isAdic i) (kap Sp i) (twistFractionFieldToPadicAlgebraicClosure_padicInt Sp i)).1
  have hks : ∀ i (y : Formalism.L2.TwC.intOf (T.l i) (Sp.K0 i).1),
      kap Sp i (algebraMap (T.O0 i) (FractionRing (T.O0 i)) ((Sp.eO0 i).symm y)) = (y : PadicAlgCl (T.l i)) := by
    intro i y; rw [kap_alg, RingEquiv.apply_symm_apply]
  refine ⟨rho, fun i σ b => ?_, fun i σ b hocc hgood π hc hr hloc φ ι hφ hι => ?_⟩
  · by_cases h : GoodOcc D σ
    · have e : rho i σ b = mapRep (Sp.eO0 i).symm.toRingHom (restrictRep (Formalism.L2.TwC.intOf (T.l i) (Sp.K0 i).1)
          (_root_.GlobalTheory.HeightCounting.RowRhoInt.padicRepresentationOfEmbedding hA D cf jE A hG hR hC (T.l i) (jSide D hstar (T.l i) (Sp.j0 i) b) σ) (hmem i σ b h)) := dif_pos h
      rw [e]
      refine continuous_pi fun k => continuous_pi fun k' => ?_
      refine (hemb i).continuous_iff.mpr ?_
      have hc0 := (_root_.GlobalTheory.HeightCounting.RowRhoInt.pick_spec_alt hA D cf jE A hG hR hC (T.l i) (jSide D hstar (T.l i) (Sp.j0 i) b) σ h).1.matrix_elem k k'
      refine hc0.congr fun g => ?_
      exact (hks i ⟨_, hmem i σ b h g k k'⟩).symm
    · have e : rho i σ b = 1 := dif_neg h
      rw [e]
      simp only [MonoidHom.one_apply, Units.val_one]
      exact continuous_const
  · have h : GoodOcc D σ := ⟨hocc, hgood⟩
    have e : rho i σ b = mapRep (Sp.eO0 i).symm.toRingHom (restrictRep (Formalism.L2.TwC.intOf (T.l i) (Sp.K0 i).1)
        (_root_.GlobalTheory.HeightCounting.RowRhoInt.padicRepresentationOfEmbedding hA D cf jE A hG hR hC (T.l i) (jSide D hstar (T.l i) (Sp.j0 i) b) σ) (hmem i σ b h)) := dif_pos h
    rw [e]
    have hstd : ∀ z : ℤ_[T.l i], algebraMap ℤ_[T.l i] (PadicAlgCl (T.l i)) z =
        algebraMap ℚ_[T.l i] (PadicAlgCl (T.l i)) (z : ℚ_[T.l i]) :=
      fun z => IsScalarTower.algebraMap_apply ℤ_[T.l i] ℚ_[T.l i] (PadicAlgCl (T.l i)) z
    haveI : FaithfulSMul ℤ_[T.l i] (T.O0 i) := by
      rw [faithfulSMul_iff_algebraMap_injective]
      intro z z' hzz
      have h3 := congrArg (fun y => kap Sp i (algebraMap (T.O0 i) (FractionRing (T.O0 i)) y)) hzz
      simp only [twistFractionFieldToPadicAlgebraicClosure_padicInt] at h3
      exact Subtype.ext ((algebraMap ℚ_[T.l i] (PadicAlgCl (T.l i))).injective h3)
    have h₀ : ((kap Sp i).comp (algebraMap (T.O0 i) (FractionRing (T.O0 i)))).comp (algebraMap ℤ_[T.l i] (T.O0 i)) =
        algebraMap ℤ_[T.l i] (PadicAlgCl (T.l i)) := RingHom.ext fun z => (twistFractionFieldToPadicAlgebraicClosure_padicInt Sp i z).trans (hstd z).symm
    have h₁ : (φ.comp (algebraMap (T.O0 i) (FractionRing (T.O0 i)))).comp (algebraMap ℤ_[T.l i] (T.O0 i)) =
        algebraMap ℤ_[T.l i] (PadicAlgCl (T.l i)) := RingHom.ext fun z => (hφ z).trans (hstd z).symm
    obtain ⟨τ, hτ⟩ := GlobalTheory.EmbConj.exists_algEquiv _ _ h₀ h₁
    have hφτ : ∀ q, φ q = τ (kap Sp i q) := by
      have : φ = (τ.toRingEquiv.toRingHom).comp (kap Sp i) :=
        IsLocalization.ringHom_ext (nonZeroDivisors (T.O0 i)) (RingHom.ext fun y => (hτ y).symm)
      intro q; rw [this]; rfl
    have hrep : mapRep (φ.comp (algebraMap (T.O0 i) (FractionRing (T.O0 i))))
        (mapRep (Sp.eO0 i).symm.toRingHom (restrictRep (Formalism.L2.TwC.intOf (T.l i) (Sp.K0 i).1)
          (_root_.GlobalTheory.HeightCounting.RowRhoInt.padicRepresentationOfEmbedding hA D cf jE A hG hR hC (T.l i) (jSide D hstar (T.l i) (Sp.j0 i) b) σ) (hmem i σ b h))) =
        mapRep τ.toRingEquiv.toRingHom (_root_.GlobalTheory.HeightCounting.RowRhoInt.padicRepresentationOfEmbedding hA D cf jE A hG hR hC (T.l i) (jSide D hstar (T.l i) (Sp.j0 i) b) σ) := by
      ext g k k'
      change φ (algebraMap (T.O0 i) (FractionRing (T.O0 i)) ((Sp.eO0 i).symm ⟨_, hmem i σ b h g k k'⟩)) = τ _
      rw [hφτ, hks]
    rw [hrep]
    apply isRepOf_map D (T.l i) ι _ _ _ τ
    refine (_root_.GlobalTheory.HeightCounting.RowRhoInt.pick_spec_alt hA D cf jE A hG hR hC (T.l i) (jSide D hstar (T.l i) (Sp.j0 i) b) σ h).2.2 π hc hr hloc _ (fun x => ?_)
    have hx := hι x
    cases b
    · have e1 : T.emb0b i x = T.emb0 i (starRestrictSubfield D hstar x) := T.restX_coefficientEmbedding_conj i x _ rfl
      simp only [Bool.false_eq_true, if_false] at hx
      rw [e1, hφτ, kap_emb0] at hx
      exact hx
    · simp only [if_true] at hx
      rw [hφτ, kap_emb0] at hx
      exact hx
end GlobalTheory.HeightCounting.RowRhoInt
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.conjugate_place_completion_iso_tame_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (S : Reading P.T), _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (s : SplitPlace D.host.E) (hw : IsSplitPl D.host s.w), s.w = GlobalTheory.DimPartsCompare.cPl (D.naut.plGw k v) → IsTame (S i s.w hw).mu → ∀ c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E, Continuous c → (∀ x : D.host.E, c (s.i x) = algebraMap D.host.E (s.w.adicCompletion D.host.E) x) → ∀ Q, ∃ f ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q), f ≠ 0 ∧ ∀ x : GAf D.host.E D.R.nV, TrivOutside {s.v} x → Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x) ∈ blockGrp (s.w.adicCompletion D.host.E) D.R.r D.R.t → NG.rt D.host.E D.R.nV x f = blockChar (S i s.w hw).mu (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) • f := by
  exact _root_.GlobalTheory.TypeBlockConj.main_alt_alt
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.completion_iso_split_place_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (S : Reading P.T), _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ (i : D.nd.Loc) (PI : D.naut.AV i) (k : Fin 2) (v : D.nd.PlG k) (s : SplitPlace D.host.E) (hw : IsSplitPl D.host s.w), s.w = D.naut.plGw k v → ∀ c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E, Continuous c → (∀ x : D.host.E, c (s.i x) = algebraMap D.host.E (s.w.adicCompletion D.host.E) x) → ∀ F ∈ D.naut.typeV i PI, ∀ x : GAf D.host.E D.R.nV, TrivOutside {s.v} x → Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x) ∈ GlobalTheory.BlockType.blockGrp (s.w.adicCompletion D.host.E) D.R.r D.R.t → NG.rt D.host.E D.R.nV x ((P.M.loc i).real F) = GlobalTheory.BlockType.blockChar (S i s.w hw).mu (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) • (P.M.loc i).real F := by
  exact _root_.GlobalTheory.TypeVecEig.main_alt_alt
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.split_place_completion_iso_tame_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (S : Reading P.T), _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (s : SplitPlace D.host.E) (hw : IsSplitPl D.host s.w), s.w = D.naut.plGw k v → IsTame (S i s.w hw).mu → ∀ c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E, Continuous c → (∀ x : D.host.E, c (s.i x) = algebraMap D.host.E (s.w.adicCompletion D.host.E) x) → ∀ Q, ∃ f ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q), f ≠ 0 ∧ ∀ x : GAf D.host.E D.R.nV, TrivOutside {s.v} x → Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x) ∈ blockGrp (s.w.adicCompletion D.host.E) D.R.r D.R.t → NG.rt D.host.E D.R.nV x f = blockChar (S i s.w hw).mu (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) • f := by
  exact _root_.GlobalTheory.typeVec_blockChar_fixedPlace_alt
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.de_rham_weight_direct_sum_alt : GlobalTheory.Published.DeRhamPotSemistable → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ i : D.nd.Loc, (∀ a b (ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin a) (Qbar (D.nd.l i))) (ρ' : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin b) (Qbar (D.nd.l i))), Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i ρ → Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i ρ' → (∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i (Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ') w ↔ D.naut.IsdRW i ρ w ∧ D.naut.IsdRW i ρ' w) ∧ (∀ w, Formalism.MainNotions.SumRepresentations.At.WDok D.nd D.naut i ρ w → Formalism.MainNotions.SumRepresentations.At.WDok D.nd D.naut i ρ' w → D.naut.wdOf i (Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ') w = D.naut.lpSum (D.naut.wdOf i ρ w) (D.naut.wdOf i ρ' w)) ∧ (∀ τ, (∀ w, InducesW D.nd i τ w → D.naut.IsdRW i ρ w ∧ D.naut.IsdRW i ρ' w) → D.naut.jumpsW i (Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ') τ = D.naut.jumpsW i ρ τ + D.naut.jumpsW i ρ' τ)) := by
  first | exact @_root_.GlobalTheory.SumRepAdd.main_alt_alt | exact _root_.GlobalTheory.SumRepAdd.main_alt_alt | (intros; apply _root_.GlobalTheory.SumRepAdd.main_alt_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.pairRead_of_join_isTrue_unit :
    GlobalTheory.Published.BernsteinZelevinskyFiniteness →
      ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : CharacterChoiceData hL D),
        CharacterChoiceJoin P → ∀ S : Reading P.T, IsFaithfulReading P S → RowUnit S → PairRead S :=
  GlobalTheory.NPin.pairRead_of_join_alt
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
noncomputable section
namespace GlobalTheory.AutPart
theorem heckePol_map_eq_frobPol_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc) (ι : Type) [Finite ι] (F : ι → Submodule ℂ (GAf D.host.E D.R.nV → (mlX M X i).wt.W)) (irr : ∀ P, NG.IsIrrRep (mlX M X i).wt.ρ (F P)) (hinj : ∀ P P', NG.IsoRep (F P) (F P') → P = P') (hsurj : ∀ S', NG.IsIrrRep (mlX M X i).wt.ρ S' → (NG.isoTyp (mlX M X i).wt.ρ S').comap (mlX M X i).real ≠ ⊥ → ∃ P, NG.IsoRep (F P) S') (hne : ∀ P, (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real ≠ ⊥) (hind : iSupIndep (fun P => (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real)) (htop : ⨆ P, (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real = ⊤) (ptV : ι → Option (X.nd.X i)), (∀ P x, ptV P = some x ↔ (∀ (w : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), SplitOut X.nd i w → IsConjPl D.host w s.w → IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∀ y ∈ ((NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real), NG.tN (mlX M X i).J s ϖ k ((mlX M X i).real y) = (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) ((X.nd.hT i w k : X.nd.X i → X.nd.O i) x) • (mlX M X i).real y)) → ∀ P x, ptV P = some x → ∀ w, SplitOut X.nd i w → (heckePol X.nd i x w).map (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) = ((D.naut.frobEig (D.naut.lpTw (D.nbc.locAU (X.nd.j i) (A.au.cls (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2 { (mlX M X i).wt with S := F P, irrS := irr P }) w) ((1 - (D.R.nV : ℝ)) / 2))).map fun α => Polynomial.X - Polynomial.C α).prod := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp i ι _ F irr hinj hsurj hne hind htop ptV hpt P x hx w hw
  obtain ⟨s, ϖ, hc, hu⟩ := GlobalTheory.SplitConjPlace.splitEx_all D w hw.1
  have heig := (hpt P x).1 hx
  have hlev := _root_.GlobalTheory.T.mem_j_iff_umax_and_chi_eq_one_of_split_out D cf jE A M C tp hMI big X T Sp i w s hw hc
  have hne' : Formalism.L2.NG.isoTyp (mlX M X i).wt.ρ (F P) ⊓ Formalism.L2.NG.TypeSp (mlX M X i).wt.ρ (mlX M X i).J (mlX M X i).χ ≠ ⊥ := by
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hne P)
    rw [Submodule.ne_bot_iff]
    refine ⟨(mlX M X i).real y, ⟨hy, ?_⟩, fun h0 => hy0 ((mlX M X i).real_inj (h0.trans (map_zero _).symm))⟩
    rw [← (mlX M X i).real_range]; exact LinearMap.mem_range_self _ _
  obtain ⟨f, ⟨hfF, hfT⟩, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (GlobalTheory.T.inf_typeSpace_ne_bot_of_isotypicPart (mlX M X i).wt.ρ (mlX M X i).J (mlX M X i).χ (F P) (irr P).1 hne')
  have hfR : f ∈ LinearMap.range (mlX M X i).real := by rw [(mlX M X i).real_range]; exact hfT
  obtain ⟨y, rfl⟩ := hfR
  have hyV : y ∈ (Formalism.L2.NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real := by
    show (mlX M X i).real y ∈ Formalism.L2.NG.isoTyp (mlX M X i).wt.ρ (F P)
    exact (le_sSup (show F P ∈ {S' | Formalism.L2.NG.IsIrrRep (mlX M X i).wt.ρ S' ∧ Formalism.L2.NG.IsoRep (F P) S'} from
      ⟨irr P, LinearEquiv.refl ℂ _, fun h f f' e => e⟩)) hfF
  have hsph : ∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {s.v} κ →
      Formalism.L2.NG.rt D.host.E D.R.nV κ ((mlX M X i).real y) = (mlX M X i).real y := by
    intro κ hκ ht
    have hJ : κ ∈ (mlX M X i).J := ((hlev κ ht).1).2 hκ
    have := hfT.2 ⟨κ, hJ⟩
    rw [this, (hlev κ ht).2 hJ]; simp
  have hpol := A.au.locPol (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2
    { (mlX M X i).wt with S := F P, irrS := irr P } s w ϖ hc hu (mlX M X i).J (fun κ ht => (hlev κ ht).1)
    ((mlX M X i).real y) hfF hf0 hsph
    (fun k => (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) ((X.nd.hT i w k : X.nd.X i → X.nd.O i) x))
    (fun k hk1 hk2 => heig w k s ϖ hw hc hu hk1 hk2 y hyV)
  refine Eq.trans ?_ hpol

  simp [heckePol, Polynomial.map_sum]
end GlobalTheory.AutPart
end
end
end
