module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharpolySmulOfProd
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.Bundle009
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.GalRead
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle398
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle931
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle562
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodRowHeckeOfOcc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle568
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle064
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle023
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle035
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle570
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle066
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle019
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle573
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle582
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1105
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle030
public import Formalism.LocalToGlobal.IndefiniteReal.IsFDiagIffDiagonal
public import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.FramesExistOfDiagonalTypePlaces
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle060
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EigenCompatibleOfBadSet
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle021
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle575
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle563
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle032
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle477
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle379
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle065
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle036
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle011

@[expose] public section

section



section
noncomputable section
namespace GlobalTheory.Triple
open NumberField IsDedekindDomain Polynomial Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open Formalism.L2.Host (HChar CharFrame embLL0 eExp ValLL0)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
open GlobalTheory.GalChar (IsGal toQ block)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf Zbar GalE toFb)
open GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary (embOver)
variable {D : D7}
section Reading
variable (X : NTw D.R D.host D.what₂ D.LL0 D.nd)
variable {X} {i : X.Tw} {b : Bool}
end Reading
section Comparison₂
variable (C : CharFrame D) (art : Ideles D.host.E →* Gab D.host.E D.nd.Om) {X : NTw D.R D.host D.what₂ D.LL0 D.nd}
structure IsGaloisTripleWithReduction {i : X.Tw} {b : Bool} (ρ : Reading X i b) (s : X.Sig i) (σ : D.what₂.FT) (π : D.naut.CG D.R.r)
    (r : GalE D →* GL (Fin D.R.r) (Qbar (X.l i))) (ν : GalE D →* (X.O0 i)ˣ) (w : D.what₂.places.Pl)
    (red : Zbar (X.l i) →+* FbAt D w) : Prop where
  good : D.nd.goodRow σ
  occurs : D.what₂.isot (X.jS i s) σ ≠ ⊥
  param : IsParam σ π
  gal : _root_.UpperTheory.GalS.IsGaloisRepOfN D π (X.l i) ρ.ι r
  shift : ∃ n, IsGal art ρ.κ ρ.ι (shiftChar C) n ν
  rho : ∀ g, ((X.rhoS i s g : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).map (toQ ρ.κ) =
    toQ ρ.κ ((ν g : (X.O0 i)ˣ) : X.O0 i) •
      ((r g : GL (Fin D.R.r) (Qbar (X.l i))) : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar (X.l i)))
  hecke : ∀ k P, k ≤ D.R.r → IsSplitPl D.host P → P ∉ X.S0 i → ∃ x : X.O0 i,
    algebraMap (X.O0 i) (X.O i) x = X.hEig i s k P ∧ ρ.toC x = heckeVal (muBase C (X.l i) (jIdx s)) π k P
  induces : ρ.Induces w
  residual : IsResidual ρ.ι r σ w red
def IsGaloisTripleAtSignature {i : X.Tw} {b : Bool} (ρ : Reading X i b) (s : X.Sig i) : Prop :=
  ∃ σ π r ν w red, _root_.GlobalTheory.Triple.IsGaloisTripleWithReduction C art ρ s σ π r ν w red
structure IsGaloisTripleForExpansion (Y : NExp D.R D.host D.what₂ D.LL0 D.nd X) : Prop where
  artin : IsGlobalArtin art
  evidence : ∀ i, X.NonzeroIndexPlace i → ∀ b : Bool, ∃ ρ : Reading X i b, IsChars C art ρ ∧
    ∀ s : X.Sig i, X.side i s = b → _root_.GlobalTheory.Triple.IsGaloisTripleAtSignature C art ρ s
  vec : ∀ i, X.NonzeroIndexPlace i → ∀ s : X.Sig i, Formalism.MainNotions.BlochKatoReduction.Gen.goodE Y i s
  all : Y.sig_all
end Comparison₂
def IsGaloisTripleOfExpansion {X : NTw D.R D.host D.what₂ D.LL0 D.nd} (Y : NExp D.R D.host D.what₂ D.LL0 D.nd X) : Prop :=
  ∃ (C : CharFrame D) (art : Ideles D.host.E →* Gab D.host.E D.nd.Om), _root_.GlobalTheory.Triple.IsGaloisTripleForExpansion C art Y
def IsGaloisTriple (D : D7) : Prop := _root_.GlobalTheory.Triple.IsGaloisTripleOfExpansion D.nexp
section ReadingAPI
variable {X : NTw D.R D.host D.what₂ D.LL0 D.nd} {i : X.Tw} {b : Bool}
end ReadingAPI
section Chars
variable (C : CharFrame D)
variable {C} {X : NTw D.R D.host D.what₂ D.LL0 D.nd} {i : X.Tw} {b : Bool} {art : Ideles D.host.E →* Gab D.host.E D.nd.Om}
end Chars
section Values
variable (μ : HChar D.host.E) (π : D.naut.CG D.R.r) (P : PlE D.host)
end Values
section API
variable {C : CharFrame D} {art : Ideles D.host.E →* Gab D.host.E D.nd.Om} {X : NTw D.R D.host D.what₂ D.LL0 D.nd}
  {i : X.Tw} {b : Bool} {ρ : Reading X i b} {s : X.Sig i} {σ : D.what₂.FT} {π : D.naut.CG D.R.r}
  {r : GalE D →* GL (Fin D.R.r) (Qbar (X.l i))} {ν : GalE D →* (X.O0 i)ˣ} {w : D.what₂.places.Pl}
  {red : Zbar (X.l i) →+* FbAt D w}
theorem isTripleAt_of_conj_alt (good : D.nd.goodRow σ) (occurs : D.what₂.isot (X.jS i s) σ ≠ ⊥) (param : IsParam σ π)
    (gal : _root_.UpperTheory.GalS.IsGaloisRepOfN D π (X.l i) ρ.ι r) (shift : ∃ n, IsGal art ρ.κ ρ.ι (shiftChar C) n ν)
    (A : GL (Fin D.R.r) (Qbar (X.l i)))
    (rho : ∀ g, ((X.rhoS i s g : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).map (toQ ρ.κ) =
      toQ ρ.κ ((ν g : (X.O0 i)ˣ) : X.O0 i) •
        ((A * r g * A⁻¹ : GL (Fin D.R.r) (Qbar (X.l i))) : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar (X.l i))))
    (hecke : ∀ k P, k ≤ D.R.r → IsSplitPl D.host P → P ∉ X.S0 i → ∃ x : X.O0 i,
      algebraMap (X.O0 i) (X.O i) x = X.hEig i s k P ∧ ρ.toC x = heckeVal (muBase C (X.l i) (jIdx s)) π k P)
    (induces : ρ.Induces w) (residual : IsResidual ρ.ι r σ w red) : _root_.GlobalTheory.Triple.IsGaloisTripleAtSignature C art ρ s := by
  refine ⟨σ, π, (MulAut.conj A).toMonoidHom.comp r, ν, w, red, good, occurs, param,
    _root_.GlobalTheory.Triple.isGaloisRepOfN_of_conj gal A fun _ => rfl, shift, rho, hecke, induces, residual.ss, fun g => ?_, residual.teich⟩
  obtain ⟨p, h1, h2⟩ := residual.charpoly g
  refine ⟨p, h1.trans ?_, h2⟩
  change _ = ((A * r g * A⁻¹ : GL (Fin D.R.r) (Qbar (X.l i))) : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar (X.l i))).charpoly
  rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]
theorem IsGaloisTripleWithReduction.unr_of_notMem (h : _root_.GlobalTheory.Triple.IsGaloisTripleWithReduction C art ρ s σ π r ν w red) {P : PlE D.host} (hS : P ∉ X.S0 i) :
    D.naut.unr (D.naut.locG π P) := h.param.unr P fun k hk => hS (X.placesOver_subset_exceptional i k hk)
variable {Y : NExp D.R D.host D.what₂ D.LL0 D.nd X}
theorem IsGaloisTripleForExpansion.triple (h : _root_.GlobalTheory.Triple.IsGaloisTripleForExpansion C art Y) {i : X.Tw} (hi : X.NonzeroIndexPlace i) (s : X.Sig i) :
    ∃ ρ : Reading X i (X.side i s), IsChars C art ρ ∧ _root_.GlobalTheory.Triple.IsGaloisTripleAtSignature C art ρ s :=
  let ⟨ρ, h1, h2⟩ := h.evidence i hi (X.side i s)
  ⟨ρ, h1, h2 s rfl⟩
theorem IsGaloisTripleOfExpansion.allGood (h : _root_.GlobalTheory.Triple.IsGaloisTripleOfExpansion Y) : GlobalTheory.TwSys.AllGood Y := let ⟨_, _, h⟩ := h; h.vec
theorem IsGaloisTripleOfExpansion.sig_all (h : _root_.GlobalTheory.Triple.IsGaloisTripleOfExpansion Y) : Y.sig_all := let ⟨_, _, h⟩ := h; h.all
end API
end GlobalTheory.Triple
end
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
noncomputable section
namespace GlobalTheory.TopLocData
section Gen
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {S T : HSp D}
end Gen
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : D.what₂.Word} {f : _root_.GlobalTheory.Fam.FamilyCharacter W u}
  {v : VCom f.c}
theorem s_eq_alt (G : GLoc v) {j : ℕ} (h : j + 2 * 0 + 2 = D.R.m) : G.s = j := by
  have := G.hs; omega
def frameOfSuccessor (G : GLoc v) {j : ℕ} (h : j + 2 * 0 + 2 = D.R.m) :
    Frame G.k (Yc D (j + 1)).rank (XIx (Fin D.R.k) (Fin D.R.t) (G.s + 1) ⊕ Fin 0) :=
  reN (congrArg (fun s => (Yc D (s + 1)).rank) (_root_.GlobalTheory.TopLocData.s_eq_alt G h)) (G.FY (G.s + 1) 0 rfl)
def successorFrameMatrix (G : GLoc v) : SB (Matrix (Ix (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.t) (G.s + 2))
    (XIx (Fin D.R.k) (Fin D.R.t) (G.s + 1) ⊕ Fin 0) G.k) :=
  ⟨(G.S.T (Fin D.R.t)).PhiTop, (GModel.phi_sb G).2⟩
def eigenvectorAtPlace {n : ℕ} {G : Fin n → GLoc v} (hGP : GPin G) {j : ℕ} (h : j + 2 * 0 + 2 = D.R.m) (i : Fin n) :
    WO (Yc D (j + 1)) D.sp.X' →₀ ℂ :=
  Classical.choose (hGP.eGT j h) i
theorem eGT_comb_eq_foldr_eigenvectorAtPlace {n : ℕ} {G : Fin n → GLoc v} (hGP : GPin G) {j : ℕ} (h : j + 2 * 0 + 2 = D.R.m) :
    (∀ i, HEq (_root_.GlobalTheory.TopLocData.eigenvectorAtPlace hGP h i) (G i).egT) ∧ ∀ F, IsThetaFunO f.c.ψ _ _ F →
      comb f.c.ψ _ _ (v.eGT j h) F = (List.finRange n).foldr (fun i g => comb f.c.ψ _ _ (_root_.GlobalTheory.TopLocData.eigenvectorAtPlace hGP h i) g) F :=
  Classical.choose_spec (hGP.eGT j h)
theorem eigenvectorAtPlace_isCombAt {n : ℕ} {G : Fin n → GLoc v} (hGP : GPin G) {j : ℕ} (h : j + 2 * 0 + 2 = D.R.m) (i : Fin n) :
    (ofSplit (G i).q).IsCombAt f.c.ψ (_root_.GlobalTheory.TopLocData.frameOfSuccessor (G i) h) (G i).FT (_root_.GlobalTheory.TopLocData.eigenvectorAtPlace hGP h i) (_root_.GlobalTheory.TopLocData.successorFrameMatrix (G i)).1 :=
  isCombAt_reN (G i).q f.c.ψ (G i).FT _ (_root_.GlobalTheory.TopLocData.s_eq_alt (G i) h) ((G i).FY ((G i).s + 1) 0 rfl) (G i).egT _
    ((_root_.GlobalTheory.TopLocData.eGT_comb_eq_foldr_eigenvectorAtPlace hGP h).1 i) (G i).egT_is
def localLatticeAtPlace (hψ : IsStdChar D f.c.ψ (-1)) {n : ℕ} {G : Fin n → GLoc v} (hGP : GPin G) {j : ℕ} (h : j + 2 * 0 + 2 = D.R.m)
    {M : GlobalTheory.FinPl.Lat (Yc D (j + 1))} (hM : IsSelfDualC (Yc D (j + 1)) M) (hLT : IsSelfDualC D.sp.X' f.g.LT) (i : Fin n) :
    LocPl f.c.ψ (Yc D (j + 1)) D.sp.X' M f.g.LT :=
  mkPl hψ (G i).q (G i).unit (_root_.GlobalTheory.TopLocData.frameOfSuccessor (G i) h) (G i).FT (_root_.GlobalTheory.TopLocData.successorFrameMatrix (G i)) (_root_.GlobalTheory.TopLocData.eigenvectorAtPlace hGP h i) (_root_.GlobalTheory.TopLocData.eigenvectorAtPlace_isCombAt hGP h i) hM hLT
end GlobalTheory.TopLocData
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.GalLoc.PsiLvl
theorem psiRead_withLoc_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D' : D7} (b : _root_.GlobalTheory.HeightCounting.NormChoiceConstructed hL D') : PsiRead (withLoc b.L) b.θ := by
  intro i u hu hu'
  have h := b.Bs.psiU i true u hu hu'
  exact h
theorem atMem_of_forall' {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.HeightCounting.Up.LayPAlt hL}
    (h : ∀ K B f T w Z Wt p0 t nch n c, p K B f T w Z Wt p0 t nch n c) : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL p := by
  refine ⟨1, one_pos, fun eps C8 C5 c6 Cb _ _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C _ _ _ => ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨0, fun K _ _ _ _ _ _ => ?_⟩⟩⟩⟩⟩
  refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, by simp, by simp, fun B f T _ _ _ _ => ?_⟩
  intro _ w Z Wt p0 t nch n xd c _ _ _
  exact h K B f T w Z Wt p0 t nch n c
end GlobalTheory.GalLoc.PsiLvl
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar


namespace GlobalTheory.HeightCounting.RatSide
theorem eigAd_of_rowEig_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x → ∀ eig : ℕ → (Dof x).what₂.FT → ℕ → PlE (Dof x).host → ↥(Dof x).LL0, (∀ (i : Fin (Dof x).R.m) (σ : (Dof x).what₂.FT) (k : ℕ) (Pl : PlE (Dof x).host) α Rr, HkDat x.m.z.R (SbD (Dof x)) i k Pl α Rr → (Dof x).nd.goodRow σ → (Dof x).what₂.isot (i.1 + 1) σ ≠ ⊥ → (Dof x).what₂.embLL (eig (i.1 + 1) σ k Pl : (Dof x).what₂.LL) = hkNorm x.m.z.R i k Pl * GlobalTheory.EigRows.rowEig x.r.Y i σ Pl (GlobalTheory.EigRows.diagLab (Dof x).R.r k)) → EigAd x.r.Y (SbD (Dof x)) eig := by
  intro hL
  refine StepW.of_all fun K B f T w _ _ _ P x _ eig heig => ?_
  intro i σ k Pl α Rr hd hσ y hy
  by_cases h0 : (Dof x).what₂.isot (i.1 + 1) σ = ⊥
  · rw [h0, Submodule.mem_bot] at hy
    subst hy
    simp
  · have e1 := heig i σ k Pl α Rr hd hσ h0
    have hP := (GlobalTheory.TwInputs.Eig.low_SbD (Dof x)).offPg x.m.z.lev.is hd.offS
    have e2 := GlobalTheory.EigRows.heckeOn_partR x.r.Y x.m.z.lev.is i hP hd.le hd.elt hd.reps σ
      ((GlobalTheory.EigRows.mem_isot_iff x.r.Y i σ y).1 hy)
    change hkNorm x.m.z.R i k Pl • Mult.heckeOn _ Rr (GlobalTheory.EigRows.readW x.r.Y i y) = _ • GlobalTheory.EigRows.readW x.r.Y i y
    rw [e2, e1, smul_smul]
end GlobalTheory.HeightCounting.RatSide
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.HeckeDataAtState
theorem exists_hkDat_at_state_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x →
    ∀ (i : Fin (Dof x).R.m) (k : ℕ) (Pl : PlE (Dof x).host), 1 ≤ k → k ≤ (Dof x).R.r → IsSplitPl (Dof x).host Pl →
      Pl ∉ SbD (Dof x) → ∃ α Rr, HkDat x.m.z.R (SbD (Dof x)) i k Pl α Rr := by
  intro hL
  refine StepW.of_all fun K B f T w _ _ _ P x _ i k Pl _ hk hs hP => ?_
  obtain ⟨α, Rr, h, -⟩ := GlobalTheory.TwInputs.Eig.exists_hkDat (R := x.m.z.R) x.m.z.F x.m.z.pins.char.base.lev (subset_refl _)
    (GlobalTheory.TwInputs.Eig.low_SbD (Dof x)) i hs hP hk
  exact ⟨α, Rr, h⟩
end GlobalTheory.HeckeDataAtState
end
end

section



section
noncomputable section
namespace GlobalTheory.HeightCounting.Up
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
open GlobalTheory.Mem.Top.TwChar (plUnder RootIso FrobPick)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option genInjectivity false
set_option genSizeOfSpec false

section Slot
variable (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (cDep : ℝ)
def OriginData (K : Ctx) {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) {D : D7} (Wt : Set B.places.Pl) (nch : NChoice D) : Prop :=
  ∃ (P : Pre2 K w) (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x), (ListSt cDep x ∧ SatU P) ∧ Wt = P.Wt ∧ Kept l.c.ch nch
def extensionWithOrigin : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL := fun K B f T w Z Wt p0 t nch n xd c => _root_.GlobalTheory.HeightCounting.Up.extensionWithList hL cDep K B f T w Z Wt p0 t nch n xd c ×
  PLift (_root_.GlobalTheory.HeightCounting.Up.OriginData hL cDep K w Wt nch)
def GeometricNormExtension : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL := fun K B f T w Z Wt p0 t nch n xd c => _root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep K B f T w Z Wt p0 t nch n xd c × PLift (GoodO (w.D Z) nch xd)
def SpectralFiniteness : Prop := AllSt fun K _ _ _ w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) (S : SExt) (Γ : GeoP), (ListSt cDep x ∧ SatU P) →
  ∃ (Z : w.Lt) (v : Lv3 (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) S Γ).s K w Z), v.Wt = P.Wt ∧ Kept l.c.ch v.nch
def SecondNonvanishing : Prop := ∀ (S : SExt) (Γ : GeoP), Pass KPx (IsBuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) S Γ).s) fun K B f T =>
  ∃ w : ColW B f T, Start K B f T w ∧ Has3 (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.GeometricNormExtension hL cDep) S Γ).s K B f T w
end Slot
variable (hL : _root_.UpperTheory.Zero.LLC.RecTExists)
def FirstStageExists : Prop := AllSt fun _ _ _ _ _ P x => IsEmpty x.o.N.nd.Loc →
  ∃ x' : St P, Nonempty (_root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x') ∧ SameGal (Dof x) (Dof x')
def ThirdStageExists : Prop := AllSt fun _ B _ T _ _ x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (s : B.places.Pl → (Dof x).ntw.Tw),
  (∀ v, ∃ b, ReadsAt (D := Dof x) (s v) b v) → (∀ v, s (B.places.conj v) = s v) →
  ∃ c : _root_.GlobalTheory.HeightCounting.HeightCountingCharacterData l.mt l.b T.k T.psi, c.ch.twI = s
def MoveToBase : Prop := StepW Start fun K B' f' _ w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl B B' →
  HEq f' f → Start K B f T w → HEq w'.px w.px → HEq w'.I.sel w.I.sel → HEq w'.I.J w.I.J → HEq w'.δ w.δ →
  ∀ (P : Pre2 K w) (x : St P), _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x → ∀ (P' : Pre2 K w'), Ext P.z P'.z → ∀ x' : St P', _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x' → SameGal (Dof x) (Dof x') →
    ∃ x'' : St P', Nonempty (_root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x'') ∧ Carried (Dof x) (Dof x'') ∧ ∀ cDep : ℝ, ListSt cDep x → ListSt cDep x''
end GlobalTheory.HeightCounting.Up
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr
noncomputable section
namespace GlobalTheory.LayerMove

variable {D : D7} (m : Mv D) {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
section
variable {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE} {M : Formalism.L2.MtFam D} {C : NChoice D} {tp : TupTied D cf C}
end
section
variable {cf : CharFrame D} {C : NChoice D} {tp : TupTied D cf C}
theorem Mv.phtOn_alt {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE} {fr : Formalism.L2.OmFrame D} (x : PhtOn A.wd fr fun _ _ _ _ => True) : PhtOn (m.sideA_alt A).wd (m.omFrame fr) fun _ _ _ _ => True := @_root_.GlobalTheory.HeightCounting.PhtOn.mk (_) (_) (_) (_) (_)
    (card := (by with_unfolding_all exact (x.card :)))
end
end GlobalTheory.LayerMove
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.HeightCounting.Up
open GlobalTheory.Mem.R3.Tr


section Gen
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {C : Formalism.L2.Pj.CoreJ D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat3 D A3 C.Q.c.F}
  {F : Face3 D A3} {X0 : BaseLevelRowSide D} {Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0} {cG : G0 R.Pg D.R.r ≃* G0g D.nd} {cf : CharFrame D}
  {g : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1}
theorem state_b2_of_rational_data_alt {a : _root_.GlobalTheory.HeightCounting.HeightCountingBaseData hL D cf (repOf Y)} {n : InRat Y cG} {PV : ∀ i : Fin D.R.m, principalLevelFrame.RowPsi (Vc D i) D.R.nV}
    {Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host}
    (row : RowSide D) (S : RatDat D.ntw) (hLS : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j))
    (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ)
    (Sb : Finset (PlE D.host)) (PV' : ∀ i : Fin D.R.m, principalLevelFrame.RowPsi (Vc D i) D.R.nV)
    (Pq' : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host)
    (hrow : HEq a.A.row row) (hS : HEq n.S S) (hhL : HEq n.In.hL hLS) (heig : HEq n.In.eig eig) (hθ : HEq n.In.θ θ)
    (hSb : HEq n.In.Sb Sb) (hPV : PV = PV') (hPq : HEq Pq Pq')
    (Bs : SideB D cf row (lowAll D) Pq' S hLS eig θ) (Sb_le : ∀ i, Sb ⊆ D.ntw.S0 i)
    (rootsOfUnityRing_le_wittIntegers : ∀ i, OverSet D (D.ntw.S0 i) (insert (D.ntw.l i) (lowAll D)))
    (lam : ∃ Z : GlobalTheory.LamTie.LamDat D, Z.Ok ∧ Z.Teich ∧ Z.C = cf ∧ Z.q0 = AbsolutelyIrreducibleSpan.q0 D ∧ GlobalTheory.LamTie.IsLamTieFull D.ntw Z)
    (YS : NExpRealS R cG S) (eF : YS.eF = Bs.eF) (fi : ∀ i x, HEq ((YS.fi i).e x) x)
    (ser : SerAt YS g.v₀ Bs.exp PV' cf Pq') (tau : TauTrue Bs.exp)
    (geo : Nonempty (GlobalTheory.GeoTie.ThetaTie YS g.fw D.nth)) : Nonempty (_root_.GlobalTheory.HeightCounting.ModuliPointsData g a n PV Pq) := by
  cases eq_of_heq hrow
  cases eq_of_heq hS
  cases eq_of_heq hhL
  cases eq_of_heq heig
  cases eq_of_heq hθ
  cases eq_of_heq hSb
  cases hPV
  cases eq_of_heq hPq
  exact ⟨⟨⟨⟨Bs, Sb_le, rootsOfUnityRing_le_wittIntegers, lam⟩, YS, eF, fi, ser, tau⟩, geo⟩⟩
end Gen
section Gen2
end Gen2
section MtCopy
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
theorem exists_in_mt_theta_twist_pv_eq (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x) (th : NTh (Dof x).R (Dof x).host (Dof x).what₂ (Dof x).LL0 (Dof x).nd (Dof x).ntw (Dof x).nexp)
    (m : Moved (oTw x (thTw (Dof x) th))) (hm : m.z = datTw x (thTw (Dof x) th)) (hc : m.Copy) (hh : m.Coh)
    (r : ReadPk m (sideTw x (thTw (Dof x) th))) (hp : r.Pin)
    (hj : ∀ μ h i y, HEq (r.Y.IL.jMt μ h i y).1 (x.r.Y.IL.jMt μ h i y).1) :
    ∃ mt : InMt r.Y (cfOf (stTw x _ m hc hh r hp)) w.I.xi (QOf P),
      mt.ad.PV = fun i => (by with_unfolding_all exact ((rowPsi (a := x.o.Z) (oTw x (thTw (Dof x) th)).Z (l.mt.ad.PV ((by with_unfolding_all exact (i :))))) :)) := by
  rcases m with ⟨z⟩
  dsimp only at hm
  subst hm
  refine ⟨{ M := (by with_unfolding_all exact (((thTw (Dof x) th).mt l.mt.M) :))
            ad :=
              { PV := fun i => (by with_unfolding_all exact ((rowPsi (a := x.o.Z) (oTw x (thTw (Dof x) th)).Z (l.mt.ad.PV ((i)))) : _))
                std := (by with_unfolding_all exact (l.mt.ad.std :))
                eW := (by with_unfolding_all exact (l.mt.ad.eW :))
                read := fun μ h i y g => by
                  have e := congrFun (eq_of_heq (hj μ h i y)) ((l.mt.ad.PV i).ψ g)
                  exact Eq.trans ((by with_unfolding_all exact ((l.mt.ad.read μ h i y g) :))) e.symm
                rat := (by with_unfolding_all exact (l.mt.ad.rat :))
                wt := (by with_unfolding_all exact (l.mt.ad.wt :))
                id := (by with_unfolding_all exact (l.mt.ad.id :)) }
            mt := by
              with_unfolding_all exact LiTw.mtIn (thTw (Dof x) th) l.mt.mt }, rfl⟩
end MtCopy
end GlobalTheory.HeightCounting.Up
end
end
end

section



section
noncomputable section
namespace GlobalTheory.HeightCounting.Fin3
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top
  GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar


variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
variable {x : St P} (L : LocAll (lay0 (Dof x)))
theorem real_pin_setup_local (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) : GlobalTheory.SeriesTie.RealPin (datL x L).R (datL x L).cG (setupL L l.b.ser.ex.ρ) :=
  have p := l.b.ser.ex.pin
  ⟨(by with_unfolding_all exact (p.psi :)), (by with_unfolding_all exact (p.inf :)), (by with_unfolding_all exact (p.cartT :)), (by with_unfolding_all exact (p.onbS :)), (by with_unfolding_all exact (p.onbT :)), (by with_unfolding_all exact (p.latS :)), (by with_unfolding_all exact (p.latT :)), (by with_unfolding_all exact (p.frS :)), (by with_unfolding_all exact (p.frT :)), (by with_unfolding_all exact (p.vac :)), (by with_unfolding_all exact (p.Pg :)),
    (by with_unfolding_all exact (p.grp :)), (by with_unfolding_all exact (p.mu0 :)), (by with_unfolding_all exact (p.eta :)), (by with_unfolding_all exact (p.delta :)), (by with_unfolding_all exact (p.deltaPl :)), (by with_unfolding_all exact (p.ap :)), (by with_unfolding_all exact (p.am :))⟩
theorem is_univ_char_local (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) : GlobalTheory.UnivChar.IsUnivChar (DL x L).nexp := (by with_unfolding_all exact (l.b.ser.ex.univ :))
end GlobalTheory.HeightCounting.Fin3
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem.R3

theorem _root_.GlobalTheory.T.geometric_parameter_of_reciprocity_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (Γ : GeoP) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), p = _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none Γ → (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → ∀ (K : Ctx) (q : WPt p.s K), (∀ X : GlobalTheory.Mem.Stages, K.Over X.B.toPre → HostHyp X.toD7 ∧ X.toD7.host.F = maximalRealSubfield X.toD7.host.E ∧ (∀ i, IsFDiag (Wc X.toD7 i) ∧ IsFDiag (Vc X.toD7 i)) ∧ (∀ i, (Vc X.toD7 i).IsPosDef) ∧ (∀ j, Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.Y j) ∧ Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.V j) ∧ (1 ≤ j → j ≤ X.toD7.R.m → Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.W j))) ∧ Formalism.IndefR.Seed.FrmC.StdLat X.toD7.sp.X' ∧ (∀ i, (∀ a b, (Vc X.toD7 i).hT ((Vc X.toD7 i).frame a) ((Vc X.toD7 i).frame b) = if a = b then 1 else 0) ∧ (Vc X.toD7 i).L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range (Vc X.toD7 i).frame)) ∧ ((∀ a b, X.toD7.sp.X'.hT (X.toD7.sp.X'.frame a) (X.toD7.sp.X'.frame b) = if a = b then 1 else 0) ∧ X.toD7.sp.X'.L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range X.toD7.sp.X'.frame))) → GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat → ∀ (a : TwArgs q.O.ex q.x.what₂), letI := a.x.grp; letI := a.x.fin; ∀ χ ∈ a.x.A3.A.X, chiIdem χ * lvlIdem a.x.F.P0 a.x.F.ψ0 ≠ 0 := by
  first | exact @_root_.GlobalTheory.Mem.R3.GenRows.goodGeneric_rows_alt | exact _root_.GlobalTheory.Mem.R3.GenRows.goodGeneric_rows_alt | (intros; apply _root_.GlobalTheory.Mem.R3.GenRows.goodGeneric_rows_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.NPin GlobalTheory.NFacts
namespace GlobalTheory
theorem weightParam_of_pin_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.WeightParam D := by
  intro hL D P
  exact GlobalTheory.T.weightInfinitesimalCharacterParam_of_levelCompatible D P.M P.tp.tup P.H.level (GlobalTheory.T.infinityType_etaTilde_at_cmTypeEmbeddings_eq_half D P.cf P.C P.tp P.chr) (_root_.GlobalTheory.T.infWt_eq_infOf_of_isDual D P.M P.tp.tup P.H)
end GlobalTheory
end
end
