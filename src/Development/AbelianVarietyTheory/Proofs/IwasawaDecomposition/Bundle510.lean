module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle030
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle455
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle032
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle034
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle029
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle500
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle506
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle033
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle502
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle503
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle504
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle365
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle339
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle345
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSplittingCharacterSelf
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle003
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowRatW
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle499
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowEx.FrmW

open GlobalTheory.Mem.R3 Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links GlobalTheory.Mem.Col2

variable {K : Ctx} {B : GlobalTheory.Mem.Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
  {L : SizeData₂ (w.st Z).toD7} {hT : GatTies (w.st Z).toD7} {Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L} {Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7}
  {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.st Z).toD7} {cX : ExtraC} {ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX}
  {t : RowsT K w Z Wt ex.p0}



theorem frame_of_args (a : TwArgs ex t) (x : TwIn ex) (hx : HEq a.x x) :
    x.R.toRealDat.C = Fr.at (w.st Z) f ∧ TwistPlacesOffPrimeQZero x.R.toRealDat.toLevCh ∧
      ∀ u, ∃ ξ ∈ T.set f, HEq (x.R.toRealDat.toLevCh.xiH u) ξ := by
  obtain rfl := eq_of_heq hx
  have hz := GlobalTheory.RowEx.twisted_data_off_base_level B f T w Z _ _ t.r.z
  have e := congrArg (fun s => match s with
    | ⟨_, _, _, _, _, _, _, _, _, R, _, _⟩ => R.toRealDat.C = Fr.at (w.st Z) f ∧ TwistPlacesOffPrimeQZero R.toRealDat.toLevCh ∧
        ∀ u, ∃ ξ ∈ T.set f, HEq (R.toRealDat.toLevCh.xiH u) ξ) a.pack
  exact e.mpr ⟨hz.2.1, hz.1, fun u => ⟨_, hz.2.2.2 u, HEq.rfl⟩⟩

end GlobalTheory.RowEx.FrmW

end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.OxMove

set_option linter.style.haveILetI false

open Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links

section General

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

abbrev JW (R : RealDat3 D A3 Ks) (F : Face3 D A3) : Type :=
  ∀ i : Fin D.R.m, (Fin ((R.toCx3 F).dW false i) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Mj ((i : ℕ) + 1)

def wpW (R : RealDat3 D A3 Ks) (F : Face3 D A3) (u : Parts R) (i : Fin D.R.m) (c : A3.fam3.base3.Ix) :
    Submodule D.what₂.LL (Fin ((R.toCx3 F).dW false i) → D.what₂.LL) := (by with_unfolding_all exact (((cxW R F u).WpK false i c) :))

def overW (R : RealDat3 D A3 Ks) (F : Face3 D A3) (u : Parts R) (j : JW R F) (σ : D.what₂.FT) (c : A3.fam3.base3.Ix) : Prop :=
  ∀ i : Fin D.R.m, D.what₂.isot ((i : ℕ) + 1) σ ≤
    Submodule.span ℂ ((j i) '' (wpW R F u i c : Set (Fin ((R.toCx3 F).dW false i) → D.what₂.LL)))

def lamW (R : RealDat3 D A3 Ks) (F : Face3 D A3) (u : Parts R) (j : JW R F)
    (l : ℕ → D.what₂.FT → (D.what₂.LL →+* ℂ) → ℝ) : Prop :=
  ∃ lab : D.what₂.FT → A3.fam3.base3.Ix, (∀ σ, (∃ c, overW R F u j σ c) → overW R F u j σ (lab σ)) ∧
    ∀ (i : Fin D.R.m) (σ : D.what₂.FT) (e : D.what₂.LL →+* ℂ), e ≠ D.what₂.embLL →
      (D.what₂.isot ((i : ℕ) + 1) σ ≠ ⊥ →
        l ((i : ℕ) + 1) σ e = Real.log (R.lam3 i A3.A.μ0 (lab σ) (InfinitePlace.mk e))) ∧
      (D.what₂.isot ((i : ℕ) + 1) σ = ⊥ → l ((i : ℕ) + 1) σ e = 0)

end General

section Copy

variable {B : Base} {C : Cols B} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {Ks : Type} [Field Ks] [NumberField Ks]

abbrev mv (a : Late B C) (N : ∀ u, Submodule (𝓞 B.LL) (a.V.div.Nu u).V) (h : B.Word → ℝ) : Late B C := Db.setDivZ a N h



theorem lamAre_copy (a : Late B C) (N : ∀ u, Submodule (𝓞 B.LL) (a.V.div.Nu u).V) (h : B.Word → ℝ)
    [iK : Algebra Ks a.D.what₂.LL] {A : FamIn3 a.D.what₂.LL G Pl0 I0 (List ℕ) T a.D.R.m} (R : RealDat3 a.D A Ks) (F : Face3 a.D A)
    {X0 : BaseLevelRowSide a.D} {Y : R3.Read (A3 := A) R.toRealDat F.lv2 X0} (Z : R3.ReadL R F X0 Y) (X : DivX a.D)
    (X' : DivX (mv a N h).D) (hX : HEq X'.logLam X.logLam) {X0' : BaseLevelRowSide (mv a N h).D} :
    letI := alg (mv a N h) iK
    ∀ {Y' : R3.Read (A3 := famInThreeCoefficientChange (mv a N h) A) (real3 (mv a N h) R).toRealDat (face3 (mv a N h) F).lv2 X0'}
      (Z' : R3.ReadL (real3 (mv a N h) R) (face3 (mv a N h) F) X0' Y'), HEq Z'.jW Z.jW → LamAre Z X → LamAre Z' X' := by
  letI := alg (mv a N h) iK
  intro Y' Z' hj hl
  have h1 : lamW R F (R.EEp3, R.toRealDat.EEat, R.Wp3) ((by with_unfolding_all exact (Z.jW :))) X.logLam := (by with_unfolding_all exact (hl :))
  have ej : ((by with_unfolding_all exact (Z.jW :)) : JW R F) = (by with_unfolding_all exact (Z'.jW :)) := eq_of_heq ((by with_unfolding_all exact (hj.symm :)))
  have el : X.logLam = (by with_unfolding_all exact (X'.logLam :)) := eq_of_heq ((by with_unfolding_all exact (hX.symm :)))
  have h2 := cast (congr (congrArg₂ (lamW R F) (parts_eq (mv a N h) R F) ej) el) h1
  exact (by with_unfolding_all exact (h2 :))

end Copy



theorem oAt_setDiv : ∀ (Γ : GeoP) (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) (O : Obj2 (w.D Z)) (O' : Obj2 (w.D (Db.setDivZ Z N h))), O' = O.tr N h → ∀ (t : RowsT K w Z Wt O.p0) (t' : RowsT K w (Db.setDivZ Z N h) Wt O'.p0), R3.Rw.RowsSame t t' → OAt (geoCl Γ) t O.X → Nonempty (OAt (geoCl Γ) t' O'.X) := by
  intro Γ K B f T w Z Wt N h O O' hO t t' hs hp
  have hOX : O'.X = (by with_unfolding_all exact ((divTr (D := w.D Z) N h O.X) :)) := by subst hO; exact (by with_unfolding_all exact ((Eq.refl (divTr (D := w.D Z) N h O.X)) :))
  clear hO
  generalize O'.X = X' at hOX
  revert t'
  generalize O'.p0 = p0'
  intro t' hs
  subst hOX
  cases t' with | mk hX' r' => ?_
  cases r' with | mk z' holds' Y' Zr' => ?_
  cases z' with | @mk Xg' tr' core' alg' alg_eq' R' => ?_
  have hXg := hs.Xg
  have htr := hs.tr
  have hcore := hs.core
  have hR := hs.R
  have hj := hs.jW
  clear hs
  change Xg' = t.r.z.Xg at hXg
  change tr' = t.r.z.tr at htr
  subst hXg htr
  change HEq core' _ at hcore
  have hc := eq_of_heq hcore
  subst hc
  have ha : alg' = GlobalTheory.Mem.R3.Tr.alg (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩)
      ⟨(Db.setDivZ Z N h).W, (Db.setDivZ Z N h).V, (Db.setDivZ Z N h).S, (Db.setDivZ Z N h).N, (Db.setDivZ Z N h).G⟩ t.r.z.alg := by
    apply Algebra.algebra_ext
    intro r
    apply (w.st (Db.setDivZ Z N h)).B.embLL.injective
    exact (by with_unfolding_all exact (((alg_eq' r).trans (t.r.z.alg_eq r).symm) :))
  subst ha
  change HEq R' _ at hR
  have hR2 := eq_of_heq hR
  subst hR2
  refine ⟨⟨?_, ?_⟩⟩
  · exact (by with_unfolding_all exact ((GeoCl.step (Γ := Γ) (D := (w.st Z).toD7) N h hp.geo) :))
  · exact (by with_unfolding_all exact ((lamAre_copy (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) N h (iK := t.r.z.alg) t.r.z.R t.r.z.F t.r.Z O.X
      (((divTr (D := w.D Z) N h O.X))) (((HEq.refl O.X.logLam))) (X0' := (p0')) (Y' := (Y')) ((Zr')) ((hj)) hp.lam) : _))

end GlobalTheory.Mem.OxMove

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Db GlobalTheory.Mem.Top.Bl.WitTr NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.kernelTaylorSeries_preserved_divisionLatticeChange :
    ∀ {B : Base} {f : Fr B.toPre} {T : TwDat B}
    (w : ColW B f T) (Z : w.Lt) (t : ColT w Z) (Y : DivX (w.D Z)) (Gy : G.LatInst (w.D Z))
    (ker : KerFam (w.D Z) t.Gt t.cmp (w.tw Z) Gy) (k : KerT t Y Gy ker)
    (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ),
    EntC k → ∃ k' : KerT (DivTr.colTTr w Z N h t) (DivTr.divTrZ w Z N h Y)
      (DivTr.latTrZ w Z N h Gy) (DivTr.kerTr w Z N h ker), EntC k' :=
  @GlobalTheory.Mem.Top.Bl.WitTr.kerT_entC_setDiv
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

theorem _root_.GlobalTheory.T.formsCoordinates_indexOfFamilyTuple_eq : ∀ (X : Stages) (px : PreX X.B.toPre) (I : ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (t : TupU I U), (∀ b, mAU X I hX Xg tr b (ixOf I U t) = rMat (D := X.toD7) (famR X I hX U Xg tr).A (levP (face0 X I hX U Xg tr).lv2 b).1 (levP (face0 X I hX U Xg tr).lv2 b).2 t) ∧ ∀ i : Fin X.toD7.R.m, mLU X I hX Xg tr (ixOf I U t) ((i : ℕ) + 1) = lMat (D := X.toD7) (famR X I hX U Xg tr).A (face0 X I hX U Xg tr).lv2.P0 (face0 X I hX U Xg tr).lv2.ψ0 i t := by
  first | exact @GlobalTheory.Mem.R3.Rw.mAU_mLU_ixOf | exact GlobalTheory.Mem.R3.Rw.mAU_mLU_ixOf | (intros; apply GlobalTheory.Mem.R3.Rw.mAU_mLU_ixOf <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

theorem _root_.GlobalTheory.T.typeRepresentativesParts_otherLaterStages : ∀ (B : Base) (C : Cols B) (a b : Late B C) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (Ks : Type) [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL] (A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m) (R : RealDat a.D A Ks) (F : Face a.D A) (y : Hd R) (y' : HdB b R), Same b y y' → (∀ (Φ : Type) (rep : Φ → _), Reps y F rep → @Reps b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) (real b R) y' (face b F) Φ ((by exact rep))) ∧ (∀ bb π, HEq (@Hd.prtE b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) (real b R) y' (face b F) bb ((by exact π))) (y.prtE F bb π)) ∧ ∀ i π, HEq (@Hd.prtW b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) (real b R) y' (face b F) ((by exact i)) ((by exact π))) (y.prtW F i π) := by
  first | exact @GlobalTheory.Mem.R3.Tr.reps_parts_tr | exact GlobalTheory.Mem.R3.Tr.reps_parts_tr | (intros; apply GlobalTheory.Mem.R3.Tr.reps_parts_tr <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

theorem _root_.GlobalTheory.T.definiteFormsAllTuples_coordinateLaws : ∀ (X : Stages) (px : PreX X.B.toPre) (I : ColIn X.B px) (hX : X.B.fields.Ok) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px), I.Ok → (∀ χ ∈ Xg, IsAbsIrrChar χ) → (∀ b a, (mAU X I hX Xg tr b a).Laws X.toD7.what₂.embLL (idemOf Xg)) ∧ ∀ a j, (mLU X I hX Xg tr a j).Laws X.toD7.what₂.embLL (idemOf Xg) := by
  first | exact @GlobalTheory.Mem.R3.Rw.Mats.mats_laws | exact GlobalTheory.Mem.R3.Rw.Mats.mats_laws | (intros; apply GlobalTheory.Mem.R3.Rw.Mats.mats_laws <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

theorem _root_.GlobalTheory.T.exists_periodMapForms_equiv_rowLiftForms_upperLevel : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (hX : B.fields.Ok) (Xg : Finset (Gc B w.px → B.LL)) (tr : TrI B w.px) (p : PkB B w.C (Gc B w.px)) (tA : ∀ a : w.I.ι, Tie1 (w.st Z).toD7.what₂.embLL (mAU (w.st Z) w.I hX Xg tr true a) (p.sA true a)), ∃ d : PerD p, Nonempty (PerT w Z hX Xg tr p (fun a x => (tA a).j x) d) := by
  first | exact @GlobalTheory.Mem.R3.Rw.PerId.exists_perT | exact GlobalTheory.Mem.R3.Rw.PerId.exists_perT | (intros; apply GlobalTheory.Mem.R3.Rw.PerId.exists_perT <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

theorem _root_.GlobalTheory.T.exists_rowsDatum_prescribedTuples_definedWeights : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (hX : B.fields.Ok) (Wt : Set B.places.Pl), (∀ v, B.places.conj v ∈ Wt ↔ v ∈ Wt) → ∃ W₀ : RowsRest B w.C, MuW w Wt W₀ ∧ (∀ W' : RowsRest B w.C, W'.kaBig = W₀.kaBig → W'.kaSmall = W₀.kaSmall → ∀ V S N G, DV.KapDef (assemble B w.C W' V S N G)) ∧ GlobalTheory.MemN.ShaOK B.toPre W₀.shaLen := by
  first | exact @GlobalTheory.Mem.R3.Rw.exists_rowsRest_muW | exact GlobalTheory.Mem.R3.Rw.exists_rowsRest_muW | (intros; apply GlobalTheory.Mem.R3.Rw.exists_rowsRest_muW <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Top.Bl

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_isE_of_heq {𝒮 : Slots} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {D : D7}
    (e : w.D Z = D) (O : Obj D) {O' : Obj2 (w.D Z)} (hO : HEq (ofObj O) O') (x : Wit 𝒮 K w Z O') (hx : EntC x.ker) :
    ∃ q : WPt 𝒮 K, q.Is D O ∧ EntC q.x.ker := by
  subst e
  obtain rfl := eq_of_heq hO
  exact ⟨⟨B, f, T, w, Z, O, x⟩, rfl, hx⟩

theorem exists_isE_pt {𝒮 : Slots} (H : WitMv 𝒮) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt}
    {O : Obj2 (w.D Z)} (x : Wit 𝒮 K w Z O) (hx : EntC x.ker) (Y : Lay (w.D Z)) (hY : layObj Y = O) (p : LedPart K.C Y) :
    ∃ q : WPt 𝒮 K, q.Is p.pt.D (Obj.ofPt p.pt) ∧ EntC q.x.ker := by
  obtain ⟨y, hy⟩ := H K B f T w Z O x (nPrime p.L) p.ht hx
  exact exists_isE_of_heq (Db.D_setDivZ w Z (nPrime p.L) p.ht) (Obj.ofPt p.pt)
    (hY ▸ heq_of_eq (pointObj_pt p)) y hy

theorem witExE_of_witMv : ∀ 𝒮 : Slots, WitMv 𝒮 → WitExE 𝒮 := fun 𝒮 H _ β hβ =>
  positionOf_ind (P := GoodE 𝒮) (R := fun K X _ _ c => ∀ (Y : Lay X.toD7) (_ : layObj Y = c.O) (p : LedPart K.C Y),
      ∃ q : WPt 𝒮 K, q.Is p.pt.D (Obj.ofPt p.pt) ∧ EntC q.x.ker)
    (fun _ _ _ _ _ _ _ g => g.1.elim fun b hb => exists_isE_pt H (b.wit g.2) hb) hβ β.Y β.hY β.p

end GlobalTheory.Mem.Top.Bl

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}

def St.rowsAre {P : Pre2 K w} (x : St P) (hη : ∀ j v, 1 ≤ j → j ≤ B.R.m → x.o.η j v = P.q.eta j v) :
    R3.RowsAre (w.st x.o.Z) w.I P.hX T P.Wt (Equiv.refl _) x.s.p0 :=
  ⟨x.m.z, x.m.intersectionNumber_baseChange, x.r.Y, x.r.Z.full fun j v h1 h2 => (x.m.eta j v).symm ▸ hη j v h1 h2, fun t => by
    change x.r.Y.tup t = _
    rw [x.r.tup]; exact x.m.tup t⟩

end GlobalTheory.Mem.R3.Rw

end
end

section

noncomputable section

namespace GlobalTheory.Mem.SRe.StdUnique

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr
  GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3.Tr

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem pt_of_deco {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} {ST SG Q Q' : Finset (HeightOneSpectrum (𝓞 E))} (hQ : Q' = ∅)
    {g : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} {p' : DecoF E n ST SG Q'} (e : p'.deco = p.deco)
    (h : IsPtOf hc g p) : IsPtOf hc g p' :=
  ⟨h.uni, e ▸ h.lat, e ▸ h.f, e ▸ h.be, fun P => (Finset.eq_empty_iff_forall_notMem.1 hQ P.1 P.2).elim⟩

variable {B : Base} {X : PreX B.toPre} (I : TC B X)



theorem reads_mem (u : B.Word) (i : ℕ) {Lb Lb' : Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)}
    {U U' : Subgroup (GA B (B.R.N i))} {chi : U →* ℂˣ} {chi' : U' →* ℂˣ} {y : (I.stp u I.mu0 i).Cl → GA B (B.R.N i)}
    {st st' : ∀ c, (I.stp u I.mu0 i).Stab c → GL (Fin (B.R.N i)) B.host.E} {k k' : Unit → GA B (B.R.N i)}
    (hR : I.Reads u I.mu0 i (fun _ => ()) (fun _ => Lb) (fun _ => U) (fun _ => chi) y st k)
    (hR' : I.Reads u I.mu0 i (fun _ => ()) (fun _ => Lb') (fun _ => U') (fun _ => chi') y st' k')
    (x : U) (hx : x.1 ∈ UAd B.sp.cm (B.R.N i)) : ∃ h : x.1 ∈ U', chi' ⟨x.1, h⟩ = chi x := by
  obtain ⟨c, -⟩ := hR.onto ()
  obtain ⟨p0, hp0, -⟩ := hR.k_std ()
  have hk : k () ∈ UAd B.sp.cm (B.R.N i) := hp0.uni
  have hQ : QE I.sel (I.tup I.mu0 : Chr B.fields.F B.fields.E B.fields.K) = ∅ := ColIn.twistPrimes_reference_tuple_eq_empty I
  haveI : NeZero (B.R.N i) := ⟨(B.R.N_pos i).ne'⟩
  have h1 : PtOf (y c * k ()) ((I.stp u I.mu0 i).rep c).1.1 := pt_of_deco hQ (extTo_deco _ _).symm (hR.pt c)
  have h2 : PtOf (y c * k' ()) ((I.stp u I.mu0 i).rep c).1.1 := pt_of_deco hQ (extTo_deco _ _).symm (hR'.pt c)
  have hyk : y c * k () ∈ UAd B.sp.cm (B.R.N i) := h1.uni
  have hg : y c * x.1 * k () ∈ UAd B.sp.cm (B.R.N i) := by
    have e : y c * x.1 * k () = (y c * k ()) * ((k ())⁻¹ * x.1 * k ()) := by group
    rw [e]
    exact mul_mem hyk (mul_mem (mul_mem (inv_mem hk) hx) hk)
  obtain ⟨q, hq⟩ := ChiFinTop.exists_isPtOf_of_mem (ST := (B.primes X).vT u) (SG := (B.primes X).vGs)
    (Q := QE I.sel (I.tup I.mu0 : Chr B.fields.F B.fields.E B.fields.K)) B.sp.cm hQ hg
  have hq' : PtOf (y c * x.1 * k' ()) q := by
    have e : y c * x.1 * k' () = y c * x.1 * k () * ((y c * k ())⁻¹ * (y c * k' ())) := by group
    rw [e]
    exact PtStab.isPtOf_mul_stab _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 hq
  obtain ⟨κ, hgam, hκq, hcos⟩ := (hR.lev c x.1 q hq).1 x.2
  have hm : x.1 ∈ U' := (hR'.lev c x.1 q hq').2 ⟨κ, hgam, hκq, hcos⟩
  refine ⟨hm, Units.ext ?_⟩
  exact (hR'.chr c ⟨x.1, hm⟩ κ hgam (by rw [hκq]; exact hq')).trans (hR.chr c x κ hgam (by rw [hκq]; exact hq)).symm



theorem reads_unique (u : B.Word) (i : ℕ) {Lb Lb' : Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)}
    {U U' : Subgroup (GA B (B.R.N i))} {chi : U →* ℂˣ} {chi' : U' →* ℂˣ} {y y' : (I.stp u I.mu0 i).Cl → GA B (B.R.N i)}
    {st st' : ∀ c, (I.stp u I.mu0 i).Stab c → GL (Fin (B.R.N i)) B.host.E}
    (hR : ∃ k, I.Reads u I.mu0 i (fun _ => ()) (fun _ => Lb) (fun _ => U) (fun _ => chi) y st k)
    (hR' : ∃ k, I.Reads u I.mu0 i (fun _ => ()) (fun _ => Lb') (fun _ => U') (fun _ => chi') y' st' k) (hy : y' = y)
    (hU : U ≤ UAd B.sp.cm (B.R.N i)) (hU' : U' ≤ UAd B.sp.cm (B.R.N i)) : Lb' = Lb ∧ U' = U ∧ HEq chi' chi := by
  obtain ⟨k, hR⟩ := hR
  obtain ⟨k', hR'⟩ := hR'
  subst hy
  have e : U' = U := le_antisymm (fun x hx => (reads_mem I u i hR' hR ⟨x, hx⟩ (hU' hx)).1)
    fun x hx => (reads_mem I u i hR hR' ⟨x, hx⟩ (hU hx)).1
  subst e
  refine ⟨Submodule.ext fun x => (hR'.lb () x).trans (hR.lb () x).symm, rfl, heq_of_eq (MonoidHom.ext fun x => ?_)⟩
  exact (reads_mem I u i hR hR' x (hU x.2)).2

variable (l : I.Laws)



theorem lev_le (hI : I.Ok) (hP : TC.Pins B X) (Z : TC.Later B (I.cols l)) (u : B.Word) (i : ℕ) (hi : i ≤ B.R.m)
    (K : ClsTied (D := I.rec7 l Z) u i hi) : (show Subgroup (GA B (B.R.N i)) from K.lev.U) ≤ UAd B.sp.cm (B.R.N i) := by
  have hg1 : gramN (I.rec7 l Z) i hi = 1 := ((spaces_in_coordinates I hI hP l Z).2.2.2 i hi).1
  have eU : UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) =
      UAd B.sp.cm (B.R.N i) := by rw [hg1]; rfl
  exact fun x hx => eU ▸ ((K.lev.U_eq x).1 hx).1



theorem std_pair (hI : I.Ok) (hP : TC.Pins B X) (Z Z' : TC.Later B (I.cols l)) (u : B.Word) {Ch Ch' : ℕ → Type}
    {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i} {chOf' : ∀ i, ((I.rec7 l Z').mem u).C.cls i → Ch' i}
    (F : FormsTiedSym (I.rec7 l Z) u Ch chOf) (F' : FormsTiedSym (I.rec7 l Z') u Ch' chOf')
    (hF : I.StdF l Z u F) (hF' : I.StdF l Z' u F') :
    F'.to0.cls0.lev.Lb = F.to0.cls0.lev.Lb ∧ F'.to0.cls0.lev.U = F.to0.cls0.lev.U ∧ HEq F'.to0.cls0.lev.chi F.to0.cls0.lev.chi ∧
      F'.to0.cls0.y = F.to0.cls0.y ∧ F'.to0.val0.eY = F.to0.val0.eY := by
  have hy : ∀ c : (I.stp u I.mu0 0).Cl, (F'.to0.cls0.y c).1 = (F.to0.cls0.y c).1 := fun c =>
    (hF'.yE 0 (Nat.zero_le _) (Or.inl rfl) c).trans (hF.yE 0 (Nat.zero_le _) (Or.inl rfl) c).symm
  have h := reads_unique I u 0 (hF.ends 0 (Nat.zero_le _) (Or.inl rfl)) (hF'.ends 0 (Nat.zero_le _) (Or.inl rfl)) (funext hy)
    (lev_le I l hI hP Z u 0 _ _) (lev_le I l hI hP Z' u 0 _ _)
  refine ⟨h.1, h.2.1, h.2.2, funext fun c => Subtype.ext (hy c), Equiv.ext fun z => Subtype.ext ?_⟩
  exact (hF'.eY 0 (Nat.zero_le _) (Or.inl rfl) z).trans (hF.eY 0 (Nat.zero_le _) (Or.inl rfl) z).symm



theorem car_of_same {D : D7} {u : D.what₂.Word} {F₁ F' : Forms0 D u}
    {lev : StepLevel D.host.F D.host.E (sigD D) (gramN D 0 (Nat.zero_le _)) (D.mem u).A.T D.R.f (badG D)}
    {y : (D.mem u).C.cls 0 → UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)}
    {eY : (D.mem u).C.Y 0 ≃ Formalism.L2.Forms.Fr D 0 (Nat.zero_le _)}
    (h : F₁.cls0.lev = lev ∧ F₁.cls0.y = y ∧ F₁.val0.eY = eY)
    (h' : F'.cls0.lev.Lb = lev.Lb ∧ F'.cls0.lev.U = lev.U ∧ HEq F'.cls0.lev.chi lev.chi ∧ F'.cls0.y = y ∧ F'.val0.eY = eY) :
    F'.cls0.lev.Lb = F₁.cls0.lev.Lb ∧ F'.cls0.lev.U = F₁.cls0.lev.U ∧ HEq F'.cls0.lev.chi F₁.cls0.lev.chi ∧
      F'.cls0.y = F₁.cls0.y ∧ F'.val0.eY = F₁.val0.eY := by
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact h'



theorem sameStd : SameStd := by
  intro B f T w Z Zn col col' F₁ h u
  have h1 := std_pair w.I w.l w.ok w.pins Z (reL Z Zn) u (col.C.forms u) (col'.C.forms u) (col.std u) (col'.std u)
  exact car_of_same (F₁ := F₁ u) (F' := (col'.C.forms u).to0) (lev := (by with_unfolding_all exact ((col.C.forms u).to0.cls0.lev :)))
    (y := (by with_unfolding_all exact ((col.C.forms u).to0.cls0.y :))) (eY := (by with_unfolding_all exact ((col.C.forms u).to0.val0.eY :))) ((by with_unfolding_all exact ((h u) :))) ((by with_unfolding_all exact (h1 :)))

end GlobalTheory.Mem.SRe.StdUnique

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Th

theorem weilTiedEq_of_eqTied : ∀ (D : D7) (X : ThetaX D) (T : ThetaTied D X) (W : WeilTied D X T), WeilThetaCompatibility W → WeilCompatibleEquivariance W :=
  fun _ _ _ _ h => ⟨h.range, h.Heisenberg₂, h.aut, h.cont, h.unit, h.split, ⟨h.twW, h.twV⟩, h.th⟩

end GlobalTheory.Mem.Th
end
