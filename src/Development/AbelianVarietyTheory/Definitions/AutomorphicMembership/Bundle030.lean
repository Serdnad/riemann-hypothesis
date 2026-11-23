module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle025
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle027
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodTupleConditionOfIdempotentZero
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle014
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle015
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle019
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp
public import Lean.Meta.Injective

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
  {L : SizeData₂ (w.st Z).toD7} {hT : GatTies (w.st Z).toD7} {Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L} {Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7}
  {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.st Z).toD7} {cX : ExtraC} (ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX)

abbrev famT {p0 : BaseLevelRowSide (w.D Z)} (t : RowsT K w Z Wt p0) := famR (w.st Z) w.I t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr


set_option genInjectivity false in
set_option genSizeOfSpec false in

structure TwArgs (t : RowsT K w Z Wt ex.p0) : Type 1 where
  Dc : ∀ Zs : DefSub (famT t).fam3.amb3, DefCols ((famT t).side3 t.r.z.F.P1 t.r.z.F.ψ1 Zs)
  Sp : ∀ Zs, SPer (Dc Zs)
  Zsc : DefSub (famT t).fam3.amb3 → IndefScale (famT t).fam3.base3
  lam : type_of% t.r.z.R.lam3
  err : type_of% t.r.z.R.err0
  lam_eq : ∀ i s p v, t.r.z.R.EEp3 p ≠ ⊥ → lam i s p v = t.r.z.R.lam3 i s p v
  x : TwIn ex
  pack : (⟨x.G, x.grp, x.fin, x.Pl0, x.I0, x.T, x.A3, x.core, x.alg, x.R, x.F, x.cG⟩ :
      Σ' (G : Type) (_ : Group G) (_ : Fintype G) (Pl0 I0 T0 : Type)
        (A3 : FamIn3 (w.st Z).toD7.what₂.LL G Pl0 I0 (List ℕ) T0 (w.st Z).toD7.R.m) (C : Formalism.L2.Pj.CoreJ (w.st Z).toD7)
        (_ : Algebra C.Q.c.F (w.st Z).toD7.what₂.LL) (R : RealDat3 (w.st Z).toD7 A3 C.Q.c.F) (_ : Face3 (w.st Z).toD7 A3),
        G0 R.Pg (w.st Z).toD7.R.r ≃* G0g (w.st Z).toD7.nd) =
    ⟨_, _, _, _, _, _, famT t, t.r.z.core, t.r.z.alg, (t.r.z.R.updS t.r.z.R.kap lam).withErr err, reFace t.r.z.F Dc Sp Zsc,
      (t.r.z.cG)⟩
  intersectionNumber_baseChange : Holds x.R x.F
  κ : HEq x.geo.κ t.r.z.geo.κ
  v₀ : HEq x.geo.v₀ t.r.z.geo.v₀
  fw : HEq x.geo.fw.e t.r.z.geo.fw.e
  tup : HEq x.Y.tup t.r.Y.tup
  tupT : HEq x.Y.tupT t.r.Y.tupT
  jA : HEq x.Y.jA t.r.Y.jA
  jA0 : HEq x.Y.jA0 t.r.Y.jA0
  eMt : HEq x.Y.eMt t.r.Y.eMt
  PY : HEq x.Y.PY t.r.Y.PY
  PW : HEq x.Y.PW t.r.Y.PW
  eFT : HEq x.Y.eFT t.r.Y.eFT
  IL : HEq x.Y.IL t.r.Y.IL
  eE : HEq x.Y.eE t.r.Y.eE
  eW : HEq x.Y.mj.eW t.r.Y.mj.eW
  jW : HEq x.Z.jW t.r.Z.jW
  eRR : HEq x.Z.eRR t.r.Z.eRR

end GlobalTheory.Mem.R3

end
end

section

noncomputable section

namespace GlobalTheory.Mem.Top.Bl.Model3

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)}

theorem fk_zero (t : RowsT K w Z Wt p0) (v : B.places.Pl) (hv : v ∉ Wt) (j : Fin B.R.m) :
    FK K.s (w.D Z) (j.1 + 1) (B.places.resChar v) = 0 := by
  by_contra h
  apply hv
  rw [t.exact]
  refine ⟨j, _, Or.inl rfl, Or.inr (Or.inr ?_)⟩
  have e : (w.D Z).plEq.symm ((w.D Z).plEq v) = v := Equiv.symm_apply_apply _ _
  show FK K.s (w.D Z) (j.1 + 1) ((w.D Z).what₂.places.resChar ((w.D Z).plEq.symm ((w.D Z).plEq v))) ≠ 0
  rw [e]
  exact h

section Idx

open Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T' : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T' D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
  {Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0}

end Idx

theorem fTypeG_ne {D : D7} (h : DV.KapDef D) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) : FTypeG D j ≠ 0 := by
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hf : 0 < Fintype.card D.what₂.Tau := by rw [D.what₂.card_Tau]; exact GaloisStage.f_pos D.R
  obtain ⟨τ⟩ := Fintype.card_pos_iff.1 hf
  have hs : (D.R.sigW j).1 = D.R.k + j - 1 := rfl
  let i : Fin (D.R.sigW j).1 := ⟨D.R.k + j - 1 - 1, by rw [hs]; omega⟩
  have e := (h j h1 h2 τ).1 i
  have l := DV.aPlusQ_last D j h1 h2 τ
  have p : (1 : ℤ) ≤ D.what₂.kaBig j τ i := by
    have : (1 : ℚ) ≤ (D.what₂.kaBig j τ i : ℚ) := e ▸ l
    exact_mod_cast this
  have q : 0 < fockDeg D j := by
    unfold fockDeg
    refine Finset.sum_pos' (fun t _ => add_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)
      (Finset.sum_nonneg fun _ _ => abs_nonneg _)) ⟨τ, Finset.mem_univ _, ?_⟩
    refine add_pos_of_pos_of_nonneg (Finset.sum_pos' (fun _ _ => abs_nonneg _) ⟨i, Finset.mem_univ _, ?_⟩)
      (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    exact abs_pos.2 (by omega)
  unfold FTypeG
  have : (0 : ℝ) < (fockDeg D j : ℝ) := by exact_mod_cast q
  linarith

theorem type_mem (t : RowsT K w Z Wt p0) (v : B.places.Pl) (i : Fin 2) (hv : B.places.resChar v = B.host.g i) : v ∈ Wt := by
  by_contra h
  have hm : 0 < B.R.m := by have := B.R.two_le_m; omega
  have z := fk_zero t v h ⟨0, hm⟩
  unfold FK at z
  rw [if_pos ⟨i, hv⟩] at z
  exact fTypeG_ne t.r.Y.kap 1 le_rfl hm z

end GlobalTheory.Mem.Top.Bl.Model3

end
end

section

noncomputable section

namespace GlobalTheory.Mem.Top.Bl

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

abbrev GeoP : Type 1 := ∀ D : D7, Formalism.L2.Pj.Core D → DivX D → Prop

def anyGeometry : GeoP := fun _ _ _ => True

section Reading

open Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
  {Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0}

def OverIx (Z : R3.ReadL R F X0 Y) (σ : D.what₂.FT) (c : A3.fam3.base3.Ix) : Prop :=
  ∀ i : Fin D.R.m, D.what₂.isot ((i : ℕ) + 1) σ ≤
    Submodule.span ℂ ((Z.jW i) '' ((R3.s0Of R F).Wp i c : Set (Fin ((R3.s0Of R F).dW i) → D.what₂.LL)))

def LamAre (Z : R3.ReadL R F X0 Y) (Xd : DivX D) : Prop :=
  ∃ lab : D.what₂.FT → A3.fam3.base3.Ix, (∀ σ, (∃ c, OverIx Z σ c) → OverIx Z σ (lab σ)) ∧
    ∀ (i : Fin D.R.m) (σ : D.what₂.FT) (e : D.what₂.LL →+* ℂ), e ≠ D.what₂.embLL →
      (D.what₂.isot ((i : ℕ) + 1) σ ≠ ⊥ →
        Xd.logLam ((i : ℕ) + 1) σ e = Real.log ((R3.s0Of R F).lam i A3.A.μ0 (lab σ) (InfinitePlace.mk e))) ∧
      (D.what₂.isot ((i : ℕ) + 1) σ = ⊥ → Xd.logLam ((i : ℕ) + 1) σ e = 0)

end Reading

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B}

structure OAt (Γ : GeoP) {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)} (t : RowsT K w Z Wt p0)
    (X : DivX (w.D Z)) : Type 1 where
  geo : Γ (w.st Z).toD7 t.r.z.core.toCore X
  lam : LamAre t.r.Z X

def OX (Γ : GeoP) : OComponent₂ := fun _ _ _ _ _ _ _ O t => OAt Γ t O.X

end GlobalTheory.Mem.Top.Bl

end
end

section

noncomputable section

namespace GlobalTheory.Mem.Top.Bl

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV
  Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.MainNotions Formalism.L2.Forms NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure SAt {D : D7} {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type} {A : FamIn D.what₂.LL G' Pl0 T D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (eE : D.what₂.EE →ₗ[ℂ] R.HE.H)
    (F0 : ∀ u, Forms0 D u) : Type 1 where
  P : SPack D F0
  S : SRest P
  t : GA D (D.sp.Y 0)
  c : ℝ
  c_pos : 0 < c
  see : SeeAt R F P.X P.inst t
  ev : EvalTieT (MP R) R.ν0 R.fd0 (EP R F) P.X P.G (iotaX P.X P.inst).toMulEquiv t c
  rowJ : RowJ R eE P.X P.inst P.G t S.j

def SX : SPosition := fun _ _ _ _ w Z _ _ r col =>
  SAt (D := (w.st Z).toD7) r.r.z.R.toRealDat r.r.z.F.lv2 r.r.Y.eE fun u => (col.C.forms u).to0

end GlobalTheory.Mem.Top.Bl

end
end

section

noncomputable section

namespace GlobalTheory.Mem.Top.Bl

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain
  Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section General

variable (D : D7) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} (A : FamIn D.what₂.LL G Pl0 T D.R.m)
  (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (P1 : Subgroup G) (ψ1 : P1 →* D.what₂.LLˣ) (X0 : BaseLevelRowSide D) (tp : D.what₂.Tup → T)
  (eG : G ≃* G0g D.nd)


set_option genInjectivity false in
set_option genSizeOfSpec false in
structure AllT : Type where
  jA : ∀ μ, (Fin (rDim D A P1 ψ1 (tp μ)) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Amb μ
  jA0 : ∀ μ, (Fin (rDim D A P0 ψ0 (tp μ)) → D.what₂.LL) →ₛₗ[D.what₂.embLL] X0.s.Amb μ
  eMt : ∀ (i : Fin D.R.m) μ, (Fin (lDim D A P0 ψ0 i (tp μ)) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL μ ((i : ℕ) + 1)
  formsA : ∀ μ, FormsTie D.what₂.embLL (jA μ) (rH D A P1 ψ1 (tp μ)) (rE D A P1 ψ1 (tp μ)) (D.what₂.eOp μ)
  latA : ∀ μ, OLatTie D.what₂.embLL (D.what₂.Mtilde μ) (jA μ) (rNab D A P1 ψ1 (tp μ))
  formsAtBottomLevel : ∀ μ, FormsTie D.what₂.embLL (jA0 μ) (rH D A P0 ψ0 (tp μ)) (rE D A P0 ψ0 (tp μ)) (X0.s.eOp μ)
  latA0 : ∀ μ, OLatTie D.what₂.embLL (X0.s.Mtilde μ) (jA0 μ) (rNab D A P0 ψ0 (tp μ))
  formsL : ∀ (i : Fin D.R.m) μ, FormsTie D.what₂.embLL ((D.what₂.jMt μ ((i : ℕ) + 1)).comp (eMt i μ).toLinearMap)
    (lH D A P0 ψ0 i (tp μ)) (lE D A P0 ψ0 i (tp μ)) (D.what₂.eMt μ ((i : ℕ) + 1))
  latL : ∀ (i : Fin D.R.m) μ, OLatTie D.what₂.embLL (D.what₂.MtLat μ ((i : ℕ) + 1))
    ((D.what₂.jMt μ ((i : ℕ) + 1)).comp (eMt i μ).toLinearMap) (lNab D A P0 ψ0 i (tp μ))
  cen : ∀ μ (z : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))) (a : MonoidAlgebra D.what₂.LL G),
    (∀ g : G, D.what₂.embLL (a.coeff g) = (z : MonoidAlgebra ℂ (G0g D.nd)).coeff (eG g)) →
    (∀ x, (RowSide.sharp D).cen μ z (jA μ x) = jA μ ((Formalism.L2.Rows.rOp D A P1 ψ1 (tp μ) a).mulVec x)) ∧
    (∀ x, X0.s.cen μ z (jA0 μ x) = jA0 μ ((Formalism.L2.Rows.rOp D A P0 ψ0 (tp μ) a).mulVec x)) ∧
    ∀ (i : Fin D.R.m) x, D.ntypes.cenMt μ ((i : ℕ) + 1) z (D.what₂.jMt μ ((i : ℕ) + 1) (eMt i μ x)) =
      D.what₂.jMt μ ((i : ℕ) + 1) (eMt i μ (((A.fam.L i (tp μ)).S.lvlOp (A.fam.L i (tp μ)).r (A.fam.lvlA P0 ψ0).P
        (A.fam.lvlA P0 ψ0).ψ a).mulVec x))

def SameOn {K : Type} {n n' : ℕ} {V : Type} (j : (Fin n → K) → V) (j' : (Fin n' → K) → V) : Prop :=
  n = n' ∧ ∀ x x', (∀ (a : Fin n) (a' : Fin n'), (a : ℕ) = a' → x a = x' a') → j x = j' x'

end General

section Cols

attribute [local instance] GlobalTheory.Mem.Col2.starE

variable {B : Base} {px : PreX B.toPre} (I : ColIn B px)

def tAll (a : I.ι) : R3.TupU I Set.univ := ⟨I.tup a, Or.inr ((R3.tup_mem_tuOf I).2 (Set.mem_univ a))⟩

end Cols

section Forms

open _root_.Formalism.L2.Col

def IsFormOf {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (hX : X.Ok)
    (P : LevFam X.E X.K R.r Pr.vGs) (x : MtildeV W Ch sel mu P) {V : Type} (y : V) : Prop :=
  ∃ (F : (mtildeKGSD W Ch sel mu).EqFun) (h : F.1 ∈ (mtildeGSD W Ch sel mu P).EqFun),
    HEq ((mtildeKGSD W Ch sel mu).res (mtildeKOk W Ch sel mu hX) F) y ∧ x = ⟨F.1, h⟩

end Forms

section Crd

attribute [local instance] GlobalTheory.Mem.Col2.starE

def IsCrd {B : Base} {px : PreX B.toPre} (I : ColIn B px) (hX : B.fields.Ok) (a : I.ι) {V M : Type} [AddCommGroup M] [Module ℂ M]
    (e : Df.MtCx I a ≃ₗ[ℂ] M) (y : V) (v : M) : Prop :=
  ∃ x : Formalism.L2.Col.MtildeV (Pr := B.primes px) B.wts I.Ch I.sel (I.tup a) (TC.Ps I),
    IsFormOf (Pr := B.primes px) B.wts I.Ch I.sel (I.tup a) hX (TC.Ps I) x y ∧ v = e (Df.toCx I hX a x)

end Crd

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B}

abbrev famAll {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)} (t : RowsT K w Z Wt p0) :=
  (R3.famR (w.st Z) w.I t.hX Set.univ t.r.z.Xg t.r.z.tr).A


set_option genInjectivity false in
set_option genSizeOfSpec false in

structure RXs {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)} (t : RowsT K w Z Wt p0) : Type 1 where
  all : AllT (w.st Z).toD7 (famAll t) (R3.lev0 w.I) (R3.chr0 w.I) (R3.lev1 w.I) (R3.chr1 w.I) p0 (tAll w.I)
    (t.r.z.R.eG.trans t.r.z.cG)
  jA_use : ∀ s, SameOn (all.jA (t.r.Y.tup s)) (t.r.Y.jA s)
  movedReadingSameMaps_baseReading_agrees : ∀ s, SameOn (all.jA0 (t.r.Y.tup s)) (t.r.Y.jA0 s)
  eMt_use : ∀ i s, SameOn (all.eMt i (t.r.Y.tup s)) (t.r.Y.eMt i s)
  e : ∀ a : w.C.Tup, Df.MtCx w.I a ≃ₗ[ℂ] Z.W.Amb a
  eMt0 : ∀ u F, Df.SameForm w.I w.l u w.I.mu0 F ((Z.W.eMt0 u).symm (e w.C.mu0 F))
  eMtTw : ∀ u (a : w.C.Tup) F, Df.SameForm w.I w.l u a F ((Z.W.eMtTw u a).symm (e a F))
  crd : ∀ (a : w.C.Tup) y, IsCrd w.I t.hX a (e a)
    (R3.rowForm (D := (w.st Z).toD7) (famAll t) (R3.lev1 w.I) (R3.chr1 w.I) (tAll w.I a) y) (all.jA a y)
  io : ∀ μ j, ¬ Formalism.IndefR.RecTie.Used0 (w.D Z) μ → Z.W.io μ j = 0 ∧ p0.s.io μ j = 0
  sha : GlobalTheory.MemN.ShaOK B.toPre Z.W.shaLen
  laws : Formalism.L2.Pj.LawsCore t.r.z.core.toCore
  canon : t.r.z.core.Q.Canon
  rank : ∀ j, 1 ≤ (t.r.z.core.Q.Dw j).p + (t.r.z.core.Q.Dw j).q
  pb : t.r.z.core.pb = f.P.pb
  std : t.r.z.Std

def RX : RPosition := fun _ _ _ _ _ _ _ _ t => RXs t

end GlobalTheory.Mem.Top.Bl

end
end

section

noncomputable section

namespace GlobalTheory.Mem.Top.Bl

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure GoodO (D : D7) (nch : NChoice D) (xd : ThData D) : Prop where
  tw : ∃ I : TwIn D, I.E = twEOf xd ∧ DQ.GoodAllAt D nch I ∧ GlobalTheory.HeightCounting.GoodCl D nch I
  sep : ∀ v v', D.what₂.muAt v ≠ D.what₂.mu0 → D.what₂.muAt v' ≠ D.what₂.mu0 → nch.twI v ≠ nch.twI v' → Disjoint (nch.Q v) (nch.Q v')

variable {B : Base} {f : Fr B.toPre} {T : TwDat B}

structure Wit (𝒮 : Slots) (K : Ctx) (w : ColW B f T) (Z : w.Lt) (O : Obj2 (w.D Z)) : Type 1 where
  isOver : K.Over B.toPre
  forced : Forced K B T
  Wt : Set B.places.Pl
  pin : ColPin w
  coh : Coh B T
  vol : Formalism.L2.Theta.VolTieG (w.D Z)
  col : ColumnDataSplitPrimes K w Z
  what₂ : RowsT K w Z Wt O.p0
  rx : 𝒮.Rx K B f T w Z Wt O.p0 what₂
  lev : O.lev = col.full.1.base.lev0
  errX : O.errX = Formalism.L2.Herm.toErrXS col.full.1
  n : NchT w Z Wt O.nch
  nx : 𝒮.Nx K B f T w Z Wt O.p0 what₂ O.nch n O.xd
  sx : 𝒮.Sx K B f T w Z Wt O.p0 what₂ col.toColT
  ker0 : KerFam (w.D Z) col.Gt col.cmp (w.tw Z) O.Gy
  ker_eq : (⟨O.gatT, O.cmp, O.tw, O.ker⟩ : Σ (Gt : GatTies (w.D Z)) (cmp : LatCmp (w.D Z)) (tw : TwForms (w.D Z)),
    KerFam (w.D Z) Gt cmp tw O.Gy) = ⟨col.Gt, col.cmp, w.tw Z, ker0⟩
  ker : KerT col.toColT O.X O.Gy ker0
  div : DivT n O.X
  th : ThT n O.th
  obj : ObjT O what₂
  ox : 𝒮.Ox K B f T w Z Wt O what₂
  real : Formalism.L2.Theta.RealTied (w.D Z)
  dsig_eq : ∀ τ, Z.S.dsig τ = Vol.trueDsig B.R (B.hc τ)
  gauge : O.gauge.IsGauge
  good : GoodO (w.D Z) O.nch O.xd

def Built.wit {𝒮 : Slots} {K : Ctx} {w : ColW B f T} {Z : w.Lt} {c : V4.Core K (w.st Z) f T} (b : Built 𝒮 K w Z c)
    (h : GoodO (w.D Z) c.O.nch c.O.xd) : Wit 𝒮 K w Z c.O :=
  { b with isOver := c.isOver, forced := c.forced, Wt := c.Wt, vol := (b.g Z.W Z.V Z.S Z.N).1, real := c.real, dsig_eq := c.dsig_eq,
           gauge := c.gauge_def, good := h }

structure WPt (𝒮 : Slots) (K : Ctx) : Type 1 where
  B : Base
  f : Fr B.toPre
  T : TwDat B
  w : ColW B f T
  Z : w.Lt
  O : Obj (w.D Z)
  x : Wit 𝒮 K w Z (ofObj O)

def WPt.Is {𝒮 : Slots} {K : Ctx} (p : WPt 𝒮 K) (D : D7) (O : Obj D) : Prop := (⟨D, O⟩ : Σ D : D7, Obj D) = ⟨p.w.D p.Z, p.O⟩

abbrev PinT (𝒮 : Slots) (Bd : GlobalTheory.Fc.BdT) : Type 1 := ∀ (K : Ctx) (p : WPt 𝒮 K) (c : ℝ), Bd (p.w.D p.Z) p.O c → Prop

def linkOf {𝒮 : Slots} {Bd : GlobalTheory.Fc.BdT} (P : PinT 𝒮 Bd) : GlobalTheory.Fc.LkT Bd := fun K β c b =>
  ∃ (p : WPt 𝒮 K) (b' : Bd (p.w.D p.Z) p.O c), P K p c b' ∧
    (⟨β.D, β.O, b⟩ : Σ (D : D7) (O : Obj D), Bd D O c) = ⟨p.w.D p.Z, p.O, b'⟩

end GlobalTheory.Mem.Top.Bl

end
end
