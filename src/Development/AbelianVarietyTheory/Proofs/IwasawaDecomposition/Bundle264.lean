module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.RatDatOfReal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1389
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle305
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1105
import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
import Formalism.LocalToGlobal.IndefiniteReal.ExistsSumOfMemISup
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AutomorphicArithmetic.WeightCongruences.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle256
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle253
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle003
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ComplexMultiplicationJPremises
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle214
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle254
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle255
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.AlgebraMapNormOfBasisOneSqrt
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Mathlib.RingTheory.DedekindDomain.Factorization

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.RatDatRExp

theorem chi_val_small {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (hL : R.toLevCh.Is A.μ0) (hV : GlobalTheory.RealGeo.ValKs R) (i : Fin D.R.m) (PP : Pl D.host.E) (hP : PP ∈ R.Pg)
    (u : (kP PP)ˣ) :
    ∃ y : Ks, ((R.chi ((i : ℕ) + 1) PP u : ℂˣ) : ℂ) = D.what₂.embLL (algebraMap Ks D.what₂.LL y) := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u : kP PP)
  have ha0 : (a : D.host.E) ≠ 0 := by
    intro h
    have h0 : a = 0 := RingOfIntegers.coe_eq_zero_iff.mp h
    apply u.ne_zero
    rw [← ha, h0, map_zero]
  let k : D.host.Eˣ := Units.mk0 _ ha0
  obtain ⟨ι, hι, hint, happ⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨e, he, -⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι hι hint happ PP
  have hv : PP.valuation D.host.E (k : D.host.E) ≤ 1 := PP.valuation_le_one a
  have hinf := (GlobalTheory.UnramCharUnique.loc_parts he _ hv).1
  obtain ⟨y, hy⟩ := hV i (Formalism.L2.JoinChr.locU he.1 k) hinf
  have h1 := (hL.mu0 i).2 PP e he k (Formalism.L2.JoinChr.locU he.1 k) rfl
  have h2 := hL.chi i PP hP a k u rfl ha.symm
  refine ⟨y⁻¹, ?_⟩
  rw [MonoidHom.inv_apply] at h2
  have h3 : R.chi ((i : ℕ) + 1) PP u = ((R.C.mu0 i).locK PP k)⁻¹ := by rw [← h2, inv_inv]
  rw [h3, Units.val_inv_eq_inv_val, ← h1, hy, map_inv₀, map_inv₀]

end GlobalTheory.Mem.RatDatRExp

namespace GlobalTheory.Mem.RatDatRExp

theorem rhoStab_chiInLL0 : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (C : Formalism.L2.Pj.CoreJ D) [Algebra C.Q.c.F D.what₂.LL] (R : RealDat3 D A3 C.Q.c.F) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (g : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1) (kKs : C.Q.c.F →+* ↥D.LL0) (hk : ∀ x, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap C.Q.c.F D.what₂.LL x), Pins R F cG → GlobalTheory.RealGeo.InGeo g → ∀ j, 1 ≤ j → j ≤ D.R.m → NX.RhoStab (NX.ratDatR R cG kKs hk) j ∧ NX.ChiInLL0 (NX.ratDatR R cG kKs hk) j := by
  intro D G _ _ Pl0 I0 T A3 C _ R F cG B kKs hk hP _ j _ _
  refine ⟨?_, ?_⟩
  · intro g0 x hx
    change (R.FW (NX.idxOf D j)).ρ g0 x ∈ (R.FW (NX.idxOf D j)).WK
    change x ∈ (R.FW (NX.idxOf D j)).WK at hx
    by_cases hK : Formalism.IndefR.FWT.ActKeeps (κ := B.κ) B.O (NX.idxOf D j)
    · obtain ⟨hf, heq⟩ := (B.rhoGeo (NX.idxOf D j)).1 hK g0 ((B.fw.e (NX.idxOf D j)).symm ⟨x, hx⟩)
      rw [LinearEquiv.apply_symm_apply] at heq
      rw [← heq]
      exact Submodule.coe_mem _
    · rw [(B.rhoGeo (NX.idxOf D j)).2 hK g0]
      exact hx
  · intro g0
    change (((R.FW (NX.idxOf D j)).chi g0 : D.what₂.LLˣ) : D.what₂.LL) ∈ D.LL0
    have hL := hP.char.base.lev
    have hW := hP.char.base.grp.chiW
    have hV := hP.keep.valKs
    have hy : ∀ PP : R.Pg, ∃ y : C.Q.c.F,
        ((R.chi ((NX.idxOf D j : ℕ) + 1) PP.1 (Matrix.GeneralLinearGroup.det (R.eG g0 PP)) : ℂˣ) : ℂ) =
          D.what₂.embLL (algebraMap C.Q.c.F D.what₂.LL y) := fun PP =>
      chi_val_small R.toRealDat hL hV (NX.idxOf D j) PP.1 PP.2 _
    choose y hy using hy
    have h1 := hW (NX.idxOf D j) g0
    rw [Finset.prod_congr rfl (fun PP _ => hy PP), ← map_prod, ← map_prod] at h1
    have h2 := D.what₂.embLL.injective h1
    rw [h2, ← hk]
    exact (kKs _).2

end GlobalTheory.Mem.RatDatRExp
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.RatLift

theorem exists_rat_lift_mem_part : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Inputs D → Pins R F cG → Holds R F → GlobalTheory.CuspMult.MultEq R.toRealDat → (∀ χ ∈ A3.A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → ∀ p, R.EEp3 p ≠ ⊥ → ∀ i, (R.toCx3 F).Wp i p ⊓ LinearMap.range ((R.toCx3 F).w0C false i) ≠ ⊥ → ∃ x : Fin ((lv (F.fc (R.toCx3 F).zs) false).dZ i A3.A.μ0) → D.what₂.LL, (R.toCx3 F).tC F.cr false i A3.A.μ0 (cpt A3.A.v0.embedding x) ∈ (R.toCx3 F).Wp i p ∧ x ≠ 0 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG _ hP hH _ _ p _ i hB
  have hRw := complex_data_conditions_base_level_of_primitive_links hH.ok hH.sep hP.char hH.prim
  have hk : (R.toCx3 F).KForm false := hRw.kForm
  have he : (R.toCx3 F).EWnorm false := hRw.ewNorm
  have hn : 0 < (R.toCx3 F).nP false := hRw.h4pos.2.2 false
  have h5 : (R.toCx3 F).H5 F.cr false := hRw.lifts0.1
  have hr : (R.toCx3 F).RATth F.cr false := hRw.ratTh
  have h3W : (R.toCx3 F).H3W F.cr false := hRw.liftHyp0.h3W
  have ht : (lv (F.fc (R.toCx3 F).zs) false).Types := hRw.types0
  have hK : ∀ y, y ∈ ⨆ q, (R.toCx3 F).WpK false i q := fun y => CxData.liftsK ht hk he hn h5 hr h3W i y
  have hc0 : cpt A3.A.v0.embedding (0 : Fin ((R.toCx3 F).dW false i) → D.what₂.LL) = 0 := by
    funext l; simp [cpt]
  have hWpK : (R.toCx3 F).WpK false i p ≠ ⊥ := by
    intro h0
    apply hB
    rw [eq_bot_iff]
    intro w hw
    let M : Submodule ℂ ((R.toCx3 F).W i) :=
      ⨆ q, ⨆ (_ : q ≠ p), (R.toCx3 F).Wp i q ⊓ LinearMap.range ((R.toCx3 F).w0C false i)
    have hrat : ∀ y, (R.toCx3 F).w0C false i (cpt A3.A.v0.embedding y) ∈ M := by
      intro y
      refine Submodule.iSup_induction _ (motive := fun y => (R.toCx3 F).w0C false i (cpt A3.A.v0.embedding y) ∈ M)
        (hK y) ?_ ?_ ?_
      · intro q z hz
        by_cases hq : q = p
        · subst hq
          rw [h0] at hz
          rw [(Submodule.mem_bot _).1 hz, hc0, map_zero]
          exact M.zero_mem
        · exact (le_iSup₂ (f := fun q (_ : q ≠ p) => (R.toCx3 F).Wp i q ⊓ LinearMap.range ((R.toCx3 F).w0C false i)) q hq)
            ⟨hz, ⟨_, rfl⟩⟩
      · rw [hc0, map_zero]
        exact M.zero_mem
      · intro a c ha hc
        have : cpt A3.A.v0.embedding (a + c) = cpt A3.A.v0.embedding a + cpt A3.A.v0.embedding c := by
          funext l; simp [cpt]
        rw [this, map_add (f := _)]
        exact M.add_mem ha hc
    have hrange : LinearMap.range ((R.toCx3 F).w0C false i) ≤ M := by
      rw [LinearMap.range_eq_map, ← (Pi.basisFun ℂ (Fin ((R.toCx3 F).dW false i))).span_eq, Submodule.map_span,
        Submodule.span_le]
      rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
      have : (Pi.basisFun ℂ (Fin ((R.toCx3 F).dW false i)) k) =
          cpt A3.A.v0.embedding (Pi.single k (1 : D.what₂.LL)) := by
        funext l
        simp only [Pi.basisFun_apply, cpt, Pi.single_apply]
        split_ifs <;> simp
      rw [this]
      exact hrat _
    have hperp : M ≤ (ℂ ∙ w)ᗮ := by
      refine iSup₂_le fun q hq => ?_
      intro v hv
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
      exact (hH.prim.sumW i).1 p q (Ne.symm hq) w hw v hv
    have hww := hperp (hrange hw.2)
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hww
    exact (Submodule.mem_bot ℂ).2 (inner_self_eq_zero.1 hww)
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWpK
  obtain ⟨x, rfl⟩ := ((R.toCx3 F).liftMat_bij F.cr false hk he hn h5 hr i A3.A.μ0).2 y
  refine ⟨x, ?_, ?_⟩
  · have hy' : (R.toCx3 F).w0C false i (cpt A3.fam3.base3.v0.embedding
        ((R.toCx3 F).liftMat F.cr false i A3.A.μ0 *ᵥ x)) ∈ (R.toCx3 F).Wp i p := hy
    rw [(R.toCx3 F).key_lift F.cr false h5 hr i A3.A.μ0 x] at hy'
    exact hy'
  · rintro rfl
    exact hy0 (Matrix.mulVec_zero _)

end GlobalTheory.RatLift
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.HeightCounting
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CenFrame

section Local

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

abbrev Os (s : ReciprocityTheory.Aut.SplitPlace L) : Type := ↥(s.v.adicCompletionIntegers (maximalRealSubfield L))

structure IsResidue (s : ReciprocityTheory.Aut.SplitPlace L) {k : Type} [CommRing k] (φ : Os s →+* k) : Prop where
  surj : Function.Surjective φ
  ker : ∀ x : Os s, φ x = 0 ↔ Valued.v (x : s.v.adicCompletion (maximalRealSubfield L)) < 1

def IsCompOf (s : ReciprocityTheory.Aut.SplitPlace L) (κ : Formalism.AUTREP.GAf L n) (y : GL (Fin n) (Os s)) : Prop :=
  ∀ a c, ((y.val a c : Os s) : s.v.adicCompletion (maximalRealSubfield L)) = (s.loc n κ).val a c

end Local

def colMat {k : Type} [CommRing k] {n : ℕ} (v : Fin n → k) (m : Fin n) : Matrix (Fin n) (Fin n) k :=
  1 + Matrix.vecMulVec v (Pi.single m 1)

variable {D : D7}

def FrameRed {V : HSp D} {n : ℕ} (hn : V.rank = n) (P : principalLevelFrame.RowPsi V n) (β : GL (Fin V.rank) (EAf D))
    (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (φ : Os s →+* kP s.w) (b : GL (Fin n) (kP s.w)) : Prop :=
  ∀ κ ∈ ReciprocityTheory.Aut.Umax D.host.E n, ∀ y, IsCompOf s κ y → ∀ a c : Fin n,
    (redFn β s.w (finE V (P.ψ κ))).val (Fin.cast hn.symm a) (Fin.cast hn.symm c) =
      (b * Matrix.GeneralLinearGroup.map φ y * b⁻¹).val a c

variable {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A3.A Ks} {F : Face D A3.A} {X0 : BaseLevelRowSide D}

def CenRead (Y : R3.Read (A3 := A3) R F X0) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) : Prop :=
  ∀ (i : Fin D.R.m) (t : T) (z : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))) (a : MonoidAlgebra D.what₂.LL G),
    (∀ g, D.what₂.embLL (a.coeff g) = (z : MonoidAlgebra ℂ (G0g D.nd)).coeff ((R.eG.trans cG) g)) → ∀ x,
      D.ntypes.cenMt (Y.tup t) ((i : ℕ) + 1) z (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t x)) =
        D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (((A3.A.fam.L i t).S.lvlOp (A3.A.fam.L i t).r (A3.A.fam.lvlA F.P0 F.ψ0).P
          (A3.A.fam.lvlA F.P0 F.ψ0).ψ a).mulVec x))

end GlobalTheory.CenFrame

end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical

namespace GlobalTheory.Mem.Pre

variable (B : Pre)

theorem splitsC_level {p : ℕ} (hp : p ∈ B.host.levelPrimes) : SplitsC B.host.E p :=
  (GlobalTheory.HostSplit.split_of_one_mod B.R B.host p (B.level_cond p hp).1 (B.level_cond p hp).2).1

theorem splitsC_g (k : Fin 2) : SplitsC B.host.E (B.host.g k) := B.splitsC_level (B.host.g_level k)

theorem splitsC_pde : SplitsC B.host.E B.host.pde := B.splitsC_level B.host.pde_level.1

theorem splitsC_pde' : SplitsC B.host.E B.host.pde' := B.splitsC_level B.host.pde_level.2

def EvenExp : Prop := ∀ j, UpperTheory.MUQ (_root_.Formalism.L2.Host.embPsi B.host) (fun τ : B.R.Psi => (B.hc τ).e j)

theorem nonempty_hframe (h : B.EvenExp) : Nonempty (HFrame B.host fun j τ => (B.hc τ).e j) :=
  GlobalTheory.T.nonempty_hostHeckeCharacterFrame B.R B.host _ B.splitsC_g B.splitsC_pde B.splitsC_pde' (fun j τ => (B.hc τ).e_int j) h

end GlobalTheory.Mem.Pre

namespace GlobalTheory.Mem.Chr

end GlobalTheory.Mem.Chr

end
end

section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField Pointwise

namespace GlobalTheory.Mem.FieldsEx

theorem isFrob_conj {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    {v : HeightOneSpectrum (𝓞 K)} {σ : L ≃ₐ[K] L} (h : IsFrob L v σ) (τ : L ≃ₐ[K] L) :
    IsFrob L v (τ * σ * τ⁻¹) := by
  obtain ⟨P, hP, hl, h⟩ := (isFrob_iff L v σ).1 h
  exact (isFrob_iff L v _).2 ⟨τ • P, inferInstance, inferInstance, h.conj τ⟩

theorem isFrob_one_of_fix {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    {v : HeightOneSpectrum (𝓞 K)} {σ : L ≃ₐ[K] L} (h : IsFrob L v σ) (F : IntermediateField K L)
    [NumberField F] (hF : ∀ x ∈ F, σ x = x) : IsFrob F v 1 := by
  obtain ⟨P, hP, hl, h⟩ := h
  refine ⟨P.under (𝓞 F), inferInstance, inferInstance, fun x => ?_⟩
  rw [Ideal.under_def, Ideal.mem_comap, one_smul, map_sub, map_pow]
  have h1 : σ • algebraMap (𝓞 F) (𝓞 L) x = algebraMap (𝓞 F) (𝓞 L) x :=
    RingOfIntegers.ext (hF _ (x : F).2)
  have := h (algebraMap (𝓞 F) (𝓞 L) x)
  rwa [h1] at this

theorem closure_frob_eq_top : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] (S : Set (HeightOneSpectrum (𝓞 K))), S.Finite →
    (∀ (F : Type) [Field F] [NumberField F] [Algebra K F],
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → IsFrob F v 1) → ∀ σ : F ≃ₐ[K] F, σ = 1) →
    Subgroup.closure {σ : L ≃ₐ[K] L | ∃ v : HeightOneSpectrum (𝓞 K), v ∉ S ∧ IsFrob L v σ} = ⊤ := by
  intro K L _ _ _ _ _ _ S _ h
  set H := Subgroup.closure {σ : L ≃ₐ[K] L | ∃ v : HeightOneSpectrum (𝓞 K), v ∉ S ∧ IsFrob L v σ} with hH
  have hn : H.Normal := by
    refine ⟨fun n hn g => ?_⟩
    induction hn using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨v, hv, hx⟩ := hx
      exact Subgroup.subset_closure ⟨v, hv, isFrob_conj hx g⟩
    | one => simp
    | mul x y _ _ hx hy =>
      have := H.mul_mem hx hy
      convert this using 1
      group
    | inv x _ hx =>
      have := H.inv_mem hx
      convert this using 1
      group
  let F := IntermediateField.fixedField H
  have : IsGalois K F := IsGalois.of_fixedField_normal_subgroup H
  have : NumberField F := NumberField.of_module_finite K F
  have h1 := h F fun v hv => by
    obtain ⟨σ, hσ⟩ := exists_isFrob L v
    exact isFrob_one_of_fix hσ F fun x hx =>
      (IntermediateField.mem_fixedField_iff _ _).1 hx σ (Subgroup.subset_closure ⟨v, hv, hσ⟩)
  refine eq_top_iff.2 fun τ _ => ?_
  rw [← IntermediateField.fixingSubgroup_fixedField H, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have h2 := τ.restrictNormal_commutes F ⟨x, hx⟩
  rw [h1 (τ.restrictNormal F)] at h2
  exact h2.symm

end GlobalTheory.Mem.FieldsEx
end

section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.Fld

theorem card_le_of_pow_eq_self {R : Type} [CommRing R] [IsDomain R] [Finite R] {q : ℕ} (hq : 1 < q)
    (h : ∀ x : R, x ^ q = x) : Nat.card R ≤ q := by
  classical
  have := Fintype.ofFinite R
  have hd : (Polynomial.X ^ q - Polynomial.X : Polynomial R).natDegree = q := by
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt (by simpa using hq), Polynomial.natDegree_X_pow]
  have hne : (Polynomial.X ^ q - Polynomial.X : Polynomial R) ≠ 0 := by
    intro h0
    rw [h0, Polynomial.natDegree_zero] at hd
    omega
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
  refine le_trans (Polynomial.card_le_degree_of_subset_roots ?_) hd.le
  intro x _
  rw [Polynomial.mem_roots hne]
  simp [h x]

theorem exists_two_primes_of_isFrob_one (K F : Type) [Field K] [NumberField K] [Field F] [NumberField F]
    [Algebra K F] (σ : F ≃ₐ[K] F) (hσ : σ ≠ 1) :
    ∃ T : Set (HeightOneSpectrum (𝓞 K)), T.Finite ∧ ∀ v : HeightOneSpectrum (𝓞 K), v ∉ T → IsFrob F v 1 →
      ∃ P Q : HeightOneSpectrum (𝓞 F), P ≠ Q ∧ P.asIdeal.LiesOver v.asIdeal ∧ Q.asIdeal.LiesOver v.asIdeal ∧
        Ideal.absNorm P.asIdeal = Ideal.absNorm v.asIdeal ∧ Ideal.absNorm Q.asIdeal = Ideal.absNorm v.asIdeal := by
  let e : 𝓞 F ≃ₐ[𝓞 K] 𝓞 F := RingOfIntegers.mapAlgEquiv σ
  obtain ⟨θ, hθ⟩ : ∃ θ : 𝓞 F, e θ - θ ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply hσ
    ext x
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) x
    have h : ∀ a : 𝓞 F, σ (algebraMap (𝓞 F) F a) = algebraMap (𝓞 F) F a := fun a =>
      congrArg (algebraMap (𝓞 F) F) (sub_eq_zero.1 (hc a))
    simp only [map_div₀, h, AlgEquiv.one_apply]
  have hfin : {P : HeightOneSpectrum (𝓞 F) | P.asIdeal ∣ Ideal.span {e θ - θ}}.Finite :=
    Ideal.finite_factors (by simpa using hθ)
  refine ⟨{v | ∃ P : HeightOneSpectrum (𝓞 F), P.asIdeal ∣ Ideal.span {e θ - θ} ∧
    P.asIdeal.under (𝓞 K) = v.asIdeal}, ?_, ?_⟩
  · refine Set.Finite.of_finite_image (f := fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal)
      ((hfin.image (fun P => P.asIdeal.under (𝓞 K))).subset ?_) (fun a _ b _ h => HeightOneSpectrum.ext h)
    rintro _ ⟨v, ⟨P, hP, hv⟩, rfl⟩
    exact ⟨P, hP, hv⟩
  rintro v hv ⟨P, hP, hPo, hx⟩
  have hvp := v.isPrime
  have hne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P
  have hfP : Finite (𝓞 F ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot _ hne
  have hfv : Finite (𝓞 K ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  have hq : 1 < Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    exact Finite.one_lt_card
  have hle : Nat.card (𝓞 F ⧸ P) ≤ Nat.card (𝓞 K ⧸ v.asIdeal) := by
    have h0 : Ideal.absNorm v.asIdeal = Nat.card (𝓞 K ⧸ v.asIdeal) := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rw [← h0]
    refine card_le_of_pow_eq_self hq fun x => ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    have := hx x
    rw [one_smul] at this
    rw [← map_pow]
    exact (Ideal.Quotient.eq.2 this).symm
  have hinj : Function.Injective (algebraMap (𝓞 K ⧸ v.asIdeal) (𝓞 F ⧸ P)) := FaithfulSMul.algebraMap_injective _ _
  have hbij : Function.Bijective (algebraMap (𝓞 K ⧸ v.asIdeal) (𝓞 F ⧸ P)) :=
    hinj.bijective_of_nat_card_le hle
  have hN : Ideal.absNorm P = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    exact (Nat.card_eq_of_bijective _ hbij).symm
  have hQo : (P.comap e).LiesOver v.asIdeal := inferInstance
  have hQ : (P.comap e).IsPrime := Ideal.comap_isPrime _ _
  have hQne : P.comap e ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot _
  refine ⟨⟨P, hP, hne⟩, ⟨P.comap e, hQ, hQne⟩, ?_, hPo, hQo, hN, ?_⟩
  · intro h
    have h' : P = P.comap e := congrArg HeightOneSpectrum.asIdeal h
    apply hv
    refine ⟨⟨P, hP, hne⟩, ?_, hPo.over.symm⟩
    rw [Ideal.dvd_span_singleton]
    obtain ⟨a, ha⟩ := hbij.2 (Ideal.Quotient.mk P θ)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    have h1 : algebraMap (𝓞 K) (𝓞 F) a - θ ∈ P := Ideal.Quotient.eq.1 ha
    have h2 : e (algebraMap (𝓞 K) (𝓞 F) a - θ) ∈ P := by
      have := h' ▸ h1
      exact this
    rw [map_sub, AlgEquiv.commutes] at h2
    have := P.sub_mem h1 h2
    show e θ - θ ∈ P
    convert this using 1
    ring
  · show Ideal.absNorm (P.comap e) = _
    rw [← hN, Ideal.absNorm_apply, Submodule.cardQuot_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    refine Nat.card_congr (Ideal.quotientEquiv (P.comap e) P e.toRingEquiv ?_).toEquiv
    exact (Ideal.map_comap_of_surjective (e.toRingEquiv : 𝓞 F →+* 𝓞 F) e.surjective P).symm

end GlobalTheory.Mem.Fld
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical


theorem _root_.GlobalTheory.T.fullFlagBundleMorphism_bijective_fieldPoints : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∀ g : Y₁.X ⟶ Y₂.X, g ≫ f₂ = f₁ → (∀ (K : Type) [Field K] (p : Sp K ⟶ Y₁.X), CoBear Eb S₁ φ₁ S₂ φ₂ (p ≫ f₁) p (p ≫ g)) → ∀ (K : Type) [Field K], Function.Bijective (fun p : Sp K ⟶ Y₁.X => p ≫ g) := by
  first | exact @GlobalTheory.FlagBundle.CoBear₂ | exact GlobalTheory.FlagBundle.CoBear₂ | (intros; apply GlobalTheory.FlagBundle.CoBear₂ <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical


theorem _root_.GlobalTheory.T.fullFlagBundle_functionFieldMap_dominates_localRings : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∀ ψ : Y₂.Fn →ₐ[F] Y₁.Fn, ψ.comp φ₂ = φ₁ → CoBear Eb S₁ φ₁ S₂ φ₂ ((ratOf Y₁).pt ≫ f₁) (ratOf Y₁).pt (spMap ψ.toRingHom ≫ (ratOf Y₂).pt) → ∀ y : Y₁.X, ∃ y' : Y₂.X, ∀ a ∈ (ratOf Y₂).O y', ψ a ∈ (ratOf Y₁).O y := by
  first | exact @GlobalTheory.FlagBundle.dominates_O | exact GlobalTheory.FlagBundle.dominates_O | (intros; apply GlobalTheory.FlagBundle.dominates_O <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical


theorem _root_.GlobalTheory.T.fullFlagBundleMorphism_bearsFlags_of_generic : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∀ ψ : Y₂.Fn →ₐ[F] Y₁.Fn, ψ.comp φ₂ = φ₁ → CoBear Eb S₁ φ₁ S₂ φ₂ ((ratOf Y₁).pt ≫ f₁) (ratOf Y₁).pt (spMap ψ.toRingHom ≫ (ratOf Y₂).pt) → ∀ g : Y₁.X ⟶ Y₂.X, (ratOf Y₂).IsHom (ratOf Y₁) ψ g → ∀ (K : Type) [Field K] (p : Sp K ⟶ Y₁.X), CoBear Eb S₁ φ₁ S₂ φ₂ (p ≫ f₁) p (p ≫ g) := by
  first | exact @GlobalTheory.FlagBundle.coBear_comp_of_isHom | exact GlobalTheory.FlagBundle.coBear_comp_of_isHom | (intros; apply GlobalTheory.FlagBundle.coBear_comp_of_isHom <;> assumption)
end
