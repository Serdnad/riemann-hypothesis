module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1184
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle200
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle193
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle237
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle236
public import Formalism.LocalToGlobal.Columns.DecoFin
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle238
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle010
import Formalism.LocalToGlobal.IndefiniteReal.Bundle014
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle133
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle136

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows
open Formalism.IndefR.CxPass Formalism.IndefR.CxPass.LevelOperators

namespace GlobalTheory.GoodModelVec

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]



theorem actL_coord (R : RealDat D A Ks) (hr : R.grp_red_L) (hj : R.models_jV) (i : Fin D.R.m) (hc : (R.cV i).Is) (t : T0)
    (g : G) (x : (A.fam.L i t).S.Forms) (ℓ : (R.cV i).W →ₗ[ℂ] ℂ) :
    actL (Vc D i) (R.βV i) (R.datVt i t) (R.eG g) (fun h => ℓ (R.extV i t (R.jV i t x) h)) =
      fun h => ℓ (R.extV i t (R.jV i t ((A.fam.L i t).r g x)) h) := by
  have hT := GlobalTheory.RationalFormsAction.isTranslate_act_V R hr hj i t g x
  have hk : ∃ κ, IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) (R.eG g) κ := by
    obtain ⟨κ, h1, -⟩ := GlobalTheory.LiftEquivariance.exists_adelic_lift hT
    exact ⟨κ, h1⟩
  funext h
  refine (GlobalTheory.SecLift.actL_apply hk _ h).trans ?_
  have hs := hk.choose_spec
  have e1 := finE_eq (Vc D i) hk.choose
  have hq : (finHom (Vc D i)).rangeRestrict hk.choose ∈ (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q := by
    show Formalism.UG.bc (swapAE D) (finHom (Vc D i) hk.choose) ∈ lev _ _ _ _
    rw [← e1]
    exact ⟨hs.2.1, Subgroup.mem_top _⟩
  have hl : GlobalTheory.IndefiniteRowSideFullHecke.TranslateRepresentations.LiftsTo (Vc D i) (R.βV i) (R.datVt i t) ⟨(finHom (Vc D i)).rangeRestrict hk.choose, hq⟩ (R.eG g) := by
    show rTup (R.βV i) (R.datVt i t) (Formalism.UG.bc (swapAE D) (finHom (Vc D i) hk.choose)) = R.eG g
    rw [← e1]; exact hs.2.2
  have hT2 : ∀ u, (R.HV i t).e ((R.jV i t) (((A.fam.L i t).r g) x)) u =
      ((((levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch ⟨(finHom (Vc D i)).rangeRestrict hk.choose, hq⟩)⁻¹ : ℂˣ) : ℂ) •
        (R.HV i t).e ((R.jV i t) x) (u * (finHom (Vc D i)).rangeRestrict hk.choose) := hT.2 _ hl
  have h2 := GlobalTheory.SecLift.coord_translate (R.cV i) hc hs.1 _ hT2 ℓ h
  have ec := GlobalTheory.LiftEquivariance.ch_eq (V := Vc D i) (β := R.βV i) (L := R.datVt i t) ⟨(finHom (Vc D i)).rangeRestrict hk.choose, hq⟩
  have e2 : levFn (R.βV i) (flagL (R.datVt i t)) (Formalism.UG.bc (swapAE D) ((finHom (Vc D i)) hk.choose)) =
      levFn (R.βV i) (flagL (R.datVt i t)) (finE (Vc D i) hk.choose) := by rw [e1]
  have hc' : ((((levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch ⟨(finHom (Vc D i)).rangeRestrict hk.choose, hq⟩ : ℂˣ)) : ℂ) =
      levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) hk.choose := congrArg Units.val (ec.trans e2)
  rw [Units.val_inv_eq_inv_val, hc'] at h2
  exact h2.symm



theorem goodV_of_fix (R : RealDat D A Ks) (hr : R.grp_red_L) (hj : R.models_jV) (i : Fin D.R.m) (hc : (R.cV i).Is)
    (x : (A.fam.L i A.μ0).S.Forms) (hx : opF (A.fam.L i A.μ0).r (idemOf A.X) x = x) :
    GlobalTheory.LiftRows.GoodV R i (R.jV i A.μ0 x) := by
  intro ℓ
  let Φ : (R.HV i A.μ0).H →ₗ[ℂ] (GA D (Vc D i) → ℂ) := ℓ.compLeft (GA D (Vc D i)) ∘ₗ R.extV i A.μ0
  have hΦ : ∀ y, Φ y = fun h => ℓ (R.extV i A.μ0 y h) := fun _ => rfl
  have key : ∀ g, Φ (R.jV i A.μ0 ((A.fam.L i A.μ0).r g x)) =
      actL (Vc D i) (R.βV i) (R.datVt i A.μ0) (R.eG g) (Φ (R.jV i A.μ0 x)) := fun g =>
    (actL_coord R hr hj i hc A.μ0 g x ℓ).symm
  have hs : ∀ a, RealDat.eC (A := A) (sg0 D A) a = D.what₂.embLL ((idemOf A.X).coeff a) := fun a => by
    show sg0 D A _ = _
    rw [sg0, sgAt_mk D.what₂.embLL R.hv0]
  have e1 : Φ (R.jV i A.μ0 (opF (A.fam.L i A.μ0).r (idemOf A.X) x)) =
      gaL (Vc D i) (R.βV i) (R.datVt i A.μ0) R.eG (RealDat.eC (A := A) (sg0 D A)) (Φ (R.jV i A.μ0 x)) := by

    simp only [opF, gaL, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, LinearMap.map_smulₛₗ, key, hs, RingHom.id_apply]
    rfl
  rw [← hΦ, ← e1, hx]

noncomputable def goodSub (R : RealDat D A Ks) (i : Fin D.R.m) : Submodule ℂ (R.HV i A.μ0).H :=
  ⨅ ℓ : (R.cV i).W →ₗ[ℂ] ℂ, LinearMap.ker
    (gaL (Vc D i) (R.βV i) (R.datVt i A.μ0) R.eG (RealDat.eC (A := A) (sg0 D A)) ∘ₗ (ℓ.compLeft (GA D (Vc D i)) ∘ₗ R.extV i A.μ0) -
      ℓ.compLeft (GA D (Vc D i)) ∘ₗ R.extV i A.μ0)

theorem mem_goodSub (R : RealDat D A Ks) (i : Fin D.R.m) (y : (R.HV i A.μ0).H) :
    y ∈ goodSub R i ↔ GlobalTheory.LiftRows.GoodV R i y := by
  simp only [goodSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
  rfl

end GlobalTheory.GoodModelVec


open GlobalTheory.GoodModelVec in

theorem GlobalTheory.goodV_of_goodL : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PGEquiv F → ∀ (j : Fin D.R.m) (y : (R.toCx3 F).FLC j A3.A.fam.μ0), y ∈ U2.goodL A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 j → GoodV R.toRealDat j (Tw.out (s := twAt D.what₂.embLL A3.A.v0) y) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hok hC _ _ _ j y hy
  have hM := hC.base.models
  have hr := hC.base.grp.red_L
  have hfix : ∀ x ∈ BlockGood.goodR (A3.fam3.F.L j A3.A.fam.μ0) (A3.fam3.F.lvlA F.P0 F.ψ0),
      opF (A3.A.fam.L j A3.A.fam.μ0).r (idemOf A3.A.X) x = x := by
    intro x hx
    rw [goodR_eq] at hx
    obtain ⟨z, rfl⟩ := hx
    have hid := opF_goodAt_idem (A3.A.fam.L j A3.A.fam.μ0).r A3.A.X hok.ok2.irr ⊥ 1
    rw [goodAt_bot] at hid
    show opF _ (idemOf A3.A.X) (opF _ (idemOf A3.A.X * lvlIdem F.P0 F.ψ0⁻¹) z) = opF _ (idemOf A3.A.X * lvlIdem F.P0 F.ψ0⁻¹) z
    rw [opF_mul, LinearMap.comp_apply]
    exact LinearMap.congr_fun hid _
  have hy' : y ∈ Submodule.span ℂ ((R.toCx3 F).jL j A3.A.fam.μ0 ''
      (BlockGood.goodR (A3.fam3.F.L j A3.A.fam.μ0) (A3.fam3.F.lvlA F.P0 F.ψ0) : Set _)) := hy
  rw [← mem_goodSub]
  clear hy
  induction hy' using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, hx, rfl⟩ := hz
    exact (mem_goodSub _ _ _).2 (goodV_of_fix R.toRealDat hr hM.jV j (hM.cV j) x (hfix x hx))
  | zero => exact Submodule.zero_mem _
  | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
  | smul c a _ ha => exact Submodule.smul_mem _ (Links.cj (twAt D.what₂.embLL A3.A.v0) c) ha
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.PosAtBase

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem Wp3_eq {R : RealDat3 D A3 Ks}
    (hU : ∀ p c c', R.Carries p c → R.Carries p c' → R.EEc c = R.EEc c' ∧ ∀ i, R.Wc' i c = R.Wc' i c')
    {p : A3.fam3.base3.Ix} {c0 : Pl D.host.E → List ℤ → ℂ} (h0 : R.Carries p c0) (i : Fin D.R.m) :
    R.Wp3 i p = R.Wc' i c0 := by
  apply le_antisymm
  · exact iSup₂_le fun c hc ↦ ((hU p c c0 hc h0).2 i).le
  · exact le_iSup₂_of_le (f := fun c (_ : R.Carries p c) ↦ R.Wc' i c) c0 h0 le_rfl

theorem EEp3_eq {R : RealDat3 D A3 Ks}
    (hU : ∀ p c c', R.Carries p c → R.Carries p c' → R.EEc c = R.EEc c' ∧ ∀ i, R.Wc' i c = R.Wc' i c')
    {p : A3.fam3.base3.Ix} {c0 : Pl D.host.E → List ℤ → ℂ} (h0 : R.Carries p c0) :
    R.EEp3 p = R.EEc c0 := by
  apply le_antisymm
  · exact iSup₂_le fun c hc ↦ (hU p c c0 hc h0).1.le
  · exact le_iSup₂_of_le (f := fun c (_ : R.Carries p c) ↦ R.EEc c) c0 h0 le_rfl

theorem Wp3_bot {R : RealDat3 D A3 Ks} {p : A3.fam3.base3.Ix} (h : ∀ c, ¬ R.Carries p c) (i : Fin D.R.m) :
    R.Wp3 i p = ⊥ := by
  unfold RealDat3.Wp3
  simp [h]

theorem EEp3_bot {R : RealDat3 D A3 Ks} {p : A3.fam3.base3.Ix} (h : ∀ c, ¬ R.Carries p c) :
    R.EEp3 p = ⊥ := by
  unfold RealDat3.EEp3
  simp [h]

end GlobalTheory.PosAtBase

namespace GlobalTheory.PosAtBase



theorem pos_at_base {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ} (_hOk : A3.fam3.Ok3 s) (hC : R.WeakCharacterisation F) (_hE : R.toRealDat.ExAt)
    (hS : Scal R.toRealDat R.SF) (hM : MatchUp R.toRealDat R.SF)
    (hU : ∀ p c c', R.Carries p c → R.Carries p c' → R.EEc c = R.EEc c' ∧ ∀ i, R.Wc' i c = R.Wc' i c')
    (hex : ∃ p, R.EEp3 p ≠ ⊥) :
    0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0 := by
  obtain ⟨lam, κ, hκ, hl, hA, hB⟩ := hS
  have hlam : ∀ i t p c, R.Carries p c → R.Wc' i c ≠ ⊥ → R.lam3 i t p A3.A.v0 = lam i t c := by
    intro i t p c hc hne
    have hW := Wp3_eq hU hc i
    refine hC.scal.lam0 i t p _ (by rw [hW]; exact hne) fun x hx ↦ hA i t c x ?_
    rw [hW] at hx
    exact hx
  have hpos : ∀ i t p, 0 < R.lam3 i t p A3.A.v0 := by
    intro i t p
    by_cases hW : R.Wp3 i p = ⊥
    · rw [hC.scal.abs0 i t p hW]
      exact Real.exp_pos _
    · by_cases hc : ∃ c, R.Carries p c
      · obtain ⟨c, hc⟩ := hc
        rw [hlam i t p c hc (by rw [← Wp3_eq hU hc i]; exact hW)]
        exact hl i t c
      · exact absurd (Wp3_bot (not_exists.1 hc) i) hW
  refine ⟨?_, hpos⟩
  have hK : Lift.IsKap D.R.m (fun t ↦ R.Th t ∘ₗ LinearMap.adjoint (R.Th t)) R.EEp3 R.lamN κ := by
    intro t p x hx
    by_cases hc : ∃ c, R.Carries p c
    · obtain ⟨c, hc⟩ := hc
      have hx' : x ∈ R.EEc c := EEp3_eq hU hc ▸ hx
      have hpr : ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN t j p = ∏ j, lam j t c :=
        (RealDat3.prod_lamN t p).trans (Finset.prod_congr rfl fun j _ ↦ hlam j t p c hc (hM c hc.1 j))
      have h1 := hB t c x hx'
      calc (R.Th t ∘ₗ LinearMap.adjoint (R.Th t)) x = R.Th t (LinearMap.adjoint (R.Th t) x) := rfl
        _ = ((κ * ∏ i, lam i t c : ℝ) : ℂ) • x := h1
        _ = ((κ * ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN t j p : ℝ) : ℂ) • x := by rw [hpr]
    · have hb : R.EEp3 p = ⊥ := EEp3_bot (not_exists.1 hc)
      have hx0 : x = 0 := (Submodule.mem_bot ℂ).1 (hb ▸ hx)
      subst hx0
      rw [map_zero, smul_zero]
  obtain ⟨p, hp⟩ := hex
  rw [hC.scal.kap κ hK ⟨A3.A.μ0, p, hp, ?_⟩]
  · exact hκ
  · rw [RealDat3.prod_lamN]
    exact (Finset.prod_pos fun j _ ↦ hpos j _ p).ne'

end GlobalTheory.PosAtBase
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar




namespace GlobalTheory.SplitFrameColumn

theorem intAE_mul {D : D7} {x y : Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (hy : y ∈ intAE D) :
    x * y ∈ intAE D := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, c, rfl⟩ := hx
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨b, hb, d, rfl⟩ := hy
      refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, c * d, ?_⟩
      · rw [map_mul]; exact mul_mem (ha w) (hb w)
      · rw [Algebra.TensorProduct.tmul_mul_tmul]; push_cast; rfl
    | zero => rw [mul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | neg y _ hy => rw [mul_neg]; exact neg_mem hy
  | zero => rw [zero_mul]; exact zero_mem _
  | add x z _ _ hx hz => rw [add_mul]; exact add_mem hx hz
  | neg x _ hx => rw [neg_mul]; exact neg_mem hx

theorem comm_mem_intAf_iff {D : D7} (z : Af D.host.F ⊗[D.host.F] D.host.E) :
    Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔
      z ∈ intAE D := by
  constructor
  · intro hs
    have hs' : Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E z ∈
        Subring.closure (Set.range (fun x : Formalism.UG.intOE D.host.E => (x : D.host.E) ⊗ₜ[D.host.F] (1 : Af D.host.F)) ∪
        Set.range (fun y : Formalism.UG.intAd D.host.F => (1 : D.host.E) ⊗ₜ[D.host.F] (y : Af D.host.F))) := hs
    suffices h : ∀ s ∈ Subring.closure (Set.range (fun x : Formalism.UG.intOE D.host.E => (x : D.host.E) ⊗ₜ[D.host.F] (1 : Af D.host.F)) ∪
        Set.range (fun y : Formalism.UG.intAd D.host.F => (1 : D.host.E) ⊗ₜ[D.host.F] (y : Af D.host.F))),
        (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).symm s ∈ intAE D by
      simpa using h _ hs'
    have hone : (1 : Af D.host.F) ∈ intAf D.host.F := fun v => by rw [map_one]; exact one_mem _
    intro s hs
    induction hs using Subring.closure_induction with
    | mem s hs =>
      rcases hs with ⟨⟨_, c, rfl⟩, rfl⟩ | ⟨⟨a, ha⟩, rfl⟩
      · exact AddSubgroup.subset_closure ⟨1, hone, c, rfl⟩
      · refine AddSubgroup.subset_closure ⟨a, fun w => ha w, 1, ?_⟩
        simp
    | zero => rw [map_zero]; exact zero_mem _
    | one => rw [map_one]; exact AddSubgroup.subset_closure ⟨1, hone, 1, by simp [Algebra.TensorProduct.one_def]⟩
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | neg x _ hx => rw [map_neg]; exact neg_mem hx
    | mul x y _ _ hx hy => rw [map_mul]; exact intAE_mul hx hy
  · intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, rfl⟩ := hy
      rw [Algebra.TensorProduct.comm_tmul]
      have hx : (x : D.host.E) ⊗ₜ[D.host.F] a =
          ((x : D.host.E) ⊗ₜ[D.host.F] (1 : Af D.host.F)) * ((1 : D.host.E) ⊗ₜ[D.host.F] a) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [hx]
      exact mul_mem (Subring.subset_closure (Or.inl ⟨⟨(x : D.host.E), ⟨x, rfl⟩⟩, rfl⟩))
        (Subring.subset_closure (Or.inr ⟨⟨a, fun v => ha v⟩, rfl⟩))
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | neg x _ hx => rw [map_neg]; exact neg_mem hx

theorem toEAf_finEmb {D : D7} (t : EAf D) : toEAf D (GlobalTheory.AdelicLatMove.finEmb D t) = t := by
  induction t using TensorProduct.inductionOn with
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
  | tmul x α => rfl

theorem latHat_iff_hatL {D : D7} {n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (z : Fin n → Af D.host.F ⊗[D.host.F] D.host.E) :
    z ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (Λ : Set (Fin n → D.host.E)) ↔
      (fun i => Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E (z i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
  constructor
  · intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hz
      exact GlobalTheory.AdelicLatMove.pure_mem_hatL Λ a (fun w => ha w) x hx
    | zero => simp only [Pi.zero_apply, map_zero]; exact zero_mem _
    | add x y _ _ hx hy => simp only [Pi.add_apply, map_add (f := _)]; exact add_mem hx hy
    | neg x _ hx => simp only [Pi.neg_apply, map_neg]; exact neg_mem hx
  · intro hz
    have key : ∀ w ∈ AddSubgroup.closure (GlobalTheory.AdelicLatMove.pureSet (D := D) Λ),
        (fun i => (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).symm (w i)) ∈
          Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (Λ : Set (Fin n → D.host.E)) := by
      intro w hw
      induction hw using AddSubgroup.closure_induction with
      | mem w hw =>
        obtain ⟨α, hα, x, hx, rfl⟩ := hw
        exact AddSubgroup.subset_closure ⟨α, fun u => hα u, x, hx, rfl⟩
      | zero => simp only [Pi.zero_apply, map_zero]; exact zero_mem _
      | add x y _ _ hx hy => simp only [Pi.add_apply, map_add (f := _)]; exact add_mem hx hy
      | neg x _ hx => simp only [Pi.neg_apply, map_neg]; exact neg_mem hx
    have := key _ (GlobalTheory.AdelicLatMove.mem_closure_of_mem_hatL Λ _ hz)
    simpa only [AlgEquiv.symm_apply_apply] using this

theorem frame_column : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (β : GL (Fin V.rank) (EAf D)), IsSelfDualC V Λ → Formalism.L2.DIV.IsFrame β Λ → ∀ (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → ∀ y : Fin V.rank → AE D, (fun i => finPart D (e * y i)) ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (Λ : Set (Fin V.rank → D.host.E)) ↔ ∀ i, Valued.v ((((frCo φ β)⁻¹ : GL (Fin V.rank) (Fv D.host.F v)).1 *ᵥ fun k => rdA φ (y k)) i) ≤ 1 := by
  intro D V Λ β _ hβ v φ e he y
  obtain ⟨hπ, hE, -, -, -⟩ := GlobalTheory.SplitProjChart.chart_rdA D v φ e he
  set u : Fin V.rank → EAf D := (β⁻¹).1 *ᵥ fun k => toEAf D (y k) with hu
  have hsw : (fun k => Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E (finPart D (e * y k))) =
      toEAf D e • fun k => toEAf D (y k) := funext fun k => (toEAf D).map_mul e (y k)
  have hfe : ∀ t : EAf D, toEAf D (GlobalTheory.AdelicLatMove.finEmb D t) = t := toEAf_finEmb
  rw [latHat_iff_hatL, hβ, hsw, Matrix.mulVec_smul]
  refine forall_congr' fun i => ?_
  have h1 : (toEAf D e • u) i = toEAf D (e * GlobalTheory.AdelicLatMove.finEmb D (u i)) := by
    rw [map_mul, hfe]; rfl
  have h2 : rdA φ (GlobalTheory.AdelicLatMove.finEmb D (u i)) =
      ((((frCo φ β)⁻¹ : GL (Fin V.rank) (Fv D.host.F v)).1 *ᵥ fun k => rdA φ (y k)) i) := by
    rw [← hE, hfe, hu, RingHom.map_mulVec]
    unfold frCo
    rw [← map_inv]
    congr 1
    funext k
    exact hE (y k)
  rw [h1, show toEAf D (e * GlobalTheory.AdelicLatMove.finEmb D (u i)) =
      Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E (finPart D (e * GlobalTheory.AdelicLatMove.finEmb D (u i))) from rfl,
    comm_mem_intAf_iff, hπ.2.2.2, GlobalTheory.SplitHecke.isInt_Ov, HeightOneSpectrum.mem_adicCompletionIntegers, h2]

end GlobalTheory.SplitFrameColumn
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdSpan.ReVec

variable {D : D7} (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V)

theorem frPinv_mul_frP : frPinv S b * frP S b = 1 := by
  unfold frPinv frP; exact Module.Basis.toMatrix_mul_toMatrix_flip _ _

theorem frameMatrix_mul_frameMatrixInv : frP S b * frPinv S b = 1 := by
  unfold frPinv frP; exact Module.Basis.toMatrix_mul_toMatrix_flip _ _

def frPinvGL : GL (Fin S.rank) (Lev.EAf D) :=
  ⟨(frPinv S b).map (eToEAf D), (frP S b).map (eToEAf D),
    by rw [← Matrix.map_mul, frPinv_mul_frP]; exact Matrix.map_one _ (map_zero _) (map_one _),
    by rw [← Matrix.map_mul, frameMatrix_mul_frameMatrixInv]; exact Matrix.map_one _ (map_zero _) (map_one _)⟩

theorem frPinvGL_inv_val : (frPinvGL S b)⁻¹.val = (frP S b).map (eToEAf D) := rfl

def reWi (x : WO S T) : WO (reS S b) T :=
  HMul.hMul (α := Matrix (Fin T.rank) (Fin S.rank) (AE D)) x ((frP S b).map (incA D))

theorem mapA_frPinv_mul_frP : (frPinv S b).map (incA D) * (frP S b).map (incA D) = 1 := by
  rw [← Matrix.map_mul, frPinv_mul_frP]; exact Matrix.map_one _ (map_zero _) (map_one _)

theorem map_frP_mul_map_frPinv : (frP S b).map (incA D) * (frPinv S b).map (incA D) = 1 := by
  rw [← Matrix.map_mul, frameMatrix_mul_frameMatrixInv]; exact Matrix.map_one _ (map_zero _) (map_one _)

theorem reW_reWi (x : WO S T) : reW S T b (reWi S T b x) = x := by
  unfold reW reWi
  rw [Matrix.mul_assoc, map_frP_mul_map_frPinv, Matrix.mul_one]

theorem reWi_reW (x : WO (reS S b) T) : reWi S T b (reW S T b x) = x := by
  have h := Matrix.mul_assoc (show Matrix (Fin T.rank) (Fin S.rank) (AE D) from x) ((frPinv S b).map (incA D))
    ((frP S b).map (incA D))
  rw [mapA_frPinv_mul_frP, Matrix.mul_one] at h
  exact h

theorem reW_add (x y : WO (reS S b) T) : reW S T b (x + y) = reW S T b x + reW S T b y :=
  Matrix.add_mul _ _ _

def reWHom : WO (reS S b) T →+ WO S T := AddMonoidHom.mk' (reW S T b) (reW_add S T b)

theorem reW_nsmul (k : ℕ) (x : WO (reS S b) T) : reW S T b (k • x) = k • reW S T b x :=
  map_nsmul (reWHom S T b) k x

theorem reW_bijective : Function.Bijective (reW S T b) :=
  Function.bijective_iff_has_inverse.2 ⟨reWi S T b, reWi_reW S T b, reW_reWi S T b⟩

theorem isHalf_reW_iff (e : AE D) (x : WO (reS S b) T) : IsHalf e (reW S T b x) ↔ IsHalf e x := by
  have key : ∀ (M : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (N : Matrix (Fin S.rank) (Fin S.rank) (AE D)),
      IsHalf e M → IsHalf e (HMul.hMul (α := Matrix (Fin T.rank) (Fin S.rank) (AE D)) M N) := by
    intro M N h i j
    simp only [Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← mul_assoc, h i l]
  constructor
  · intro h
    have h2 := key _ ((frP S b).map (incA D)) h
    have : HMul.hMul (α := Matrix (Fin T.rank) (Fin S.rank) (AE D)) (reW S T b x) ((frP S b).map (incA D)) = x :=
      reWi_reW S T b x
    rwa [this] at h2
  · intro h
    exact key x _ h

theorem heisO_reF (ψ : AddChar (AF D.host.F) ℂ)
    (hs : ∀ x y, symplO (reS S b) T x y = symplO S T (reW S T b x) (reW S T b y))
    (u : WO (reS S b) T) (f : WO S T → ℂ) :
    heisO ψ (reS S b) T u (reF S T b f) = reF S T b (heisO ψ S T (reW S T b u) f) := by
  funext w
  simp only [heisO, reF_apply, symplOH, hs, reW_add]

end GlobalTheory.AdSpan.ReVec

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField


theorem _root_.GlobalTheory.T.conjPrime_smul_lattice_heckeElement_le : ∀ (D : D7) (V : HSp D) (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D) (ϖ : 𝓞 D.host.E) (k : ℕ) (g a₀ : GA D V),
    Formalism.L2.NTheta.IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 →
    Formalism.L2.NTheta.IsHeckeElt V e (ϖ : D.host.E) k a₀ →
    (Formalism.L2.Col.conjPrime₂ P).asIdeal • latG V (g * a₀) ≤ latG V g := by
  first | exact @GlobalTheory.HeckeConjPart.conj_part | exact GlobalTheory.HeckeConjPart.conj_part | (intros; apply GlobalTheory.HeckeConjPart.conj_part <;> assumption)
end
end
