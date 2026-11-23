module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveLatticeTwistGenerated
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle790
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle214
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle098
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedModelFibre
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle107
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle091
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle183
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2827
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle134
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle042
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle120
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3110
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
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2826
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3104
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open Classical

theorem GlobalTheory.GSep.exists_zhAbove : ∀ (X₁ : GlobalTheory.GSep.GSet), ∃ (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z),
    GlobalTheory.GSep.ZHAbove X₁ Y πY := by
  intro X₁
  obtain ⟨m, c, hc⟩ := RatModel.exists_isCl_of_isProjOver X₁.projM
  have hc0 : ∃ j, c j ≠ 0 := by
    obtain ⟨j, hj⟩ := hc.1 (genericPoint X₁.M.Z)
    exact ⟨j, hj.1⟩
  obtain ⟨Y, U₀, EE, hO, hdiv, hE, ⟨G⟩⟩ := GlobalTheory.zhSt_holds X₁.o₁ X₁.Ω₁ X₁.S X₁.ρ X₁.big (Fin (m + 1)) c hc0
    (GlobalTheory.ZH.finite_closure_theta_ratios_of_isCl X₁.o₁ X₁.Ω₁ X₁.S X₁.M (Fin (m + 1)) c hc)
  obtain ⟨q, hq⟩ := hc.exists_isHom (M' := Y) (φ := AlgHom.id X₁.o₁ X₁.Ω₁) hdiv
  have hYp : IsProper Y.s := ((GlobalTheory.isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hO.proj).1
  have hsep : IsSeparated X₁.M.s := X₁.M.sep
  have hqp : IsProper q := by
    haveI : IsProper (q ≫ X₁.M.s) := by rw [hq.inducedModelMorphism_comp_structureMap]; exact hYp
    exact IsProper.of_comp q X₁.M.s
  exact ⟨Y, q, U₀, EE, ⟨G⟩, hO, hE, hq, hqp⟩
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.GSep

theorem exists_points_frames_theta : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ), ∃ (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)) (th : SecA 𝔪.A (FractionRing V) 1) (ρ : LB.Gen (𝔪.A.L.pull (eSec 𝔪.A.A))), (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) ∧ (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' → Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' = val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) ∧ (∀ a, ValAt th (x a) (fr a) (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩)) ∧ ρ.IsGen ∧ ∀ a, IsTorsFrame 𝔪.A ρ (X₁.S.r * X₁.S.N) (x a) (fr a) := by
  intro I X₁ z₁ act V _ _ _ ev X _ t δ 𝔪
  have hj : (TFK (R := V) (FractionRing V)).hom = 𝟙 _ := by
    show Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V) (FractionRing V))) = _
    rw [Algebra.algebraMap_self]
    exact Spec.map_id _
  have gp := 𝔪.cart
  have hsq : ∀ a, (spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) ≫ X₁.ρ.P.A.hom = (TFK (R := V) (FractionRing V)).hom ≫ spMap 𝔪.yK := by
    intro a
    rw [Category.assoc, Over.w (X₁.ρ.pt a), hj]
    simp
  let x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A) := fun a =>
    Over.homMk (gp.1.lift _ _ (hsq a)) (gp.1.lift_snd _ _ _)
  have hx : ∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left := fun a => gp.1.lift_fst _ _ _
  obtain ⟨rig, fr, hrig, -, hfr⟩ := GlobalTheory.exists_frames_move_through (T := baseOver (Sp X₁.S.R))
    (T' := TFK (R := V) (FractionRing V)) (h := spMap 𝔪.yK) gp 𝔪.wl_gen X₁.ρ.rig_gen hx X₁.ρ.fr_tors
  have hτ : (spMap 𝔪.yK : (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left) ≫
      (baseOver (Sp X₁.S.R)).hom = (TFK (R := V) (FractionRing V)).hom ≫ spMap 𝔪.yK := by
    rw [hj]; simp
  obtain ⟨th, hth⟩ := GlobalTheory.ThetaPtMove.exists_secRel (T := TFK (R := V) (FractionRing V))
    (T₀ := baseOver (Sp X₁.S.R)) (τ := spMap 𝔪.yK) gp hτ (w := 𝔪.wl) 𝔪.wl_gen X₁.ρ.P.isLB 𝔪.A.isLB (a := 1) X₁.ρ.th₁
  refine ⟨x, fr, th, rig, hx, fun a => ⟨(hfr a).1.2.1, fun z J J' hJ hJ' => ?_⟩, fun a => ?_, hrig, fun a => (hfr a).1⟩
  · have e := (hfr a).2 _ (𝟙 _) z J J' hJ hJ'
    rw [Fin.prod_univ_one, zpow_one, Category.id_comp, Category.id_comp] at e
    exact e.symm
  · have hv := GlobalTheory.ThetaPtMove.isValueAt_move (T := TFK (R := V) (FractionRing V))
      (T₀ := baseOver (Sp X₁.S.R)) (τ := spMap 𝔪.yK) gp hτ (w := 𝔪.wl) X₁.ρ.P.isLB 𝔪.A.isLB (a := 1)
      (x := x a) (x₀ := X₁.ρ.pt a) (hx a).symm (ρ₀ := X₁.ρ.fr a) (ρ := fr a) (hfr a).2 (s₀ := X₁.ρ.th₁) (s := th) hth
      (X₁.ρ.th_val a)
    intro z J hJ
    have e := GlobalTheory.FrameMove.sval_valueAt hv (𝟙 _) hJ
    rw [Category.id_comp] at e
    refine e.trans ?_
    rw [GlobalTheory.FrameMove.val_powFrame, Nat.cast_one, zpow_one]
    congr 1
    exact (gs_pull (𝟙 _) (spMap 𝔪.yK) z ⊤ trivial _).trans
      ((congrArg (fun q => gs q z ⊤ _) (Category.id_comp _)).trans (GlobalTheory.FrameMove.gs_spMap 𝔪.yK z _))

end GlobalTheory.GSep
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep.BaseTerms

noncomputable section

namespace GlobalTheory.GSep

theorem exists_points_frames : ∀ {I : Type} (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V]
    [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X)
    (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ), ∃ (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)),
    (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) ∧
      (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' →
        Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' =
          val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) := by
  intro I X₁ z₁ act V _ _ _ ev X _ t δ 𝔪
  have hj : (TFK (R := V) (FractionRing V)).hom = 𝟙 _ := by
    show Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V) (FractionRing V))) = _
    rw [Algebra.algebraMap_self]
    exact Spec.map_id _
  have gp := 𝔪.cart
  have hsq : ∀ a, (spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) ≫ X₁.ρ.P.A.hom = (TFK (R := V) (FractionRing V)).hom ≫ spMap 𝔪.yK := by
    intro a
    rw [Category.assoc, Over.w (X₁.ρ.pt a), hj]
    simp
  let x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A) := fun a =>
    Over.homMk (gp.1.lift _ _ (hsq a)) (gp.1.lift_snd _ _ _)
  have hx : ∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left := fun a => gp.1.lift_fst _ _ _
  obtain ⟨rig, fr, hrig, -, hfr⟩ := GlobalTheory.exists_frames_move_through (T := baseOver (Sp X₁.S.R))
    (T' := TFK (R := V) (FractionRing V)) (h := spMap 𝔪.yK) gp 𝔪.wl_gen X₁.ρ.rig_gen hx X₁.ρ.fr_tors
  refine ⟨x, fr, hx, fun a => ⟨(hfr a).1.2.1, fun z J J' hJ hJ' => ?_⟩⟩
  have e := (hfr a).2 _ (𝟙 _) z J J' hJ hJ'
  rw [Fin.prod_univ_one, zpow_one, Category.id_comp, Category.id_comp] at e
  exact e.symm

end GlobalTheory.GSep
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep
noncomputable section

namespace GlobalTheory.USepGen

theorem genfib_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ (X₁ : GlobalTheory.GSep.GSet) (act : 𝓞 E → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (u : Sp (ratHull X₁.S.R) ⟶ Xo.XF c) (π : X₁.M.Z ⟶ C.Z), GlobalTheory.GSep.ULink C X₁ act u π → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t) (yK : X₁.S.R →+* FractionRing V) (x' : Sp (FractionRing V) ⟶ Sp (ratHull X₁.S.R)), x' ≫ spMap (toRat X₁.S.R) = spMap yK → GenOf Xo c (x' ≫ u) t → ∃ φ : P.A.A.left ⟶ X₁.ρ.P.A.left, IsGrpPullback P.A.A X₁.ρ.P.A (spMap yK) φ ∧ LBIso P.A.L (X₁.ρ.P.L.pull φ) ∧ ∀ a, (letI := H.starRing; (P.oA.act (H.bar a)).left) ≫ φ = φ ≫ (act a).left := by
  intro E _ _ _ H Dw _ l Xo c C X₁ act u π hL V _ _ _ _ t P yK x' hx' hgen
  obtain ⟨-, ⟨G, iG, α, β, hα, hβ, hLab, hf⟩, -, -⟩ := hL
  obtain ⟨tK, ⟨m₁⟩, ⟨m₂⟩⟩ := hgen
  have := P.U.gen_hom
  have : IsMonHom P.U.gen.symm.hom := by show IsMonHom P.U.gen.inv; infer_instance
  have gpA : IsGrpPullback P.A.A t.G (jK V) (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK V)) :=
    ((isGrpPullback_of_iso P.U.gen.symm).comp (isGrpPullback_pullback t.G (jK V))).congr
      (Category.id_comp _) rfl
  have w₁ : (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK V)) ≫ t.G.hom = (P.A.A.hom ≫ 𝟙 _) ≫ jK V := by
    rw [gpA.1.w, Category.comp_id]
  let κ : P.A.A.left ⟶ tK.G.left := m₁.cart.1.lift _ _ w₁
  have hκ₁ : κ ≫ m₁.φ = P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK V) := m₁.cart.1.lift_fst _ _ _
  have hκ₂ : κ ≫ tK.G.hom = P.A.A.hom ≫ 𝟙 _ := m₁.cart.1.lift_snd _ _ _
  have gκ : IsGrpPullback P.A.A tK.G (𝟙 _) κ :=
    m₁.cart.cancel (gpA.congr (Category.id_comp _).symm hκ₁.symm) hκ₂
  have w₂ : m₂.φ ≫ Xo.univ.t.G.hom = (tK.G.hom ≫ x') ≫ u ≫ pullback.fst _ _ := by
    rw [m₂.cart.1.w]; simp only [Category.assoc]
  let lam : tK.G.left ⟶ G.left := hβ.1.lift _ _ w₂
  have hl₁ : lam ≫ β = m₂.φ := hβ.1.lift_fst _ _ _
  have hl₂ : lam ≫ G.hom = tK.G.hom ≫ x' := hβ.1.lift_snd _ _ _
  have gl : IsGrpPullback tK.G G x' lam :=
    hβ.cancel (m₂.cart.congr (Category.assoc _ _ _) hl₁.symm) hl₂
  refine ⟨κ ≫ lam ≫ α, (gκ.comp (gl.comp hα)).congr (by rw [Category.id_comp, hx']) rfl, ?_, ?_⟩
  · have hA := P.A.isLB
    have hT := t.PP.isLB
    have hK := tK.PP.isLB
    have hU := Xo.univ.t.PP.isLB
    have hP := X₁.ρ.P.isLB
    obtain ⟨w, hw⟩ := P.U.ext
    have hc : P.U.gen.inv.left ≫ P.U.gen.hom.left = 𝟙 _ := by
      rw [← Over.comp_left, Iso.inv_hom_id]; rfl
    have e₁ : LBIso (P.A.L.pull (𝟙 _)) (P.U.LG.L.pull (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK V))) :=
      GlobalTheory.GenSpread.lbIso_pull_comp P.U.gen.inv.left hc.symm rfl ⟨w, hw⟩
    rw [P.bundle, ← hκ₁] at e₁
    have e₀ : LBIso P.A.L (P.A.L.pull (𝟙 _)) := GlobalTheory.SiegelPullComp.iso_pull_id hA
    obtain ⟨w₁, hw₁, -⟩ := m₁.lin
    obtain ⟨w₂, hw₂, -⟩ := m₂.lin
    have e₂ : LBIso (tK.PP.L.pull κ) (t.PP.L.pull (κ ≫ m₁.φ)) :=
      GlobalTheory.GenSpread.lbIso_pull_of_lbIso ⟨w₁, hw₁⟩ κ rfl
    have e₃ : LBIso (tK.PP.L.pull κ) (Xo.univ.t.PP.L.pull (κ ≫ m₂.φ)) :=
      GlobalTheory.GenSpread.lbIso_pull_of_lbIso ⟨w₂, hw₂⟩ κ rfl
    have e₄ : LBIso (X₁.ρ.P.L.pull (κ ≫ lam ≫ α)) (Xo.univ.t.PP.L.pull (κ ≫ m₂.φ)) :=
      GlobalTheory.GenSpread.lbIso_pull_comp (κ ≫ lam) (Category.assoc _ _ _).symm
        (by rw [← hl₁, Category.assoc]) hLab
    refine LBIso.trans hA (pull_isLB hA _) (pull_isLB hP _) e₀ ?_
    refine LBIso.trans (pull_isLB hA _) (pull_isLB hT _) (pull_isLB hP _) e₁ ?_
    refine LBIso.trans (pull_isLB hT _) (pull_isLB hK _) (pull_isLB hP _) e₂.symm ?_
    refine LBIso.trans (pull_isLB hK _) (pull_isLB hU _) (pull_isLB hP _) e₃ ?_
    exact e₄.symm
  · intro a
    obtain ⟨f, hfα, hfβ⟩ := hf a
    letI := H.starRing
    have hext := P.lin.ext (H.bar a)
    have hg : (P.oA.act (H.bar a)).left ≫ P.U.gen.inv.left =
        P.U.gen.inv.left ≫ ((Over.pullback (jK V)).map (t.act.act (H.bar a))).left := by
      have : P.oA.act (H.bar a) ≫ P.U.gen.inv =
          P.U.gen.inv ≫ (Over.pullback (jK V)).map (t.act.act (H.bar a)) := by
        rw [Iso.eq_inv_comp, ← Category.assoc, ← hext, Category.assoc, Iso.hom_inv_id, Category.comp_id]; rfl
      rw [← Over.comp_left, this, Over.comp_left]
    have s₁ : (P.oA.act (H.bar a)).left ≫ κ = κ ≫ (tK.act.act (H.bar a)).left := by
      apply m₁.cart.1.hom_ext
      · rw [Category.assoc, hκ₁, Category.assoc, m₁.act, ← Category.assoc κ, hκ₁, ← Category.assoc, hg,
          Category.assoc, Category.assoc]
        congr 1
        exact pullback.lift_fst _ _ _
      · rw [Category.assoc, hκ₂, Category.assoc, Over.w, hκ₂, ← Category.assoc, Over.w]
    have s₂ : (tK.act.act (H.bar a)).left ≫ lam = lam ≫ f.left := by
      apply hβ.1.hom_ext
      · simp only [Category.assoc, hfβ]
        rw [hl₁, ← Category.assoc lam β, hl₁]
        exact m₂.act _
      · rw [Category.assoc, hl₂, ← Category.assoc, Over.w, Category.assoc, Over.w, hl₂]
    rw [← Category.assoc, s₁, Category.assoc, ← Category.assoc _ lam, s₂, Category.assoc, hfα]
    simp only [Category.assoc]

end GlobalTheory.USepGen
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

namespace GlobalTheory.GSep.SupISymm

theorem exists_unit_of_pow_eq_one {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω)
    {c ε : Ω} (hc : c ^ 2 = 1) (hε : ε ^ ((S.r * S.N) ^ 2) = 1) : ∃ u : oˣ, c * ε = algebraMap o Ω (u : o) := by
  have hinj : Function.Injective (algebraMap o Ω) := ArithBase.inj
  have hp : IsPrimitiveRoot (algebraMap o Ω S.ζ) ((S.r * S.N) ^ 2) := S.prim.map_of_injective hinj
  have hpos : 0 < (S.r * S.N) ^ 2 := by
    have := S.N_ge; have := S.r_pos; positivity
  obtain ⟨k, -, hk⟩ := hp.eq_pow_of_pow_eq_one hε
  have hζu : IsUnit S.ζ := S.prim.isUnit hpos.ne'
  have hc' : c = 1 ∨ c = -1 := by
    have : c * c = 1 := by rw [← sq]; exact hc
    exact mul_self_eq_one_iff.1 this
  rcases hc' with rfl | rfl
  · exact ⟨(hζu.unit) ^ k, by simp [← hk, map_pow]⟩
  · exact ⟨-(hζu.unit) ^ k, by simp [← hk, map_pow]⟩

theorem exists_unit_th_neg {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω)
    (H : ∀ a : S.Gam, ∃ c ε : Ω, c ^ 2 = 1 ∧ ε ^ ((S.r * S.N) ^ 2) = 1 ∧ S.th (-a) = c * ε * S.th a) (a : S.Gam) :
    ∃ u : oˣ, S.th (-a) = algebraMap o Ω (u : o) * S.th a := by
  obtain ⟨c, ε, hc, hε, h⟩ := H a
  obtain ⟨u, hu⟩ := exists_unit_of_pow_eq_one S hc hε
  exact ⟨u, by rw [h, hu]⟩

theorem neg_mem_supI_of_parity {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω)
    (M : RatModel o Ω)
    (H : ∀ a : S.Gam, ∃ c ε : Ω, c ^ 2 = 1 ∧ ε ^ ((S.r * S.N) ^ 2) = 1 ∧ S.th (-a) = c * ε * S.th a)
    (z : M.Z) (a : S.Gam) (ha : a ∈ S.supI M z) : -a ∈ S.supI M z := by
  obtain ⟨hne, hdiv⟩ := ha
  obtain ⟨u, hu⟩ := exists_unit_th_neg S H a
  have hu0 : algebraMap o Ω (u : o) ≠ 0 := by
    intro h0
    have h1 : algebraMap o Ω ((u : o) * ((u⁻¹ : oˣ) : o)) = 1 := by simp
    rw [map_mul, h0, zero_mul] at h1
    exact zero_ne_one h1
  refine ⟨by rw [hu]; exact mul_ne_zero hu0 hne, fun j => ?_⟩
  obtain ⟨v, hv⟩ := exists_unit_th_neg S H (-j)
  rw [neg_neg] at hv
  have key : S.th j / S.th (-a) = algebraMap o Ω ((v : o) * ((u⁻¹ : oˣ) : o)) * (S.th (-j) / S.th a) := by
    have hi : algebraMap o Ω ((u⁻¹ : oˣ) : o) = (algebraMap o Ω (u : o))⁻¹ := by
      exact eq_inv_of_mul_eq_one_left (by rw [← map_mul]; simp)
    rw [hv, hu, map_mul, hi]
    field_simp
  rw [key]
  exact (M.O z).mul_mem (Subalgebra.algebraMap_mem _ _) (hdiv (-j))

end GlobalTheory.GSep.SupISymm


open GlobalTheory.GSep.SupISymm in
theorem GlobalTheory.GSep.neg_mem_supI : ∀ (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (a : X₁.S.Gam), a ∈ X₁.S.supI X₁.M z₁ → -a ∈ X₁.S.supI X₁.M z₁ := by
  intro X₁ z₁ a ha
  exact neg_mem_supI_of_parity X₁.S X₁.M (fun a => GlobalTheory.ThetaParity.theta_neg X₁.o₁ X₁.Ω₁ X₁.S X₁.ρ a) z₁ a ha
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep

noncomputable section

namespace GlobalTheory.GSep

theorem valPt_lies_over_unitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ (X₁ : GlobalTheory.GSep.GSet) (act : 𝓞 E → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (u : Sp (ratHull X₁.S.R) ⟶ Xo.XF c) (π : X₁.M.Z ⟶ C.Z), GlobalTheory.GSep.ULink C X₁ act u π → ∀ (z₁ : X₁.M.Z) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V₁) (y : Sp (FractionRing V₁) ⟶ Xo.XF c), GlobalTheory.GSep.RegAt X₁ z₁ ev → jK V₁ ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ ≫ π = y ≫ C.i → ∃ (yK : X₁.S.R →+* FractionRing V₁) (x' : Sp (FractionRing V₁) ⟶ Sp (ratHull X₁.S.R)), (∀ a, yK a = X₁.M.val (jK V₁ ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) a) ∧ x' ≫ spMap (toRat X₁.S.R) = spMap yK ∧ x' ≫ u = y := by
  intro E _ _ _ H Dw _ l Xo c C X₁ act u π hL z₁ V₁ _ _ _ ev y hreg hy
  set yw := jK V₁ ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ with hyw
  set w := yw (IsLocalRing.closedPoint (FractionRing V₁)) with hw
  have hle : X₁.S.R ≤ X₁.M.O w := fun a ha => hreg a ha

  have hπw : π w = C.i (y (IsLocalRing.closedPoint (FractionRing V₁))) := by
    have h1 : yw ≫ π = y ≫ C.i := by simpa only [hyw, Category.assoc] using hy
    have h2 := congrArg (fun f => f (IsLocalRing.closedPoint (FractionRing V₁))) h1
    exact h2
  have hc : ∀ n : ℤ, n ≠ 0 → IsUnit (n : X₁.M.O w) := fun n hn => by
    rw [← map_intCast (X₁.M.stalkEquiv w) n, MulEquiv.isUnit_map, ← map_intCast (π.stalkMap w).hom n,
      isUnit_map_iff, hπw, ← isUnit_map_iff (C.i.stalkMap _).hom, map_intCast]
    have h : IsUnit (n : c.F) := IsUnit.mk0 _ (Int.cast_ne_zero.2 hn)
    have h' := ((h.map (Scheme.ΓSpecIso (CommRingCat.of c.F)).inv.hom).map
      ((Sp c.F).presheaf.germ ⊤ ((pullback.snd _ _ : Xo.XF c ⟶ Sp c.F) (y (IsLocalRing.closedPoint (FractionRing V₁))))
        trivial).hom).map ((pullback.snd _ _ : Xo.XF c ⟶ Sp c.F).stalkMap _).hom
    rwa [map_intCast, map_intCast, map_intCast] at h'
  have hle' : ratHull X₁.S.R ≤ X₁.M.O w := fun x hx => by
    obtain ⟨n, hn, h⟩ := mem_ratHull.1 hx
    obtain ⟨h1, h2⟩ := (RatModel.isUnit_O_iff _).1 (hc n hn)
    have e : ((n : X₁.M.O w) : X₁.Ω₁) = n := by simp
    rw [e] at h1 h2
    have := mul_mem h2 (hle h)
    rwa [inv_mul_cancel_left₀ h1] at this
  have hsp : yw (IsLocalRing.closedPoint (FractionRing V₁)) ⤳ w := specializes_rfl
  let ψ : ratHull X₁.S.R →+* X₁.M.Z.presheaf.stalk w :=
    (X₁.M.stalkEquiv w).symm.toRingHom.comp (Subalgebra.inclusion hle').toRingHom
  let φ : X₁.M.Z.presheaf.stalk w →+* FractionRing V₁ := (X₁.M.Z.presheaf.stalkSpecializes hsp ≫
    Scheme.stalkClosedPointTo (R := CommRingCat.of (FractionRing V₁)) yw).hom
  have hK : (RatModel.valHom yw w (RatModel.range_eq_singleton yw _)).comp (Subalgebra.inclusion hle).toRingHom =
      (φ.comp ψ).comp (toRat X₁.S.R) :=
    RingHom.ext fun a => (RatModel.valLoc_eq_val yw hsp (Subalgebra.inclusion hle a)).symm
  refine ⟨(RatModel.valHom yw w (RatModel.range_eq_singleton yw _)).comp (Subalgebra.inclusion hle).toRingHom,
    spMap (φ.comp ψ), fun a => rfl, ?_, ?_⟩
  · rw [hK]
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  haveI := C.isPreimmersion_i
  haveI : IsProper C.z := GlobalTheory.ThetaDescent.isProper_of_isProjOver C.proj
  haveI : C.Z.IsSeparated := by
    constructor
    rw [← terminal.comp_from C.z]
    infer_instance
  haveI : IsDominant (spMap (X₁.M.stalkHom w)) := by
    refine ⟨?_⟩
    change DenseRange (PrimeSpectrum.comap (X₁.M.stalkHom w))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot _).1 (X₁.M.stalkHom_injective w)]
    exact bot_le
  have hfs : ∀ {B : Type} [CommRing B] [IsLocalRing B] (q : Sp B ⟶ X₁.M.Z) (h : q (IsLocalRing.closedPoint B) ⤳ w),
      spMap (X₁.M.Z.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo (R := CommRingCat.of B) q).hom ≫
        X₁.M.Z.fromSpecStalk w = q := by
    intro B _ _ q h
    simp only [spMap, CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of B) q
  have e1 : spMap (X₁.M.stalkHom w) ≫ spMap ψ = spMap (ratHull X₁.S.R).val.toRingHom := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun a => congrArg Subtype.val ((X₁.M.stalkEquiv w).apply_symm_apply (Subalgebra.inclusion hle' a))
  have e2 : spMap (X₁.M.stalkHom w) ≫ X₁.M.Z.fromSpecStalk w = X₁.M.pt :=
    hfs X₁.M.pt (X₁.M.pt_specializes _ w)
  have hab : spMap ψ ≫ u ≫ C.i = X₁.M.Z.fromSpecStalk w ≫ π := by
    refine ext_of_isDominant (spMap (X₁.M.stalkHom w)) ?_
    rw [reassoc_of% e1, reassoc_of% e2, hL.2.2.2]
  have e3 : spMap φ ≫ X₁.M.Z.fromSpecStalk w = yw := hfs yw hsp
  rw [← cancel_mono C.i, Category.assoc]
  rw [show spMap (φ.comp ψ) = spMap φ ≫ spMap ψ by
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp], Category.assoc, hab, reassoc_of% e3, ← hy]
  simp only [hyw, Category.assoc]

end GlobalTheory.GSep
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

namespace GlobalTheory.GSep.GMem

theorem exists_yy : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (mu : X), ∃ a : X₁.S.Gam, 𝔪.YY a mu := by
  intro I X₁ z₁ act V _ _ _ ev X _ t δ 𝔪 mu
  haveI : CharZero V := 𝔪.cn.2.2.2
  have hA : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  have hk : 1 ≤ X₁.S.r * X₁.S.N := by
    obtain ⟨j, -, hj⟩ := X₁.ρ.r_eq
    have hn := X₁.ρ.n_prime.pos
    rw [hj, X₁.ρ.N_eq]
    exact Nat.one_le_iff_ne_zero.2 (by positivity)
  obtain ⟨h, hh⟩ := GlobalTheory.TorusExt.exists_iota (F := AlgebraicClosure (FractionRing V)) 𝔪.D.tau_bimult (𝔪.e₈ mu)
  obtain ⟨g', hg'⟩ := (GlobalTheory.UT.gt_onto_divisible_kernel GlobalTheory.firstFiveLaws V (maximalIdeal V) hA 𝔪.D
    (AlgebraicClosure (FractionRing V))).2.1 _ hk h
  let p : QkPt 𝔪.D.toPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) := ⟨𝔪.e₈ mu, g', h, hg', hh⟩
  obtain ⟨f, hf, -⟩ := GlobalTheory.TorsionIso.torsion_eq GlobalTheory.firstFiveLaws V (maximalIdeal V) hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U
    (AlgebraicClosure (FractionRing V)) _ hk
  have hx := (hf p (f p)).2 rfl
  obtain ⟨w, hw⟩ := 𝔪.U.ext
  have hpow : f p ^ (X₁.S.r * X₁.S.N) = 1 := (hx w hw).1
  let z := pushHom 𝔪.cart (TFK (R := V) (AlgebraicClosure (FractionRing V))) (f p)
  have hz : z ^ (X₁.S.r * X₁.S.N) = 1 := by
    simp only [z]
    rw [← map_pow, hpow, map_one]
  obtain ⟨a, ha, -⟩ := X₁.ρ.pt_bij (AlgebraicClosure (FractionRing V)) _ z hz
  refine ⟨a, p, f p, rfl, hx, ?_⟩
  have e := congrArg (fun q => q.left) ha
  simp only [Over.comp_left, Over.homMk_left] at e
  have e2 : spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) =
      jFK (R := V) (AlgebraicClosure (FractionRing V)) ≫ spMap 𝔪.yK := by
    simp [spMap, jFK, ← Spec.map_comp]
  rw [e2]
  exact e.symm

end GlobalTheory.GSep.GMem
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.exists_thetaConstant_value_ne_zero : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), ∃ b, 𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩ ≠ 0 := by
  first | exact @GlobalTheory.Poinc.Sep.UMem.exists_th_ne_zero | exact GlobalTheory.Poinc.Sep.UMem.exists_th_ne_zero | (intros; apply GlobalTheory.Poinc.Sep.UMem.exists_th_ne_zero <;> assumption)
end
