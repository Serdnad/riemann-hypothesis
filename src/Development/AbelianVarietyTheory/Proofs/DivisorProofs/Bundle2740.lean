module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2655
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2659
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalSiegelOfGenericPrincipalSpecialAmple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle147
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2662
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocReg

theorem chart_appLE_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (U : Y.X.affineOpens) (k : Type) [Field k] (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ gen Y) (hx : ξ (closedPoint _) ∈ genι Y ⁻¹ᵁ U.1), ∃ hg : ⊤ ≤ (ξ ≫ genι Y) ⁻¹ᵁ U.1, ((ξ ≫ genι Y).appLE U.1 ⊤ hg).hom = (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom.comp (GlobalTheory.LocReg.chartHom Y U ξ hx) := by
  intro E _ _ _ H Dw l Xo c Y U k _ m d ξ hx
  have hx' : (ξ ≫ genι Y) (closedPoint (CommRingCat.of (ChartRing k m d))) ∈ U.1 := hx
  refine ⟨(Scheme.preimage_eq_top_of_closedPoint_mem (ξ ≫ genι Y) hx').ge, ?_⟩
  have key : (gen Y).presheaf.germ (genι Y ⁻¹ᵁ U.1) _ hx ≫ Scheme.stalkClosedPointTo ξ =
      ξ.appLE (genι Y ⁻¹ᵁ U.1) ⊤ (Scheme.preimage_eq_top_of_closedPoint_mem ξ hx).ge ≫
        (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom := by
    rw [Scheme.germ_stalkClosedPointTo]
    simp [Iso.trans_hom, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map_assoc]
  have e : (ξ ≫ genι Y).appLE U.1 ⊤ (Scheme.preimage_eq_top_of_closedPoint_mem (ξ ≫ genι Y) hx').ge =
      (genι Y).app U.1 ≫ (gen Y).presheaf.germ (genι Y ⁻¹ᵁ U.1) _ hx ≫ Scheme.stalkClosedPointTo ξ ≫
        (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv := by
    rw [reassoc_of% key, Iso.hom_inv_id, Category.comp_id, Scheme.Hom.comp_appLE]
  rw [e]
  rfl

end GlobalTheory.LocReg
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocReg

theorem exists_basicOpen_chartHom_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (U W : Y.X.affineOpens), W.1 = U.1 ⊓ interior Y → ∀ (k : Type) [Field k] (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ gen Y) (hx : ξ (closedPoint _) ∈ genι Y ⁻¹ᵁ U.1), (∀ p : Sp (ChartRing k m d), ξ p ∈ genBd Y ↔ ∏ i, bdParam k m d i ∈ p.asIdeal) → ∃ h : Γ(Y.X, U.1), Y.X.basicOpen h ≤ W.1 ∧ GlobalTheory.LocReg.chartHom Y U ξ hx h ≠ 0 := by
  intro E _ _ _ H Dw l Xo c Y U W hW k _ m d ξ hx hbd
  let gp : Sp (ChartRing k m d) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (ChartRing k m d))
  have hprod : (∏ i, bdParam k m d i) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ hX => by
      have := congrArg (MvPowerSeries.coeff (Finsupp.single (Sum.inl i) 1)) hX
      simp at this
  have hgbd : ξ gp ∉ genBd Y := by
    rw [hbd]
    exact fun h => hprod ((Submodule.mem_bot _).1 h)
  have hgab : genι Y (ξ gp) ∈ interior Y := by
    have := (mem_genBd_iff (Y := Y) (x := ξ gp)).not.1 hgbd
    rw [not_not, ← coe_interior] at this
    exact this
  have hsp : gp ⤳ closedPoint (ChartRing k m d) :=
    (PrimeSpectrum.le_iff_specializes _ _).1 (fun x hx => by
      rw [(Submodule.mem_bot _).1 hx]; exact Ideal.zero_mem _)
  have hgU : ξ gp ∈ genι Y ⁻¹ᵁ U.1 :=
    (hsp.map ξ.continuous).mem_open (genι Y ⁻¹ᵁ U.1).isOpen hx
  have hyW : genι Y (ξ gp) ∈ W.1 := by
    rw [hW]; exact ⟨hgU, hgab⟩
  obtain ⟨h, hle, hmem⟩ := U.2.exists_basicOpen_le (V := W.1) ⟨_, hyW⟩ hgU
  refine ⟨h, hle, fun h0 => ?_⟩
  have hg0 : gp ∈ ξ ⁻¹ᵁ (gen Y).basicOpen (((genι Y).app U.1).hom h) := by
    show ξ gp ∈ (gen Y).basicOpen _
    rw [← Scheme.preimage_basicOpen]; exact hmem
  rw [Scheme.preimage_basicOpen] at hg0
  have e := congrArg (fun q => q.hom (((genι Y).app U.1).hom h)) (Scheme.germ_stalkClosedPointTo ξ _ hx)
  simp only [chartHom, RingHom.comp_apply] at h0
  change (Scheme.stalkClosedPointTo ξ).hom (((gen Y).presheaf.germ _ _ hx).hom _) = 0 at h0
  rw [← CommRingCat.comp_apply] at h0
  rw [e] at h0
  have h1 := h0
  rw [CommRingCat.comp_apply] at h1
  have hz : (ξ.app (genι Y ⁻¹ᵁ U.1)).hom (((genι Y).app U.1).hom h) = 0 :=
    (ConcreteCategory.bijective_of_isIso _).1 (h1.trans (map_zero _).symm)
  rw [hz, Scheme.basicOpen_zero] at hg0
  exact hg0

end GlobalTheory.LocReg
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.LocReg

theorem comp_genι_eq_spMap_chartHom (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (U : Y.X.affineOpens) (k : Type) [Field k] (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ gen Y) (hx : ξ (closedPoint _) ∈ genι Y ⁻¹ᵁ U.1) :
    ξ ≫ genι Y = spMap (GlobalTheory.LocReg.chartHom Y U ξ hx) ≫ chart U := by
  have hx' : (ξ ≫ genι Y) (closedPoint (ChartRing k m d)) ∈ U.1 := hx
  have e1 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (ξ ≫ genι Y)
  have e2 : Y.X.fromSpecStalk ((ξ ≫ genι Y) (closedPoint (ChartRing k m d))) =
      Spec.map (Y.X.presheaf.germ U.1 _ hx') ≫ U.2.fromSpec :=
    (U.2.fromSpecStalk_eq_fromSpecStalk hx').symm
  rw [e2, ← Spec.map_comp_assoc, Scheme.stalkClosedPointTo_comp] at e1
  rw [← e1, chart]
  congr 2
  exact (Scheme.Hom.germ_stalkMap_assoc (genι Y) U.1 (ξ (closedPoint _)) hx (Scheme.stalkClosedPointTo ξ)).trans rfl

end GlobalTheory.LocReg
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings
open GlobalTheory.PrincSubring

noncomputable section
namespace GlobalTheory.EighthPowerBundle

open GlobalTheory.CechPic

def pre0 {S : Scheme.{0}} (h : ℕ) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (A ⊗ A).left)
    (hP : IsSymmetricPair h A P) : SiegPre 0 1 (0 : ℤ) (specZIsTerminal.from S) where
  A := A
  ab := hP.1
  P := P
  isLB := hP.2.2.1
  rig₁ := hP.2.2.2.1
  rig₂ := hP.2.2.2.2.1
  symm := hP.2.2.2.2.2
  lev := fun _ => 1
  lev_add := fun _ _ => (_root_.mul_one _).symm
  lev_tors := fun _ => one_pow _
  geom := fun k _ _ x β z _ hz => by
    rw [map_zero] at hz
    exact absurd hz z.ne_zero

theorem powLB_props : ∀ {S : Scheme.{0}} (h : ℕ) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (A ⊗ A).left),
    IsSymmetricPair h A P → Out.RelAmple A (diagPull A P) → IsAbelianScheme (Out.powObj A 8) ∧ (powLB A P).IsLB ∧
      Out.RelAmple (Out.powObj A 8) (powLB A P) ∧ Out.Rigidified (Out.powObj A 8) (powLB A P) ∧
      Out.Sym (Out.powObj A 8) (powLB A P) := by
  intro S h A _ _ P hP hA
  let c := pre0 h A P hP
  have hA' : Out.RelAmple c.A c.diag := hA
  obtain ⟨hpos, -⟩ := isE8_W8
  let pr : Fin 8 → (Out.powObj A 8 ⟶ A) := Out.powPr A
  have hmon : ∀ u, IsMonHom (pr u) := fun u => inferInstance
  have huniv : ∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ Out.powObj A 8, ∀ u, x ≫ pr u = y u := fun T y =>
    ⟨(Out.powIsLimit A 8).lift (Fan.mk T y), fun u => (Out.powIsLimit A 8).fac (Fan.mk T y) ⟨u⟩,
      fun x hx => (Out.powIsLimit A 8).uniq (Fan.mk T y) x fun u => hx u.as⟩
  have hL : (powLB A P).IsLB := LB.isLB_linComb hP.2.2.1 _ _
  have hLW : cls (powLB A P) hL = PrincipalIntegral.quad (cls c.P c.isLB) W8 pr := cls_linComb hP.2.2.1 _ _ _
  have hadd := PrincipalIntegral.pair_mul c SemiRigid.globalFns hA'
  exact ⟨AbelianSchemeGerms.isAbelianScheme_powObj A hP.1 7, hL,
    PosDefAmple.relAmple_linComb_of_posDef SemiRigid.globalFns 0 1 8 ℤ 0 S _ c (Out.powObj A 8) pr W8 hmon huniv hA'
      hpos,
    PrincipalIntegral.rigidified hadd hmon hL hLW,
    PrincipalIntegral.sym hadd (PrincipalIntegral.pair_comm c) hmon hL hLW⟩

end GlobalTheory.EighthPowerBundle
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings
open GlobalTheory.PrincSubring

noncomputable section

namespace GlobalTheory.PrincSubring

section Transport

variable {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]

theorem gm_self_of_pGen {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) {Z : Scheme.{0}} (f : Z ⟶ X')
    (z : Z) {k : L'.ι} (hk : f z ∈ L'.U k) : gm f z (L'.U k ⊓ L'.U k) (L'.g k k) = 1 := by
  obtain ⟨j, hj⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart hL (F (f z))
  have e := hw Z f z j j k k hj hj hk hk
  rw [gm_self hL (f ≫ F) z hj, _root_.one_mul] at e
  exact inv_eq_one.1 (mul_eq_right.1 e.symm)

theorem trF_self_of_pGen {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (φ' : K → (Y ⟶ X')) (ε : K → ℤ)
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {q : K → L'.ι} (hq : r z ∈ LB.wchart L' φ' q) :
    trF (L := L') φ' ε r z q q = 1 := by
  unfold trF
  refine Finset.prod_eq_one fun k _ => ?_
  rw [gm_self_of_pGen hw hL (r ≫ φ' k) z (Set.mem_iInter.1 hq k), one_zpow]

theorem exists_down_of_pGen {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) {φ' : K → (Y ⟶ X')} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε)) (ht : t.IsGen) : ∃ a : LB.Gen (LB.LinComb L' φ' ε), a.IsGen := by
  choose u hu using fun p q => exists_pw w φ' ε p q
  have glue : ∀ q : K → L'.ι, ∃ s : Γ(Y, LB.wchart L' φ' q)ˣ, ∀ (y : Y) p,
      y ∈ LB.wchart L (fun k => φ' k ≫ F) p → y ∈ LB.wchart L' φ' q →
      gm (𝟙 Y) y _ s = (pw w φ' ε (𝟙 Y) y p q)⁻¹ * gm (𝟙 Y) y (LB.wchart L (fun k => φ' k ≫ F) p) (t.s p) := by
    intro q
    have hv : ∀ (y : Y) p, y ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q →
        gm (𝟙 Y) y _ ((u p q)⁻¹ * res inf_le_left (t.s p)) =
          (pw w φ' ε (𝟙 Y) y p q)⁻¹ * gm (𝟙 Y) y (LB.wchart L (fun k => φ' k ≫ F) p) (t.s p) :=
      fun y p hz => (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_inv _ _).trans (congrArg (·⁻¹) (hu p q _ _ y hz)))
        (gm_res _ y _ hz _))
    obtain ⟨s, hs⟩ := glue_unit _ (fun p => LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q) (fun _ => inf_le_right)
      (fun y hy => by
        choose p hp using fun k => ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart hL (F (φ' k y))
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨p, Set.mem_iInter.2 hp, hy⟩) (fun p => (u p q)⁻¹ * res inf_le_left (t.s p))
      (fun p p' y hy => by
        rw [hv y p hy.1, hv y p' hy.2, pw_trans hw φ' ε (𝟙 Y) y hy.1.1 hy.2.1 hy.1.2 hy.1.2,
          trF_self_of_pGen hw hL _ ε (𝟙 Y) y hy.1.2, gen_trans ht (𝟙 Y) y hy.1.1 hy.2.1, inv_one, _root_.mul_one, mul_inv,
          _root_.mul_mul_mul_comm, inv_mul_cancel, _root_.one_mul])
    refine ⟨s, fun y p h₁ h₂ => ?_⟩
    have hz : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q := ⟨h₁, h₂⟩
    exact (gm_res _ y inf_le_right hz s).symm.trans ((congrArg (gm _ y _) (hs p)).trans (hv y p hz))
  choose s hs using glue
  refine ⟨⟨s⟩, isGen_of_gm _ fun y j j' hj hj' => ?_⟩
  choose p hp using fun k => ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart hL (F (φ' k y))
  have m : y ∈ LB.wchart L (fun k => φ' k ≫ F) p := Set.mem_iInter.2 hp
  refine (hs j y p m hj).trans (Eq.trans ?_ (congrArg _ (hs j' y p m hj')).symm)
  rw [pw_trans hw φ' ε (𝟙 Y) y m m hj hj', trF_self hL _ ε (𝟙 Y) y m, _root_.one_mul, mul_inv, inv_inv, _root_.mul_assoc]

end Transport

theorem kerAlong_of_pull : ∀ {S S' : Scheme.{0}} (f : S' ⟶ S) (A : Over S') [GrpObj A] (P : LB (A ⊗ A).left) (A₁ : Over S) [GrpObj A₁] (P₁ : LB (A₁ ⊗ A₁).left) (φ : A.left ⟶ A₁.left) (φ₂ : (A ⊗ A).left ⟶ (A₁ ⊗ A₁).left), P₁.IsLB → IsGrpPullback A A₁ f φ → IsSquare φ φ₂ → LBIso P (P₁.pull φ₂) → (∀ (T : Over S') (x : T ⟶ A), IsTrivial (slice A P x) → x = 1) → KerAlong A₁ P₁ f := by
  intro S S' f A _ P A₁ _ P₁ φ φ₂ hP₁ h hs hw hK T a ha x hx
  obtain ⟨w, hwg⟩ := hw
  obtain ⟨c, hc⟩ := hx
  let T' : Over S' := Over.mk a
  have hxw : x.left ≫ A₁.hom = a ≫ f := (Over.w x).trans ha.symm
  let x' : T' ⟶ A := Over.homMk (h.1.lift x.left a hxw) (h.1.lift_snd _ _ _)
  have hx' : x'.left ≫ φ = x.left := h.1.lift_fst _ _ _
  have key : x' = 1 := hK T' x' <| by
    let b : Over.mk ((T' ⊗ A).hom ≫ f) ⟶ T := Over.homMk (fst T' A).left (by
      show (fst T' A).left ≫ T.hom = (T' ⊗ A).hom ≫ f
      rw [← ha, ← Category.assoc]
      exact congrArg (· ≫ f) (Over.w (fst T' A)))
    let c' : Over.mk ((T' ⊗ A).hom ≫ f) ⟶ A₁ := pushPt h.1.w (snd T' A)
    have k₁ : (lift b c').left ≫ (fst T A₁).left = (fst T' A).left := congrArg (fun q => q.left) (lift_fst b c')
    have k₂ : (lift b c').left ≫ (snd T A₁).left = (snd T' A).left ≫ φ := congrArg (fun q => q.left) (lift_snd b c')
    have k₃ : (fst T' A ≫ x').left ≫ φ = (lift b c').left ≫ (fst T A₁ ≫ x).left := by
      rw [Over.comp_left, Over.comp_left, Category.assoc, hx', ← Category.assoc, k₁]
    have k₄ := GlobalTheory.SiegelDescent.lift_comp_square hs (T' := T' ⊗ A) (lift b c').left _ _ _ _ k₃ k₂.symm
    obtain ⟨c₂, h₂⟩ := gen_chartPull (chartPullSame P₁
      (fun _ : PUnit => (lift (fst T' A ≫ x') (snd T' A)).left ≫ φ₂) _ _ (lift b c').left fun _ => k₄) c hc
    exact exists_down_of_pGen (φ' := fun _ : PUnit => (lift (fst T' A ≫ x') (snd T' A)).left) (ε := fun _ => 1)
      ((isGen_iff w).1 hwg) hP₁ c₂ h₂
  let U : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk (𝟙 T.left) (by
    show 𝟙 T.left ≫ T.hom = a ≫ f
    rw [Category.id_comp, ha])
  have e₁ : U ≫ x = pushHom h T' x' := Over.OverMorphism.ext (by
    show 𝟙 T.left ≫ x.left = x'.left ≫ φ
    rw [Category.id_comp, hx'])
  have e₂ : U ≫ x = U ≫ (1 : T ⟶ A₁) := by
    rw [e₁, MonObj.comp_one]
    exact (congrArg (pushHom h T') key).trans (map_one (pushHom h T'))
  have e₃ : 𝟙 T.left ≫ x.left = 𝟙 T.left ≫ (1 : T ⟶ A₁).left := congrArg (fun q => q.left) e₂
  exact Over.OverMorphism.ext (by simpa only [Category.id_comp] using e₃)

end GlobalTheory.PrincSubring
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open Matrix

namespace GlobalTheory.ZarhinFam.KappaEx

def omegaB (h : ℕ) : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] ℤ :=
  LinearMap.mk₂ ℤ omegaStd
    (fun a a' b => by
      simp only [omegaStd, Pi.add_apply, ← Finset.sum_add_distrib]; congr 1; funext i; ring)
    (fun c a b => by
      simp only [omegaStd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]; congr 1; funext i; ring)
    (fun a b b' => by
      simp only [omegaStd, Pi.add_apply, ← Finset.sum_add_distrib]; congr 1; funext i; ring)
    (fun c a b => by
      simp only [omegaStd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]; congr 1; funext i; ring)

theorem omegaB_apply (h : ℕ) (a b : Fin h ⊕ Fin h → ℤ) : omegaB h a b = omegaStd a b := rfl

def emb (h : ℕ) (l : Fin 8) : Fin h ⊕ Fin h → Fin (8 * h) ⊕ Fin (8 * h) :=
  Sum.map (fun i => finProdFinEquiv (l, i)) (fun i => finProdFinEquiv (l, i))

def blk (h : ℕ) (l : Fin 8) : (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ) where
  toFun a := a ∘ emb h l
  map_zero' := rfl
  map_add' _ _ := rfl

theorem omegaStd_eq_sum_blk (h : ℕ) (a b : Fin (8 * h) ⊕ Fin (8 * h) → ℤ) :
    omegaStd a b = ∑ l, omegaStd (blk h l a) (blk h l b) := by
  simp only [omegaStd]
  rw [← (finProdFinEquiv (m := 8) (n := h)).sum_comp, Fintype.sum_prod_type]
  rfl

def vMat (d : ℕ) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ := fromBlocks 1 (-(quat d)ᵀ) 0 1

theorem vMat_transpose_mul_form_mul {d : ℕ} (hd : 0 < d) : (vMat d)ᵀ * form d * vMat d = 1 := by
  have h1 : ((d - 1 : ℕ) : ℤ) = (d : ℤ) - 1 := by omega
  rw [vMat, form, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply, ← fromBlocks_one]
  congr 1 <;> simp [Matrix.mul_neg, Matrix.neg_mul, quat_mul_transpose, h1, sub_smul]

theorem sum_sig {β : Type} [AddCommMonoid β] (g : Fin 4 ⊕ Fin 4 → β) : ∑ k, g (sig k) = ∑ s, g s := by
  simp [Fin.sum_univ_succ, Fintype.sum_sum_type, sig, add_assoc]

theorem sig_injective : Function.Injective sig := by
  intro k l hkl
  fin_cases k <;> fin_cases l <;> simp_all [sig]

def kap (h d : ℕ) (k : Fin 8) : (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ) :=
  ∑ l, vMat d (sig k) (sig l) • blk h l

theorem kap_apply (h d : ℕ) (k : Fin 8) (a : Fin (8 * h) ⊕ Fin (8 * h) → ℤ) :
    kap h d k a = ∑ l, vMat d (sig k) (sig l) • blk h l a := by
  simp [kap]

theorem inner_sum (d : ℕ) (m n : Fin 8) :
    ∑ k, ∑ l, vMat d (sig k) (sig m) * form d (sig k) (sig l) * vMat d (sig l) (sig n) =
      ((vMat d)ᵀ * form d * vMat d) (sig m) (sig n) := by
  have e1 : ∑ k, ∑ l, vMat d (sig k) (sig m) * form d (sig k) (sig l) * vMat d (sig l) (sig n) =
      ∑ p, ∑ l, vMat d p (sig m) * form d p (sig l) * vMat d (sig l) (sig n) :=
    sum_sig (fun p => ∑ l, vMat d p (sig m) * form d p (sig l) * vMat d (sig l) (sig n))
  have e2 : ∀ p, ∑ l, vMat d p (sig m) * form d p (sig l) * vMat d (sig l) (sig n) =
      ∑ q, vMat d p (sig m) * form d p q * vMat d q (sig n) :=
    fun p => sum_sig (fun q => vMat d p (sig m) * form d p q * vMat d q (sig n))
  rw [e1, Finset.sum_congr rfl fun p _ => e2 p]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem formZ_kap {h d : ℕ} (hd : 0 < d) (a b : Fin (8 * h) ⊕ Fin (8 * h) → ℤ) :
    formZ d h (fun k => kap h d k a) (fun k => kap h d k b) = omegaStd a b := by
  have e2 : ∀ k l, omegaStd (kap h d k a) (kap h d l b) =
      ∑ m, ∑ n, vMat d (sig k) (sig m) * vMat d (sig l) (sig n) * omegaStd (blk h m a) (blk h n b) := by
    intro k l
    rw [← omegaB_apply, kap_apply, kap_apply]

    simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    omegaB_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
    ring
  simp only [formZ, e2, Finset.mul_sum]
  have e3 : ∀ m n, ∑ k, ∑ l, form d (sig k) (sig l) *
      (vMat d (sig k) (sig m) * vMat d (sig l) (sig n) * omegaStd (blk h m a) (blk h n b)) =
      ((vMat d)ᵀ * form d * vMat d) (sig m) (sig n) * omegaStd (blk h m a) (blk h n b) := by
    intro m n
    rw [← inner_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  calc ∑ k, ∑ l, ∑ m, ∑ n, form d (sig k) (sig l) *
        (vMat d (sig k) (sig m) * vMat d (sig l) (sig n) * omegaStd (blk h m a) (blk h n b))
      = ∑ k, ∑ m, ∑ n, ∑ l, form d (sig k) (sig l) *
        (vMat d (sig k) (sig m) * vMat d (sig l) (sig n) * omegaStd (blk h m a) (blk h n b)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun m _ => Finset.sum_comm
    _ = ∑ m, ∑ n, ∑ k, ∑ l, form d (sig k) (sig l) *
        (vMat d (sig k) (sig m) * vMat d (sig l) (sig n) * omegaStd (blk h m a) (blk h n b)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun m _ => Finset.sum_comm
    _ = ∑ m, ∑ n, ((vMat d)ᵀ * form d * vMat d) (sig m) (sig n) * omegaStd (blk h m a) (blk h n b) := by
        simp only [e3]
    _ = omegaStd a b := by
        rw [vMat_transpose_mul_form_mul hd, omegaStd_eq_sum_blk]
        simp [Matrix.one_apply, sig_injective.eq_iff]

theorem blk_jlMap (h : ℕ) (l : Fin 8) (a : Fin h ⊕ Fin h → ℤ) :
    blk h l (jlMap h a) = if l = 0 then a else 0 := by
  funext x
  split_ifs with hl
  · subst hl
    rcases x with i | i <;> simp [blk, emb, jlMap]
  · have hl1 : 1 ≤ (l : ℕ) := Nat.one_le_iff_ne_zero.mpr fun h0 => hl (Fin.ext h0)
    rcases x with i | i <;> simp only [blk, emb, jlMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Function.comp_apply,
      Sum.map_inl, Sum.map_inr, Pi.zero_apply] <;> rw [dite_eq_right] <;> simp only [finProdFinEquiv_apply_val, not_lt] <;>
      nlinarith [i.2]

theorem kap_jlMap (h d : ℕ) (k : Fin 8) (a : Fin h ⊕ Fin h → ℤ) :
    kap h d k (jlMap h a) = if k = 0 then a else 0 := by
  rw [kap_apply]
  simp only [blk_jlMap, smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  fin_cases k <;> simp [vMat, sig]

end GlobalTheory.ZarhinFam.KappaEx

namespace GlobalTheory.ZarhinFam


open KappaEx in
theorem exists_kappaOK : ∀ (h M d : ℕ), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d →
    ∃ κ : Fin 8 → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ), GlobalTheory.ZarhinFam.KappaOK h M d κ := by
  intro h M d _ _ _ hd _
  refine ⟨kap h d, fun a b => ?_, fun a => ?_, fun k hk a => ?_⟩
  · rw [formZ_kap hd]
  · rw [kap_jlMap, if_pos rfl]
  · rw [kap_jlMap, if_neg hk]

end GlobalTheory.ZarhinFam
end
end
