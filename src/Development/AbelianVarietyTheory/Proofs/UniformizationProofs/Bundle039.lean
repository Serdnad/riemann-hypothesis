module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.OLinBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCommonField
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle015
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle037
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle010
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle016
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle011
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle035
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCAndCoordCorrespond
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle006
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFamOfIsPullDeg
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle004
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTwistBasisOffPrime
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle019

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT

theorem exists_genericFibre_iso_of_model_iso : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (U : UnifPre I D A G) (U' : UnifPre I D' A' G') (ψ : G' ≅ G), IsMonHom ψ.hom → LBIso U'.LG.L (U.LG.L.pull ψ.hom.left) → ∃ φ : A'.A ≅ A.A, IsMonHom φ.hom ∧ (Over.pullback (jK R)).map ψ.hom ≫ U.gen.hom = U'.gen.hom ≫ φ.hom ∧ LBIso A'.L (A.L.pull φ.hom.left) := by
  intro R _ _ I D D' A A' G G' _ _ _ _ U U' ψ hψ hL
  have := U.gen_hom
  have := U'.gen_hom
  have := hψ
  have hm : ((Over.pullback (jK R)).map ψ.hom).left ≫ pullback.fst G.hom (jK R) =
      pullback.fst G'.hom (jK R) ≫ ψ.hom.left :=
    pullback.lift_fst _ _ _
  have hi : U'.gen.inv.left ≫ U'.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, U'.gen.inv_hom_id, Over.id_left]
  refine ⟨U'.gen.symm ≪≫ (Over.pullback (jK R)).mapIso ψ ≪≫ U.gen, ?_, by simp, ?_⟩
  · show IsMonHom (U'.gen.inv ≫ (Over.pullback (jK R)).map ψ.hom ≫ U.gen.hom)
    infer_instance
  · have h₁ : LBIso A'.L (U'.LG.L.pull (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R))) :=
      LBIso.chartPull (chartPullSec A'.L _ U'.gen.inv.left hi)
        (chartPullSame U'.LG.L _ (fun _ => pullback.fst G'.hom (jK R)) _ U'.gen.inv.left fun _ => rfl) U'.ext
    have h₂ : LBIso (U'.LG.L.pull (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R)))
        (U.LG.L.pull ((U'.gen.inv.left ≫ pullback.fst G'.hom (jK R)) ≫ ψ.hom.left)) :=
      LBIso.chartPull (chartPullPull U'.LG.L _ _ rfl)
        (chartPullSame U.LG.L _ (fun _ => ψ.hom.left) _ _ fun _ => rfl) hL
    have h₃ : LBIso (A.L.pull (U'.gen.symm ≪≫ (Over.pullback (jK R)).mapIso ψ ≪≫ U.gen).hom.left)
        (U.LG.L.pull ((U'.gen.inv.left ≫ pullback.fst G'.hom (jK R)) ≫ ψ.hom.left)) :=
      LBIso.chartPull (h := U'.gen.inv.left ≫ ((Over.pullback (jK R)).map ψ.hom).left)
        (chartPullSame A.L _ (fun _ => U.gen.hom.left) _ _ fun _ => (Category.assoc _ _ _).symm)
        (chartPullSame U.LG.L _ (fun _ => pullback.fst G.hom (jK R)) _ _ fun _ =>
          (Category.assoc _ _ _).trans ((congrArg (U'.gen.inv.left ≫ ·) hm.symm).trans (Category.assoc _ _ _).symm))
        U.ext
    exact LBIso.trans A'.isLB (pull_isLB U.LG.isLB _) (pull_isLB A.isLB _)
      (LBIso.trans A'.isLB (pull_isLB U'.LG.isLB _) (pull_isLB U.LG.isLB _) h₁ h₂) h₃.symm

end GlobalTheory.UT
end
end

section

noncomputable section

namespace GlobalTheory.ArcLevel

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem epi_spMap {K k : Type} [Field K] [Field k] (β : K →+* k) : Epi (spMap β) := by
  have : Flat (spMap β) := inferInstance
  have : Surjective (spMap β) := ⟨fun y => ⟨default, Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem exists_genPt {R : Type} [CommRing R] [IsDomain R] {G : Over (Sp R)} {A : Over (Sp (FractionRing R))}
    (gen : (Over.pullback (jK R)).obj G ≅ A) {F : Type} [Field F] [Algebra (FractionRing R) F]
    (g : Sp F ⟶ G.left) (hg : g ≫ G.hom = jFK (R := R) F ≫ jK R) :
    ∃ x : TFK (R := R) F ⟶ A, x.left ≫ gen.inv.left ≫ pullback.fst G.hom (jK R) = g := by
  let z : TFK (R := R) F ⟶ (Over.pullback (jK R)).obj G :=
    Over.homMk (pullback.lift g (jFK (R := R) F) hg) (pullback.lift_snd _ _ _)
  refine ⟨z ≫ gen.hom, ?_⟩
  have hgi : gen.hom.left ≫ gen.inv.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left]
  show (z.left ≫ gen.hom.left) ≫ _ = _
  rw [Category.assoc, ← Category.assoc gen.hom.left, hgi, Category.id_comp]
  exact pullback.lift_fst _ _ _

theorem genRel_of_heq {F : Type} [Field F] {B B₀ : Scheme.{0}} {M : LB B} {M₀ : LB B₀} {φ φ' : B ⟶ B₀} (h : φ' = φ)
    {w : LB.Iso M (M₀.pull φ)} {w' : LB.Iso M (M₀.pull φ')} (hw : HEq w' w)
    {K : Type} [Fintype K] {pt : K → (Sp F ⟶ B)} {pt₀ : K → (Sp F ⟶ B₀)} {ε : K → ℤ}
    {t : LB.Gen (LB.LinComb M pt ε)} {t₀ : LB.Gen (LB.LinComb M₀ pt₀ ε)} {x : F} (H : GenRel w t t₀ x) :
    GenRel w' t t₀ x := by
  subst h
  obtain rfl := eq_of_heq hw
  exact H

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem exists_conj_part (v : D.La) : ∃ v' ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
    ∀ {S : Scheme.{0}} {B : Type} [CommRing B] {b : Base l B} {s : S ⟶ Sp B} (o : Obj D l b s),
      o.eta v = o.eta v' := by
  have h : v ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) ⊔
      l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La) := by
    rw [← Submodule.sup_smul, l.coprime, Submodule.top_smul]; trivial
  obtain ⟨v₁, h₁, v₂, h₂, rfl⟩ := Submodule.mem_sup.1 h
  exact ⟨v₂, h₂, fun o => by rw [o.eta_add, o.eta_ker _ h₁, _root_.one_mul]⟩

variable {Xo : Moduli D l} {c : Coeff l} {k : Type} [Field k] {bF : c.F →+* k} {a : ArcIn D l (RingHom.id c.F) k bF}

theorem witData {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {χ : Sp (PowerSeries k) ⟶ Y.X}
    (W : ArcWit Y (a.restrict β) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ) :
    WitData a W.P.D W.P.oD W.φ W.he W.w W.e := by
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := W.spec
  exact ⟨s1, s2, s3, s4, s5, fun F _ _ _ _ uF h₁ h₂ => (s6 F uF h₁ h₂).1⟩



theorem level_core (hL : Laws) (hL2 : Laws2) (h5 : Laws5) {O O' : Type} [CommRing O] [CommRing O']
    {β : O →+* c.F} {β' : O' →+* c.F} {Y : Model Xo c β} {Y' : Model Xo c β'}
    {χ : Sp (PowerSeries k) ⟶ Y.X} {χ' : Sp (PowerSeries k) ⟶ Y'.X}
    (W : ArcWit Y (a.restrict β) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ)
    (W' : ArcWit Y' (a.restrict β') (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ')
    (hD : IsPullDeg (RingHom.id (PowerSeries k)) W'.P.D.toPre W.P.D.toPre)
    (hφ : (hD.e.hom.left ≫ pullback.fst W'.P.D.toPre.P.A.hom (specOf (RingHom.id (PowerSeries k)))) ≫ W'.φ = W.φ)
    (hxe : ∀ x, hD.xe (W.e x) = W'.e x)
    (w₁ : LB.Iso W.P.D.toPre.P.L (a.D₀.P.L.pull ((hD.e.hom.left ≫
      pullback.fst W'.P.D.toPre.P.A.hom (specOf (RingHom.id (PowerSeries k)))) ≫ W'.φ)))
    (hw₁ : HEq w₁ W.w) (T : Tri W'.w hD.w w₁) (ψ : W.t.G ≅ W'.t.G)
    (bc : W.t.G ≅ (Over.pullback (specOf (RingHom.id (PowerSeries k)))).obj W'.t.G) (hbc : IsMonHom bc.hom)
    (hψ : bc.hom.left ≫ pullback.fst W'.t.G.hom (specOf (RingHom.id (PowerSeries k))) = ψ.hom.left)
    (hPU : IsPullUnif (RingHom.id (PowerSeries k)) hD bc W'.P.U W.P.U)
    (y y' : Sp (FractionRing (PowerSeries k)) ⟶ Xo.XF c) (hy : y ≫ Y.j = jK (PowerSeries k) ≫ χ)
    (hy' : y' ≫ Y'.j = jK (PowerSeries k) ≫ χ') (n : ℕ) (p₀ : QkPt a.D₀ (FractionRing k) n)
    (σ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G) (σ' : 𝟙_ (Over (Xo.XF c)) ⟶ Y'.oF.t.G)
    (hσ : (n = l.A ∧ ∃ v, HEq p₀ (a.etaA v) ∧ σ = Y.oF.etaA v ∧ σ' = Y'.oF.etaA v) ∨
      (n = l.M ∧ ∃ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
        HEq p₀ (a.eta v) ∧ σ = Y.oF.eta v ∧ σ' = Y'.oF.eta v))
    (g : Sp (FractionRing (PowerSeries k)) ⟶ W.t.G.left) (hg : g ≫ W.t.G.hom = jK (PowerSeries k))
    (hgm : g ≫ W.m.φ = y ≫ σ.left ≫ Y.m.φ) : g ≫ ψ.hom.left ≫ W'.m.φ = y' ≫ σ'.left ≫ Y'.m.φ := by
  have hG : GlobalFnsSt := globalFns_holds
  have hR := admissibleBase_powerSeries k
  obtain ⟨F, _, _, _, _, hF⟩ := ArcTransport.exists_commonField k
  have hn : 1 ≤ n := by
    rcases hσ with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact l.A_pos
    · exact le_trans (by norm_num) l.three_le
  have hn' : n ∣ l.M' := by
    rcases hσ with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact Nat.dvd_lcm_right _ _
    · exact Nat.dvd_lcm_left _ _
  obtain ⟨q₀, e1, -⟩ := TorusExt.existsUnique_qkExt a.bimult (algebraMap (FractionRing k) F) (RingHom.comp_id _) p₀
  obtain ⟨q, e2, e3⟩ := ArcTransport.exists_transport (witData W) hF rfl hG hn' q₀
  have hF' : ∀ r : PowerSeries k, algebraMap (FractionRing (PowerSeries k)) F (algebraMap _ _ r) =
      algebraMap (FractionRing (PowerSeries k)) F (algebraMap _ _ ((RingHom.id _) r)) := fun _ => rfl
  obtain ⟨q', hq₁, hq₂⟩ := qkPullExists hG _ _ (RingHom.id _) W'.P.D.toPre W.P.D.toPre hD F hF' n q

  have hc : (y' ≫ σ'.left ≫ Y'.m.φ) ≫ Y'.t.G.hom = jK (PowerSeries k) ≫ χ' := by
    have a₁ : Y'.m.φ ≫ Y'.t.G.hom = Y'.oF.t.G.hom ≫ Y'.j := Y'.m.cart.1.w
    have a₂ : σ'.left ≫ Y'.oF.t.G.hom = 𝟙 _ := Over.w σ'
    rw [Category.assoc, Category.assoc, a₁, reassoc_of% a₂, hy']
  let g' : Sp (FractionRing (PowerSeries k)) ⟶ W'.t.G.left := W'.m.cart.1.lift _ _ hc
  have hg' : g' ≫ W'.t.G.hom = jK (PowerSeries k) := W'.m.cart.1.lift_snd _ _ _
  have hgm' : g' ≫ W'.m.φ = y' ≫ σ'.left ≫ Y'.m.φ := W'.m.cart.1.lift_fst _ _ _
  have hih : ψ.inv.left ≫ ψ.hom.left = 𝟙 _ := by rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  obtain ⟨x, hx⟩ := exists_genPt W.P.U.gen (jFK (R := PowerSeries k) F ≫ g) (by rw [Category.assoc, hg])
  obtain ⟨x', hx'⟩ := exists_genPt W'.P.U.gen (jFK (R := PowerSeries k) F ≫ g') (by rw [Category.assoc, hg'])
  obtain ⟨x'', hx''⟩ := exists_genPt W.P.U.gen (jFK (R := PowerSeries k) F ≫ g' ≫ ψ.inv.left)
    (by rw [Category.assoc, Category.assoc, Over.w, hg'])
  have t₁ : QkToAkU W.P.U.toUnifPre F n q x := by
    refine (W.spec.2.2.2.2.2 F _ hF rfl).2 (jFK (R := PowerSeries k) F ≫ y) (by rw [Category.assoc, hy]) n p₀ σ ?_
      q₀ q x e1 e2 e3 ?_
    · rcases hσ with ⟨h, v, h₁, h₂, -⟩ | ⟨h, v, hv, h₁, h₂, -⟩
      · exact Or.inl ⟨h, v, h₁, h₂⟩
      · exact Or.inr ⟨h, v, hv, h₁, h₂⟩
    · rw [reassoc_of% hx, hgm, Category.assoc]
  have t₂ : QkToAkU W'.P.U.toUnifPre F n q' x' := by
    refine (W'.spec.2.2.2.2.2 F _ hF rfl).2 (jFK (R := PowerSeries k) F ≫ y') (by rw [Category.assoc, hy']) n p₀ σ' ?_
      q₀ q' x' e1 ?_ (fun z => ?_) ?_
    · rcases hσ with ⟨h, v, h₁, -, h₂⟩ | ⟨h, v, hv, h₁, -, h₂⟩
      · exact Or.inl ⟨h, v, h₁, h₂⟩
      · exact Or.inr ⟨h, v, hv, h₁, h₂⟩
    · have : hD.xe q.y = q'.y := by rw [hq₁, AddEquiv.apply_symm_apply]
      rw [← this, e2]; exact hxe _
    · obtain ⟨hψ', hm⟩ := hq₂.2 (W.e z)
      have pm := (maps_iff hD.w _ _ _ (q.g.s (W.e z)) (q'.g.s (hD.xe (W.e z))) (𝟙 _) _
        (GeneratorPullback.pullAlong_le _ _ _ _ _ hψ') (fun _ => rfl)).1 hm
      have k' := (genRel_transfer T W'.P.D.toPre.P.isLB W.P.D.toPre.P.isLB hψ' pm _ _).2
        (genRel_of_heq hφ hw₁ (e3 z))
      rw [hxe z] at k'
      exact k'
    · rw [reassoc_of% hx', hgm', Category.assoc]
  have t₃ : QkToAkU W.P.U.toUnifPre F n q x'' :=
    h5.qkBaseChange _ _ _ _ hR hR (RingHom.id _) W'.P.D W'.P.A W'.t.G W'.P.U W.t.G bc hbc W.P.A W.P.D hD W.P.U
      hPU F hF' n hn q' x' q x'' hq₁ hq₂ (by rw [hψ, reassoc_of% hx'', hih, Category.comp_id, hx']) t₂
  have hxx := TorsionImage.qkToAkU_unique hL hL2 _ _ hR W.P.D W.P.A W.t.G W.t.semi W.P.U F n hn q x x'' t₁ t₃
  have := epi_spMap (algebraMap (FractionRing (PowerSeries k)) F)
  have hgg : g = g' ≫ ψ.inv.left :=
    (cancel_epi (spMap (algebraMap (FractionRing (PowerSeries k)) F))).1 (hx.symm.trans (hxx ▸ hx''))
  rw [hgg, Category.assoc, reassoc_of% hih, hgm']

theorem level_match : Laws → Laws2 → Laws5 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (Y : Model Xo c β) (Y' : Model Xo c β') (χ : Sp (PowerSeries k) ⟶ Y.X) (χ' : Sp (PowerSeries k) ⟶ Y'.X) (W : ArcWit Y (a.restrict β) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ) (W' : ArcWit Y' (a.restrict β') (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ') (hD : IsPullDeg (RingHom.id (PowerSeries k)) W'.P.D.toPre W.P.D.toPre), ((hD.e.hom.left ≫ pullback.fst W'.P.D.toPre.P.A.hom (specOf (RingHom.id (PowerSeries k)))) ≫ W'.φ = W.φ ∧ (∀ x, hD.xe (W.e x) = W'.e x) ∧ ∃ w₁ : LB.Iso W.P.D.toPre.P.L (a.D₀.P.L.pull ((hD.e.hom.left ≫ pullback.fst W'.P.D.toPre.P.A.hom (specOf (RingHom.id (PowerSeries k)))) ≫ W'.φ)), HEq w₁ W.w ∧ Tri W'.w hD.w w₁) → ∀ (ψ : W.t.G ≅ W'.t.G) (bc : W.t.G ≅ (Over.pullback (specOf (RingHom.id (PowerSeries k)))).obj W'.t.G), IsMonHom ψ.hom → IsMonHom bc.hom → bc.hom.left ≫ pullback.fst W'.t.G.hom (specOf (RingHom.id (PowerSeries k))) = ψ.hom.left → IsPullUnif (RingHom.id (PowerSeries k)) hD bc W'.P.U W.P.U → (∀ x, W.t.act.act x ≫ ψ.hom = ψ.hom ≫ W'.t.act.act x) → ∀ (y y' : Sp (FractionRing (PowerSeries k)) ⟶ Xo.XF c), y ≫ Y.j = jK (PowerSeries k) ≫ χ → y' ≫ Y'.j = jK (PowerSeries k) ≫ χ' → y ≫ pullback.snd _ _ = jK (PowerSeries k) ≫ spMap (PowerSeries.C (R := k)) ≫ spMap bF → y' ≫ pullback.snd _ _ = jK (PowerSeries k) ≫ spMap (PowerSeries.C (R := k)) ≫ spMap bF → (∀ (σ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G) (σ' : 𝟙_ (Over (Xo.XF c)) ⟶ Y'.oF.t.G), ((∃ v, σ = Y.oF.etaA v ∧ σ' = Y'.oF.etaA v) ∨ ∃ v, σ = Y.oF.eta v ∧ σ' = Y'.oF.eta v) → ∀ g : Sp (FractionRing (PowerSeries k)) ⟶ W.t.G.left, g ≫ W.t.G.hom = jK (PowerSeries k) → g ≫ W.m.φ = y ≫ σ.left ≫ Y.m.φ → g ≫ ψ.hom.left ≫ W'.m.φ = y' ≫ σ'.left ≫ Y'.m.φ) := by
  intro hL hL2 h5 E _ _ _ H D l Xo c k _ bF a O O' _ _ β β' Y Y' χ χ' W W' hD ⟨hφ, hxe, w₁, hw₁, T⟩ ψ bc _ hbc hψ hPU _
    y y' hy hy' _ _ σ σ' hσ g hg hgm
  rcases hσ with ⟨v, h₁, h₂⟩ | ⟨v, h₁, h₂⟩
  · exact level_core hL hL2 h5 W W' hD hφ hxe w₁ hw₁ T ψ bc hbc hψ hPU y y' hy hy' l.A (a.etaA v) σ σ'
      (Or.inl ⟨rfl, v, HEq.rfl, h₁, h₂⟩) g hg hgm
  · obtain ⟨v', hv', e⟩ := exists_conj_part (l := l) v
    exact level_core hL hL2 h5 W W' hD hφ hxe w₁ hw₁ T ψ bc hbc hψ hPU y y' hy hy' l.M (a.eta v') σ σ'
      (Or.inr ⟨rfl, v', hv', HEq.rfl, h₁.trans (e _), h₂.trans (e _)⟩) g hg hgm

end GlobalTheory.ArcLevel
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace CharAgree

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D' : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem comp_q_eq_one_iff (g : GtCoord I D e G)
    {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (a : Z ⟶ thickObj R I e G) :
    a ≫ g.q = toUnit _ ≫ η[thickObj R I e D.P.A] ↔
      a.left ≫ g.pG.left = a.left ≫ (fstG I e G).left ≫ G.hom ≫ eSec D.P.A := by
  have h1 : (a ≫ g.q).left ≫ pullback.fst D.P.A.hom (thick R I e) = a.left ≫ g.pG.left :=
    Category.assoc _ _ _
  have h2 : (toUnit Z ≫ η[thickObj R I e D.P.A]).left ≫ pullback.fst D.P.A.hom (thick R I e) =
      a.left ≫ (fstG I e G).left ≫ G.hom ≫ eSec D.P.A := by
    have k1 := UnitValue.eSec_pullback_fst (thick R I e) D.P.A
    have k2 : (toUnit Z).left = a.left ≫ pullback.snd G.hom (thick R I e) :=
      ((Category.comp_id _).symm.trans (Over.w (toUnit Z))).trans (Over.w a).symm
    have k3 : pullback.fst G.hom (thick R I e) ≫ G.hom =
        pullback.snd G.hom (thick R I e) ≫ thick R I e := pullback.condition
    refine (Category.assoc _ _ _).trans ((congrArg ((toUnit Z).left ≫ ·) k1).trans ?_)
    refine (congrArg (· ≫ thick R I e ≫ eSec D.P.A) k2).trans ((Category.assoc _ _ _).trans ?_)
    refine congrArg (a.left ≫ ·) ((Category.assoc _ _ _).symm.trans ?_)
    exact (congrArg (· ≫ eSec D.P.A) k3.symm).trans (Category.assoc _ _ _)
  refine ⟨fun h => h1.symm.trans ((congrArg (fun φ => φ.left ≫ _) h).trans h2), fun h => ?_⟩
  refine Over.OverMorphism.ext (pullback.hom_ext (h1.trans (h.trans h2.symm)) ?_)
  exact (Over.w _).trans (Over.w _).symm

def Match (g : GtCoord I D e G) (g' : GtCoord I D' e G) (xe : D'.X → D.X) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι)
    (J' : (Z ⟶ D'.P.A.left) → D'.P.L.ι), Good D.P.L z J → Good D'.P.L z J' →
    r ≫ g.pG.left = r ≫ (fstG I e G).left ≫ G.hom ≫ eSec D.P.A →
    r ≫ g'.pG.left = r ≫ (fstG I e G).left ≫ G.hom ≫ eSec D'.P.A →
    ∀ x, val (g.t (xe x)) r z J = val (g'.t x) r z J'

omit [IsDomain R] in
theorem connected_thick [IsLocalRing R] (hI : I ≠ ⊤) (e : ℕ) :
    ConnectedSpace (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := by
  have hJ : I ^ (e + 1) ≠ ⊤ := fun h =>
    hI (top_le_iff.1 (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero e)))
  have : Nontrivial (R ⧸ I ^ (e + 1)) := Ideal.Quotient.nontrivial_iff.2 hJ
  have : IsLocalRing (R ⧸ I ^ (e + 1)) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have : PreconnectedSpace (PrimeSpectrum (R ⧸ I ^ (e + 1))) := by
    refine ⟨isPreconnected_of_forall (IsLocalRing.closedPoint _) fun y _ => ?_⟩
    exact ⟨closure {y}, Set.subset_univ _,
      (IsLocalRing.specializes_closedPoint y).mem_closure, subset_closure rfl,
      isPreconnected_singleton.closure⟩
  exact ({ toNonempty := inferInstance } : ConnectedSpace (PrimeSpectrum (R ⧸ I ^ (e + 1))))

variable [IsLocalRing R] [IsNoetherianRing R] (hI : I ≠ ⊤)
include hI

theorem exists_torus_iso (g : GtCoord I D e G) (g' : GtCoord I D' e G) :
    ∃ θ : splitTorus _ D'.X ≅ splitTorus _ D.X, IsMonHom θ.hom ∧ θ.hom ≫ g.i = g'.i := by
  have m : Mono g.i := ⟨fun a b h => g.isKernel.hom_ext h (toUnit_unique _ _)⟩
  have m' : Mono g'.i := ⟨fun a b h => g'.isKernel.hom_ext h (toUnit_unique _ _)⟩
  have := g.i_hom
  have := g'.i_hom
  let u := g.isKernel.lift g'.i (toUnit _) (gtCoord_i_comp_q hI g g')
  let v := g'.isKernel.lift g.i (toUnit _) (gtCoord_i_comp_q hI g' g)
  have hu : u ≫ g.i = g'.i := g.isKernel.lift_fst _ _ _
  have hv : v ≫ g'.i = g.i := g'.isKernel.lift_fst _ _ _
  refine ⟨⟨u, v, ?_, ?_⟩, ⟨?_, ?_⟩, hu⟩
  · rw [← cancel_mono g'.i, Category.assoc, hv, hu, Category.id_comp]
  · rw [← cancel_mono g.i, Category.assoc, hu, hv, Category.id_comp]
  · change η ≫ u = η
    rw [← cancel_mono g.i, Category.assoc, hu, IsMonHom.one_hom, IsMonHom.one_hom]
  · change μ ≫ u = (u ⊗ₘ u) ≫ μ
    rw [← cancel_mono g.i, Category.assoc, hu, IsMonHom.mul_hom, Category.assoc, IsMonHom.mul_hom,
      tensorHom_comp_tensorHom_assoc, hu]

theorem exists_match (g : GtCoord I D e G) (g' : GtCoord I D' e G) :
    ∃ xe : D'.X ≃+ D.X, Match g g' xe := by
  obtain ⟨θ, hθ, hi⟩ := exists_torus_iso hI g g'
  have := connected_thick hI e
  obtain ⟨xe, hx⟩ := exists_addEquiv_of_splitTorus_iso _ D.X D'.X θ hθ
  refine ⟨xe, fun Z r z J J' hJ hJ' _ h' x => ?_⟩
  let FinalForm : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) :=
    Over.mk (r ≫ (thickObj R I e G).hom)
  let a : FinalForm ⟶ thickObj R I e G := Over.homMk r rfl
  let τ := g'.isKernel.lift a (toUnit _) ((comp_q_eq_one_iff g' a).2 h')
  have hτ : τ ≫ g'.i = a := g'.isKernel.lift_fst _ _ _
  have hτ' : (τ ≫ θ.hom) ≫ g.i = a := by rw [Category.assoc, hi, hτ]
  have k := (TorusCoord.val_torus_point_and_translate R I D e G g FinalForm (τ ≫ θ.hom) 1 z J hJ (xe x)).1
  have k' := (TorusCoord.val_torus_point_and_translate R I D' e G g' FinalForm τ 1 z J' hJ' x).1
  rw [hτ'] at k
  rw [hτ] at k'
  refine k.trans (Eq.trans (Units.ext ?_) k'.symm)
  rw [gm_val _ _ ⊤ trivial, gm_val _ _ ⊤ trivial]
  refine congrArg (FinalForm.left.presheaf.germ ⊤ z trivial).hom ?_
  exact (SplitTorusHom.appTop_comp τ θ.hom _).trans (congrArg τ.left.appTop.hom (hx x))

theorem match_unique (g : GtCoord I D e G) (g' : GtCoord I D' e G) {f f' : D'.X → D.X}
    (h : Match g g' f) (h' : Match g g' f') : f = f' := by
  funext x
  have := connected_thick hI e
  refine SplitTorusHom.charUnit_injective (S := Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))
    (congrArg Units.val (unit_ext fun z _ => ?_))
  choose J hJ using fun ψ : (splitTorus _ D.X).left ⟶ D.P.A.left => exists_chart D.P.isLB (ψ z)
  choose J' hJ' using fun ψ : (splitTorus _ D.X).left ⟶ D'.P.A.left => exists_chart D'.P.isLB (ψ z)
  have c := (comp_q_eq_one_iff g g.i).1 g.isKernel.w
  have c' := (comp_q_eq_one_iff g' g.i).1 (gtCoord_i_comp_q hI g' g)
  have k := fun χ =>
    (TorusCoord.val_torus_point_and_translate R I D e G g _ (𝟙 _) 1 z J hJ χ).1
  simp only [Category.id_comp] at k
  exact (k _).symm.trans (((h _ _ z J J' hJ hJ' c c' x).trans
    (h' _ _ z J J' hJ hJ' c c' x).symm).trans (k _))


omit hI [IsLocalRing R] [IsNoetherianRing R] in
theorem match_down {D D' : DegData R I} {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    (U : UnifPre I D A G) (U' : UnifPre I D' A' G) {f : D'.toPre.X → D.toPre.X}
    (h : Match (U.gt (e + 1)) (U'.gt (e + 1)) f) : Match (U.gt e) (U'.gt e) f := by
  intro Z r z J J' hJ hJ' c c' x
  have t : thickMap R I e G ≫ (fstG I (e + 1) G).left = (fstG I e G).left :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have up : ∀ {Y : Scheme.{0}} (p : (thickObj R I (e + 1) G).left ⟶ Y)
      (p₀ : (thickObj R I e G).left ⟶ Y) (s : G.left ⟶ Y), thickMap R I e G ≫ p = p₀ →
      r ≫ p₀ = r ≫ (fstG I e G).left ≫ s →
      (r ≫ thickMap R I e G) ≫ p = (r ≫ thickMap R I e G) ≫ (fstG I (e + 1) G).left ≫ s := by
    intro Y p p₀ s h₁ h₂
    refine (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) h₁).trans (h₂.trans ?_))
    refine Eq.trans (congrArg (r ≫ ·) ?_) (Category.assoc _ _ _).symm
    exact (congrArg (· ≫ s) t.symm).trans (Category.assoc _ _ _)
  have k := h Z (r ≫ thickMap R I e G) z J J' hJ hJ' (up _ _ _ (U.gt_q e) c)
    (up _ _ _ (U'.gt_q e) c') x
  exact (val_corr hJ (U.gt_t e (f x)) r).symm.trans ((val_pull hJ _ _ _).trans (k.trans
    ((val_pull hJ' _ _ _).symm.trans (val_corr hJ' (U'.gt_t e x) r))))

end CharAgree


open CharAgree in
theorem unifPre_characterGroup_iso : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G), ∃ xe : D'.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG I e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U'.gt e).pG.left = r ≫ (fstG I e G).left ≫ G.hom ≫ eSec D'.toPre.P.A → ∀ x, Geo.Tor.val ((U.gt e).t (xe x)) r z J = Geo.Tor.val ((U'.gt e).t x) r z J') := by
  intro R _ _ _ I hR D D' A A' G _ _ _ U U'
  obtain ⟨hN, -, -, hC⟩ := hR
  have hI : I ≠ ⊤ := by
    rintro rfl
    have : Subsingleton R := IsHausdorff.subsingleton hC.toIsHausdorff
    exact false_of_nontrivial_of_subsingleton R
  choose xe hxe using fun e => exists_match hI (U.gt e) (U'.gt e)
  have down : ∀ (e : ℕ) (f : D'.toPre.X → D.toPre.X), Match (U.gt e) (U'.gt e) f →
      Match (U.gt 0) (U'.gt 0) f := by
    intro e f
    induction e with
    | zero => exact id
    | succ e ih => exact fun h => ih (match_down U U' h)
  refine ⟨xe 0, fun e => ?_⟩
  have h := hxe e
  rw [match_unique hI _ _ (down e _ h) (hxe 0)] at h
  exact h

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.unifPre_c_and_coord_correspond_alt : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G) (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso D'.toPre.P.L (D.toPre.P.L.pull Φ.hom.left)), w.IsGen → IsMonHom Φ.hom → (∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left) → ∀ xe : D'.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG I e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U'.gt e).pG.left = r ≫ (fstG I e G).left ≫ G.hom ≫ eSec D'.toPre.P.A → ∀ x, Geo.Tor.val ((U.gt e).t (xe x)) r z J = Geo.Tor.val ((U'.gt e).t x) r z J') → ((∀ x, D'.toPre.c x ≫ Φ.hom = D.toPre.c (xe x)) ∧ ∀ e : ℕ, ((U'.gt e).pG.left ≫ Φ.hom.left = (𝟙 _) ≫ (U.gt e).pG.left ∧ ∀ x : D'.toPre.X, (∀ κ : Fin 4, D'.toPre.Oφ (U'.gt e).pG x κ ≫ Φ.hom.left = (𝟙 _) ≫ D.toPre.Oφ (U.gt e).pG (xe x) κ) ∧ Geo.Tor.PMaps w (D'.toPre.Oφ (U'.gt e).pG x) (D.toPre.Oφ (U.gt e).pG (xe x)) Oinvε ((U'.gt e).t x) ((U.gt e).t (xe x)) (𝟙 _))) := by
  first | exact @GlobalTheory.unifPre_c_and_coord_correspond | exact GlobalTheory.unifPre_c_and_coord_correspond | (intros; apply GlobalTheory.unifPre_c_and_coord_correspond <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_sec_of_generic_fibre : ∀ (V : Type) [CommRing V] [IsDomain V] (Z : Scheme.{0}) (L : LB Z), L.IsLB → ∀ (Y : Over (Spec (CommRingCat.of V))) [QuasiCompact Y.hom] [IsSeparated Y.hom] (K : Type) [Fintype K] (φ : K → (Y.left ⟶ Z)) (ε : K → ℤ) (s : LB.Sec (LB.LinComb L (fun k => (snd (TK V) Y).left ≫ φ k) ε)), ∃ (r : V) (_ : r ≠ 0) (σ : LB.Sec (LB.LinComb L φ ε)), ∀ (T : Scheme.{0}) (ρ : T ⟶ (TK V ⊗ Y).left) (z : T) (J), Good L z J → sval σ (ρ ≫ (snd (TK V) Y).left) z J = gs ρ z ⊤ (scal (TK V ⊗ Y).hom r) * sval s ρ z J := by
  intro V _ _ Z L hL Y _ _ K _ φ ε s
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  have : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  have H : IsPullback (snd (TK V) Y).left (fst (TK V) Y).left Y.hom
      (Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))) :=
    (IsPullback.of_hasPullback (TK V).hom Y.hom).flip
  obtain ⟨t, ht, σ, hσ⟩ := TwistLoc.exists_clear_denominator (nonZeroDivisors V) H hL φ ε s
  refine ⟨t, nonZeroDivisors.ne_zero ht, σ, fun T ρ z J hJ => ?_⟩
  rw [sval_of σ (ρ ≫ (snd (TK V) Y).left) z J (fun k => J (ρ ≫ (snd (TK V) Y).left ≫ φ k))
    (fun k => by rw [Category.assoc])]
  refine (hσ T ρ z _ (hJ.mem (fun k => (snd (TK V) Y).left ≫ φ k) ρ)).trans (congrArg₂ (· * ·) ?_ rfl)
  rw [Over.w (snd (TK V) Y)]
  exact (gs_pull ρ (TK V ⊗ Y).hom z ⊤ trivial _).symm

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.exists_fam_of_isPullDeg_alt : GlobalFnsSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg φ D D') (k : ℕ) (F : Fam D (FractionRing R) k) (f : ∀ α, D.SecB k α) (f' : ∀ α, D'.SecB k α), (∀ α, GeneratorPullback.SecScal D.P.L (DegPre.famφ D (FractionRing R) α) (DegPre.famε k) (F.s α) (D.famφB α) (DegPre.famε k) (f α) (DegPre.prB D (FractionRing R)).left 1) → (∀ x : D'.X, (∀ (Z : Scheme.{0}) (r : Z ⟶ D'.P.A.left) (z : Z) (p : Fin 4 → D.P.L.ι) (q : Fin 4 → D'.P.L.ι), (∀ κ, ((hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))) ((D'.famφB x) κ (r z)) ∈ D.P.L.U (p κ)) → (∀ κ, (D'.famφB x) κ (r z) ∈ D'.P.L.U (q κ)) → Geo.Tor.gs (r ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))) z (LB.wchart D.P.L (D.famφB (hD.xe x)) p) ((f (hD.xe x)).f p) = (∏ κ, Geo.Tor.gw hD.w (r ≫ (D'.famφB x) κ) z (p κ) (q κ) ^ (DegPre.famε k) κ).val * Geo.Tor.gs r z (LB.wchart D'.P.L (D'.famφB x) q) ((f' x).f q))) → ∃ F' : Fam D' (FractionRing R') k, (∀ α, GeneratorPullback.SecScal D'.P.L (DegPre.famφ D' (FractionRing R') α) (DegPre.famε k) (F'.s α) (D'.famφB α) (DegPre.famε k) (f' α) (DegPre.prB D' (FractionRing R')).left 1) := by
  first | exact @GlobalTheory.exists_fam_of_isPullDeg | exact GlobalTheory.exists_fam_of_isPullDeg | (intros; apply GlobalTheory.exists_fam_of_isPullDeg <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.exists_twist_basis_off_prime : PolBaseChangeSt → GlobalFnsSt → DVR.TwistBaseChangeStatement → ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (D : DegPre R), (∃ W : (Spec (CommRingCat.of R)).Opens, genericPoint (Spec (CommRingCat.of R)) ∈ W ∧ Nonempty (PsiOn D W)) → ∀ (p : Ideal R) [p.IsPrime] (k : ℕ), 1 ≤ k → ∀ α : D.X, ∃ b : Fin (k ^ D.P.g) → D.SecB k α, ∀ (R' : Type) [CommRing R'] (f : R →+* R'), (∀ s ∉ p, IsUnit (f s)) → ∀ b' : Fin (k ^ D.P.g) → LB.Sec (LB.LinComb D.P.L (fun i => (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left ≫ DegPre.famφB D α i) (DegPre.famε k)), (∀ i, IsPullSecLC D.P.L (DegPre.famφB D α) (DegPre.famε k) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left (b i) (b' i)) → IsSecBasis (T := Over.mk (Spec.map (CommRingCat.ofHom f))) (A := D.P.A) _ b' := by
  first | exact @GlobalTheory.TwistLoc.exists_basis_off_prime | exact GlobalTheory.TwistLoc.exists_basis_off_prime | (intros; apply GlobalTheory.TwistLoc.exists_basis_off_prime <;> assumption)
end
