module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRatioPoints
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle011
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtCoordCompatOfPull
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HasBasisOfBasis
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Connected
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Development.AbelianVarietyTheory.BlockTheory.UniformisationCharts.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory
namespace CoordReduction

theorem exists_ratio {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ φ' : K → (Y ⟶ X)}
    {ε : K → ℤ} (hφ : ∀ k, φ k = φ' k) {u : LB.Gen (LB.LinComb L φ ε)} {u' : LB.Gen (LB.LinComb L φ' ε)}
    (hu : u.IsGen) (hu' : u'.IsGen) :
    ∃ ρ : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      val u r z J = gm r z ⊤ ρ * val u' r z J := by
  obtain ⟨t, -, hv⟩ := exists_gen hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, hφ, mul_inv_cancel])
    (LB.mulGen L _ _ _ _ u (LB.invGen L _ _ u')) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ hu'))
  have le : (⊤ : Y.Opens) ≤ LB.wchart L (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨res le (t.s PEmpty.elim), fun Z r z J hJ => ?_⟩
  have h := hv Z r z J hJ
  rw [val_mul hJ, val_inv, val_of t r z J PEmpty.elim (fun k => k.elim)] at h
  exact mul_inv_eq_iff_eq_mul.1 ((gm_res r z le trivial _).trans h).symm

theorem gm_char_comp {S S' Z : Scheme.{0}} {X : Type} [AddCommGroup X]
    (β : (splitTorus S' X).left ⟶ (splitTorus S X).left) (χ : X)
    (h : β.appTop.hom (charUnit S X χ).val = (charUnit S' X χ).val) (τ : Z ⟶ (splitTorus S' X).left) (z : Z) :
    gm (τ ≫ β) z ⊤ (charUnit S X χ) = gm τ z ⊤ (charUnit S' X χ) :=
  (gm_pull τ β z ⊤ trivial _).symm.trans (congrArg (gm τ z ⊤) (Units.ext h))

section Abstract

variable {X S S' : Scheme.{0}} {L : LB X} {H : Over S} {H' : Over S'} [GrpObj H] [GrpObj H'] {f : S' ⟶ S}
  {F : H'.left ⟶ H.left} (hp : IsGrpPullback H' H f F) {K : Type} [Fintype K] {φ : K → (H.left ⟶ X)} {ε : K → ℤ}
  (t : LB.Gen (LB.LinComb L φ ε))
include hp

theorem val_unit_pull
    (h : ∀ (Z : Over S) (z : Z.left) (J), Good L z J → val t (1 : Z ⟶ H).left z J = 1)
    {Z : Over S'} {z : Z.left} {J} (hJ : Good L z J) : val t ((1 : Z ⟶ H').left ≫ F) z J = 1 := by
  have e := hp.2 Z 1 1 (pushPt hp.1.w 1) (pushPt hp.1.w 1) rfl rfl
  rw [_root_.mul_one] at e
  have h1 : pushPt hp.1.w (1 : Z ⟶ H') = 1 :=
    left_eq_mul.1 (Over.OverMorphism.ext (f := pushPt hp.1.w 1) e.symm)
  have h2 := h (Over.mk (Z.hom ≫ f)) z J hJ
  rw [← h1] at h2
  exact h2

theorem val_torus_pull {M : Type} [AddCommGroup M] {i : splitTorus S M ⟶ H} {i' : splitTorus S' M ⟶ H'}
    (hi : TorusCompat f F i' i) (χ : M)
    (h : ∀ (Z : Over S) (z : Z.left) (J), Good L z J → ∀ (τ : Z ⟶ splitTorus S M) (a : Z ⟶ H),
      val t ((τ ≫ i) * a).left z J = gm τ.left z ⊤ (charUnit S M χ) * val t a.left z J)
    {Z : Over S'} {z : Z.left} {J} (hJ : Good L z J) (τ : Z ⟶ splitTorus S' M) (a : Z ⟶ H') :
    val t (((τ ≫ i') * a).left ≫ F) z J = gm τ.left z ⊤ (charUnit S' M χ) * val t (a.left ≫ F) z J := by
  obtain ⟨β, hβ, hχ, hβi⟩ := hi
  have e := hp.2 Z (τ ≫ i') a (pushPt hβ τ ≫ i) (pushPt hp.1.w a)
    ((Category.assoc _ _ _).trans ((congrArg (τ.left ≫ ·) hβi).trans (Category.assoc _ _ _).symm)) rfl
  have h2 := h (Over.mk (Z.hom ≫ f)) z J hJ (pushPt hβ τ) (pushPt hp.1.w a)
  exact (congrArg (fun r => val t r z J) e).symm.trans
    (h2.trans (congrArg₂ (· * ·) (gm_char_comp β χ (hχ χ) τ.left z) rfl))

end Abstract

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem isGrpPullback_trans {R : Type} [CommRing R] (I : Ideal R) (e : ℕ) (G : Over (Spec (CommRingCat.of R)))
    [GrpObj G] :
    IsGrpPullback (thickObj R I e G) (thickObj R I (e + 1) G) (thickTrans R I e) (thickMap R I e G) :=
  (isGrpPullback_pullback G (thick R I (e + 1))).cancel
    ((isGrpPullback_pullback G (thick R I e)).congr (thickTrans_comp R I e).symm
      ((pullback.lift_fst _ _ _).trans (Category.comp_id _)).symm) (pullback.lift_snd _ _ _)

end CoordReduction


open CoordReduction in
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem gtCoord_compat_of_torusCompat : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (g' : GtCoord I D (e + 1) G), thickMap R I e G ≫ g'.pG.left = g.pG.left → TorusCompat (thickTrans R I e) (thickMap R I e G) g.i g'.i → ∀ χ, LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (g'.t χ) (thickMap R I e G)) (g.t χ) := by
  intro hG R _ _ I D e G _ _ g g' hq hi χ
  obtain ⟨ρ, hρ⟩ := exists_ratio D.P.isLB (LevelCompat.thickMap_Oφ g g' hq χ)
    (DVR.pullGen_isGen _ _ _ _ (g'.t_gen χ) (thickMap R I e G)) (g.t_gen χ)
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J), Good D.P.L z J →
      val (g'.t χ) (r ≫ thickMap R I e G) z J = gm r z ⊤ ρ * val (g.t χ) r z J := fun Z r z J hJ =>
    (val_pull hJ _ _ _).symm.trans (hρ Z r z J hJ)
  have := g.q_flat
  have := g.q_surj
  have := g.q_affine
  have h1 : ρ.val = 1 := by
    refine eq_one_of_fibre_const_of_section hG _ _ _ (TLinPf.isAb_pullback _ _ D.P.isAb) g.q _
      (1 : 𝟙_ _ ⟶ thickObj R I e G) (fun Z a b hab => ?_) ?_
    · obtain ⟨τ, hτ⟩ := TorusCoord.exists_torus g a b hab
      refine TorusCoord.appTop_eq_of_gm _ _ ρ fun z => ?_
      obtain ⟨J, hJ⟩ := exists_good_pt D.P.isLB z
      have k := key _ a.left z J hJ
      have t₁ := val_torus_pull (isGrpPullback_trans I e G) (g'.t χ) hi χ
        (fun _ _ _ hJ τ a => TorusCoord.val_torus g' χ hJ τ a) hJ τ b
      have t₂ := TorusCoord.val_torus g χ hJ τ b
      rw [← hτ] at t₁ t₂
      rw [t₁, t₂, key _ b.left z J hJ, mul_left_comm, ← _root_.mul_assoc, ← _root_.mul_assoc] at k
      exact (mul_right_cancel (mul_right_cancel k)).symm
    · have h : Units.map (1 : 𝟙_ _ ⟶ thickObj R I e G).left.appTop.hom.toMonoidHom ρ = 1 := by
        refine unit_ext fun z _ => ?_
        obtain ⟨J, hJ⟩ := exists_good_pt D.P.isLB z
        have k := key _ (1 : 𝟙_ _ ⟶ thickObj R I e G).left z J hJ
        rw [val_unit_pull (isGrpPullback_trans I e G) (g'.t χ) (fun _ _ _ hJ => TorusCoord.val_unit g' χ hJ) hJ,
          TorusCoord.val_unit g χ hJ, _root_.mul_one] at k
        exact (gm_top _ z ρ).symm.trans (k.symm.trans (map_one _).symm)
      exact congrArg Units.val h
  have h2 : ρ = 1 := Units.ext h1
  refine corr_of_val D.P.isLB fun y J hJ => ?_
  rw [hρ _ _ y J hJ, h2, map_one, _root_.one_mul]

end GlobalTheory
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UU
variable {S : Scheme.{0}}

theorem isWt_of_gm {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X] {i : splitTorus S X ⟶ G} {V : G.left.Opens}
    (u : Γ(G.left, V)ˣ) (χ : X)
    (h : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (z : Z.left), g.left z ∈ V →
      gm ((t ≫ i) * g).left z V u = gm t.left z ⊤ (charUnit S X χ) * gm g.left z V u) :
    IsWt i V u.val χ := by
  intro Z t g h₁ h₂
  apply TopCat.Presheaf.section_ext Z.left.sheaf ⊤
  intro z hz
  have hg : g.left z ∈ V := h₂ trivial
  have hf : ((t ≫ i) * g).left z ∈ V := h₁ trivial
  have ht : t.left z ∈ (⊤ : (splitTorus S X).left.Opens) := trivial
  have key := congrArg Units.val (h Z t g z hg)
  simp only [gm, dif_pos hg, dif_pos hf, dif_pos ht, pullU, MonoidHom.comp_apply, Units.coe_map,
    Units.val_mul] at key
  change Z.left.presheaf.germ ⊤ z hz _ = Z.left.presheaf.germ ⊤ z hz _
  simp only [Scheme.Hom.appLE, CommRingCat.comp_apply, map_mul, TopCat.Presheaf.germ_res_apply]
  exact key

attribute [local instance] SplitExt.free SplitExt.finite

variable {E : SplitExt S} {G : Over S} [GrpObj G]

theorem exists_mem_commonChart (E : SplitExt S) (x : E.B.left) : ∃ j, x ∈ E.chart j := by
  have hk : ∀ k, ∃ a, x ∈ (E.O (E.basis k)).L.U a := by
    intro k
    have hx : x ∈ (⊤ : E.B.left.Opens) := trivial
    rw [← (E.O (E.basis k)).isLB.cover] at hx
    simpa [TopologicalSpace.Opens.mem_iSup] using hx
  choose c hc using hk
  refine ⟨c, ?_⟩
  unfold SplitExt.chart
  rw [← SetLike.mem_coe, TopologicalSpace.Opens.coe_iInf]
  exact Set.mem_iInter.2 hc

private theorem gm_res_pullU_eq_gm_comp {Z P Y : Scheme.{0}} (p : Z ⟶ P) (a : P ⟶ Y) {U : Y.Opens} {W : P.Opens}
    (h : W ≤ a ⁻¹ᵁ U) {z : Z} (hz : p z ∈ W) (w : Γ(Y, U)ˣ) :
    gm p z W (res h (pullU a U w)) = gm (p ≫ a) z U w := by
  have hz' : (p ≫ a) z ∈ U := h hz
  ext
  simp only [gm, dif_pos hz, dif_pos hz', pullU, res, MonoidHom.comp_apply, Units.coe_map]
  erw [← Scheme.Hom.germ_stalkMap_apply p W z hz, TopCat.Presheaf.germ_res_apply,
    Scheme.Hom.germ_stalkMap_apply]
  rfl

private theorem gm_id_pullU_eq_gm {Z P Y : Scheme.{0}} (p : Z ⟶ P) (a : P ⟶ Y) {U : Y.Opens} {z : Z}
    (hz : p z ∈ a ⁻¹ᵁ U) (w : Γ(Y, U)ˣ) :
    gm p z (a ⁻¹ᵁ U) (pullU a U w) = gm (p ≫ a) z U w := by
  have hz' : (p ≫ a) z ∈ U := hz
  ext
  simp only [gm, dif_pos hz, dif_pos hz', pullU, MonoidHom.comp_apply, Units.coe_map]
  rfl

theorem isWt_coordinate (d : E.GtDatum G) (j : E.ChartIdx) (k : Module.Free.ChooseBasisIndex ℤ E.X) :
    IsWt d.i _ (d.u j k).val (E.basis k) := by
  refine isWt_of_gm (d.u j k) (E.basis k) ?_
  intro Z t g z hz
  have hf : (t ≫ d.i) * g = lift t g ≫ (lift (fst (splitTorus S E.X) G ≫ d.i) (snd (splitTorus S E.X) G) ≫ μ) := by
    show lift (t ≫ d.i) g ≫ μ = _
    rw [← Category.assoc, comp_lift, lift_fst_assoc, lift_snd]
  have hp : (lift t g).left z ∈ (snd (splitTorus S E.X) G).left ⁻¹ᵁ (d.q.left ⁻¹ᵁ E.chart j) := by
    have e : ((lift t g).left ≫ (snd (splitTorus S E.X) G).left) = g.left := by
      rw [← Over.comp_left, lift_snd]
    show ((lift t g).left ≫ (snd (splitTorus S E.X) G).left) z ∈ d.q.left ⁻¹ᵁ E.chart j
    rw [e]
    exact hz
  have key := congrArg (gm (lift t g).left z _) (d.equiv j k)
  rw [map_mul] at key
  rw [gm_res_pullU_eq_gm_comp (a := (lift (fst (splitTorus S E.X) G ≫ d.i) (snd (splitTorus S E.X) G) ≫ μ).left) _ _ hp,
    gm_id_pullU_eq_gm (a := (snd (splitTorus S E.X) G).left) _ hp] at key
  rw [← Over.comp_left, ← Over.comp_left, lift_snd, ← hf] at key
  rw [key]
  congr 1
  erw [gm_res_pullU_eq_gm_comp (a := (fst (splitTorus S E.X) G).left) _ _ hp]
  rw [← Over.comp_left, lift_fst]

theorem exists_unit_isWt (d : E.GtDatum G) (j : E.ChartIdx) (χ : E.X) :
    ∃ u : Γ(G.left, d.q.left ⁻¹ᵁ E.chart j)ˣ, IsWt d.i _ u.val χ := by
  have hχ : χ ∈ AddSubgroup.closure (Set.range E.basis) := by
    rw [← Submodule.span_int_eq_addSubgroupClosure, Submodule.mem_toAddSubgroup, E.basis.span_eq]
    exact Submodule.mem_top
  induction hχ using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    exact ⟨d.u j k, isWt_coordinate d j k⟩
  | zero => exact ⟨1, by simpa using (isWt_one : IsWt d.i (d.q.left ⁻¹ᵁ E.chart j) 1 0)⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a * b, by simpa using ha.mul hb⟩
  | neg x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨a⁻¹, ha.inv⟩

def TQ.ofGtDatum (d : E.GtDatum G) : TQ G E.X where
  B := E.B
  comm := E.isAbelian.comm
  isAb := E.isAbelian
  q := d.q
  i := d.i
  q_hom := d.q_hom
  i_hom := d.i_hom
  q_flat := d.q_flat
  q_surj := d.q_surjective
  q_affine := d.q_affine
  isKernel := d.isKernel
  loc b χ := by
    obtain ⟨j, hj⟩ := exists_mem_commonChart E b
    exact ⟨E.chart j, hj, exists_unit_isWt d j χ⟩

theorem exists_tq_of_gtDatum :
    ∀ (S : Scheme.{0}) (E : SplitExt S) (G : Over S) [GrpObj G] (Dat : E.GtDatum G), ∃ Q : TQ G E.X, Q.i = Dat.i := by
  intro S E G _ Dat
  exact ⟨TQ.ofGtDatum Dat, rfl⟩

end GlobalTheory.UU
end
end

section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU GlobalTheory.IndefiniteRowSideFullHecke.CanonicalRigidImages

namespace GlobalTheory.GtCoordCompare

section Calc

variable {Y W W' Z : Scheme.{0}} {L : LB Y} {K : Type} [Fintype K] {ψ : K → (W ⟶ Y)} {ψ' : K → (W' ⟶ Y)}
  {ε ε' : K → ℤ} {r : Z ⟶ W} {r' : Z ⟶ W'}

end Calc

section Image

variable {Y G B : Scheme.{0}} {L : LB Y} {K : Type} [Fintype K] (q : G ⟶ B) {φ : K → (B ⟶ Y)} {φ' : K → (G ⟶ Y)}
  {ε ε' : K → ℤ}

variable {q} {x : LB.Gen (LB.LinComb L φ' ε')} {V : B.Opens}


end Image

section Group

variable {S Y : Scheme.{0}} {X : Type} [AddCommGroup X] {G B : Over S} [GrpObj G] [GrpObj B] {q : G ⟶ B}
  {i : splitTorus S X ⟶ G} {L : LB Y} {K : Type} [Fintype K] {ε ε' : K → ℤ}

def WtGen (i : splitTorus S X ⟶ G) {φ' : K → (G.left ⟶ Y)} (x : LB.Gen (LB.LinComb L φ' ε')) (χ : X) : Prop :=
  ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (z : Z.left) (J), Good L z J →
    val x ((t ≫ i) * g).left z J = gm t.left z ⊤ (charUnit S X χ) * val x g.left z J

theorem act_comp [IsMonHom q] (hi : i ≫ q = toUnit _ ≫ η[B]) {Z : Over S} (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) :
    ((t ≫ i) * g).left ≫ q.left = g.left ≫ q.left := by
  have e : ((t ≫ i) * g) ≫ q = g ≫ q := by
    rw [MonObj.mul_comp, Category.assoc, hi, ← Category.assoc, comp_toUnit, ← Hom.one_def, _root_.one_mul]
  exact congrArg (fun f => f.left) e

theorem isWt_of_gs {V : G.left.Opens} {a : Γ(G.left, V)} {χ : X}
    (h : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G), ⊤ ≤ g.left ⁻¹ᵁ V → ∀ z : Z.left,
      gs ((t ≫ i) * g).left z V a = (gm t.left z ⊤ (charUnit S X χ)).val * gs g.left z V a) : IsWt i V a χ :=
  fun Z t g h₁ h₂ => fn_ext fun z hz => by
    rw [gs_mul _ z _ hz, gs_appLE _ _ _ _ _ z hz, gs_appLE _ _ _ _ _ z hz, Category.id_comp, Category.id_comp,
      h Z t g h₂ z]
    congr 1
    refine ((gs_pull (𝟙 _) t.left z ⊤ trivial _).trans ?_).symm
    rw [Category.id_comp, gs_unit _ z ⊤ trivial]

section One

variable [IsMonHom q] (hi : i ≫ q = toUnit _ ≫ η[B]) (hL : L.IsLB) {φ : K → (B.left ⟶ Y)} {φ' : K → (G.left ⟶ Y)}
  (hφ : ∀ k, φ' k = q.left ≫ φ k) {x : LB.Gen (LB.LinComb L φ' ε')} (hx : x.IsGen) {χ : X} (hw : WtGen i x χ)
include hi hL hφ hx hw


end One

section All

variable [IsMonHom q] [IsMonHom i] [IsAffineHom q.left] (hL : L.IsLB) (hε : ∀ k, ε' k = -ε k)
  {φ : X → K → (B.left ⟶ Y)} {φ' : X → K → (G.left ⟶ Y)} (hφ : ∀ χ k, φ' χ k = q.left ≫ φ χ k)
  {x : ∀ χ, LB.Gen (LB.LinComb L (φ' χ) ε')} (hx : ∀ χ, (x χ).IsGen) (hw : ∀ χ, WtGen i (x χ) χ)
include hL hε hφ hx hw


end All

end Group

end GlobalTheory.GtCoordCompare
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem TQ.smooth_proj_of_free {S : Scheme.{0}} {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    {G : Over S} [GrpObj G] (Q : TQ G X) : Smooth Q.q.left := by
  have := Q.q_hom
  have := Q.q_flat
  have := Q.q_surj
  have := Q.q_affine
  have := (H1.torus_dim S X).smooth
  refine MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    ((H1.torsor_pullback Q.i Q.q Q.isKernel).map (Over.forget _)).flip
    ⟨⟨‹_›, ‹_›⟩, inferInstanceAs (QuasiCompact Q.q.left)⟩ ?_
  exact smooth_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) this

theorem TQ.dim_eq_add_finrank :
    (∀ (S : Scheme.{0}) [Nonempty S] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over S) [GrpObj G] (Q : TQ G X) (g g' : ℕ), SmoothOfRelativeDimension g G.hom → SmoothOfRelativeDimension g' Q.B.hom → g = g' + Module.finrank ℤ X) := by
  intro S hS X _ _ _ G _ Q g g' dG dB
  obtain ⟨y⟩ := hS
  have := Q.i_hom
  have := Q.smooth_proj_of_free
  obtain ⟨m, W, hW, d₁⟩ := H1.exists_dim Q.q.left (eSec G y)
  have g₂ : m = Module.finrank ℤ X := H1.dim_base (Q.isKernel.map (Over.forget _)) d₁ (H1.torus_dim S X) (eSec _ y)
    ((congrArg (fun k => k.left y ∈ W) (IsMonHom.one_hom Q.i)).mpr hW)
  have d₂ : SmoothOfRelativeDimension (m + g') (W.ι ≫ G.hom) := by
    rw [← Over.w Q.q, ← Category.assoc]; infer_instance
  have d₃ : SmoothOfRelativeDimension (0 + g) (W.ι ≫ G.hom) := inferInstance
  have := H1.dim_unique _ d₂ d₃ ⟨_, hW⟩
  omega

end GlobalTheory.UU
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem exists_cp_pull : (∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (G' : Over S') [GrpObj G'] [IsCommMonObj G'] (F : G'.left ⟶ G.left) (hw : F ≫ G.hom = G'.hom ≫ f), (∀ (T : Over S') (x y : T ⟶ G'), toBase hw (x * y) = toBase hw x * toBase hw y) → ∀ P : CP G, ∃ (P' : CP G') (w : _), P'.L.L = P.L.L.pull F ∧ IsCPMap P' P f F hw w) := by
  intro S S' f G _ _ G' _ _ F hw mul P
  obtain ⟨_, _, _, _, _, _, _, h⟩ :=
    exists_isCPMap P mul _ (pull_isLB P.L.isLB F) _ (pullIso_isGen P.L.isLB F)
  exact ⟨_, _, rfl, h⟩

end GlobalTheory.UU
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.GoodReductionUnif

theorem exists_baseChange (hB : PolBaseChangeSt) {S S' : Scheme.{0}} (f : S' ⟶ S) (P : PolAV S) :
    ∃ (A : PolAV S') (eA : (Over.pullback f).obj P.A ≅ A.A), IsMonHom eA.hom ∧
      ∃ w : LB.Iso (A.L.pull eA.hom.left) (P.L.pull (pullback.fst P.A.hom f)), w.IsGen := by
  obtain ⟨A, g, hg, -, mul, t, ht⟩ := hB S S' f P
  let eA : (Over.pullback f).obj P.A ≅ A.A := Over.isoMk hg.isoPullback.symm hg.isoPullback_inv_snd
  have he : eA.hom.left ≫ g = pullback.fst P.A.hom f := hg.isoPullback_inv_fst
  refine ⟨A, eA, isMonHom_of_mul _ fun T x y => Over.OverMorphism.ext (hg.hom_ext ?_ ?_), ?_⟩
  · have tb : ∀ a : T ⟶ (Over.pullback f).obj P.A, toBase hg.w (a ≫ eA.hom) =
        toBase (A := P.A) (A' := (Over.pullback f).obj P.A) (g := pullback.fst P.A.hom f) pullback.condition a :=
      fun a => Over.OverMorphism.ext ((Category.assoc _ _ _).trans (congrArg (a.left ≫ ·) he))
    have e : toBase hg.w ((x * y) ≫ eA.hom) = toBase hg.w ((x ≫ eA.hom) * (y ≫ eA.hom)) := by
      rw [mul, tb, tb, tb, toBase_mul_pullback]
    exact congrArg CommaMorphism.left e
  · exact (Over.w _).trans (Over.w _).symm
  · obtain ⟨t', ht', -⟩ := GenericSectionBasis.exists_inv_iso t ht
    have h₁ := (isGen_iff t').1 ht'
    have h₂ := (isGen_iff _).1 (pullIso_isGen A.isLB eA.hom.left)
    obtain ⟨w, Tw⟩ := Geo.Tor.exists_comp A.isLB t' (pullIso A.L eA.hom.left) h₁ h₂ P.isLB
      (pull_isLB A.isLB _)
    rw [← he]
    exact ⟨w, (isGen_iff w).2 (Tw.pgen_comp A.isLB h₁ h₂)⟩


end GlobalTheory.GoodReductionUnif

end
end
