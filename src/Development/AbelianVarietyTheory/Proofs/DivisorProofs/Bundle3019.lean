module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle065
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2791
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2919
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2787
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2792
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle070
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
import Development.AbelianVarietyTheory.Definitions.Divisors.SecondCountableTopologyOfIsProjOver
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EndoLbIsoSymmetryHypothesisExtendNormalModel
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle030
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2886
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCubicalRigidifiedExtension
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2412
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.Tactic.Polynomial.Basic
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8

noncomputable section

namespace GlobalTheory.Poinc.Eq8.Chars8

theorem prod_comp {S : Scheme.{0}} {T G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H]
    (g : G ⟶ H) [IsMonHom g] {κ : Type} (s : Finset κ) (f : κ → (T ⟶ G)) :
    (∏ i ∈ s, f i) ≫ g = ∏ i ∈ s, (f i ≫ g) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, MonObj.one_comp]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, MonObj.mul_comp, ih]

theorem main : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (A₀ : PolAV (Sp (FractionRing V₁))) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G₀ → ∀ (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (D : DegData V₁ (maximalIdeal V₁)) (P : PolAV (Sp (FractionRing V₁))) (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V₁) D P G) (q : Fin 8 → (G ⟶ G₀)), (∀ u, IsMonHom (q u)) → (∀ (T' : Over (Sp V₁)) (y' : Fin 8 → (T' ⟶ G₀)), ∃! x : T' ⟶ G, ∀ u, x ≫ q u = y' u) → ∃ c : Fin 8 → (D₀.toPre.X →+ D.toPre.X), (∀ u, TorMatch U₀ U (RingHom.id V₁) (q u).left (c u)) ∧ Function.Bijective (fun χ : Fin 8 → D₀.toPre.X => ∑ u, c u (χ u)) := by
  intro V₁ _ _ _ hCN D₀ A₀ G₀ _ _ hG₀ U₀ D P G _ _ hG U q hq huniv
  have hB : GlobalTheory.Mum.Base V₁ := ⟨⟨hCN.1, inferInstance, hCN.2.1, hCN.2.2.1⟩, hCN.2.2.2⟩
  choose c hc using fun u => GlobalTheory.Poinc.HomTor.exists_torMatch V₁ hB G₀ hG₀ D₀ A₀ U₀ G hG D P U (q u) (hq u)

  let y : Fin 8 → Fin 8 → (G₀ ⟶ G₀) := fun u v => if v = u then 𝟙 G₀ else 1
  choose sc hsc _ using fun u => huniv G₀ (y u)
  have hscm : ∀ u, IsMonHom (sc u) := fun u => isMonHom_of_mul _ fun T a b => by
    refine (huniv T (fun v => (a * b) ≫ y u v)).unique (fun v => ?_) (fun v => ?_)
    · rw [Category.assoc, hsc]
    · haveI := hq v
      rw [MonObj.mul_comp, Category.assoc, Category.assoc, hsc]
      by_cases h : v = u
      · simp only [y, h, if_true, Category.comp_id]
      · simp only [y, h, if_false, comp_one, _root_.mul_one]
  choose d hd using fun u => GlobalTheory.Poinc.HomTor.exists_torMatch V₁ hB G hG D P U G₀ hG₀ D₀ A₀ U₀ (sc u) (hscm u)
  obtain ⟨hid₀, hone₀, -⟩ := torMatch_id_one_mul V₁ hB G₀ hG₀ D₀ A₀ U₀ G₀ hG₀ D₀ A₀ U₀
  obtain ⟨hid, hone, hmul⟩ := torMatch_id_one_mul V₁ hB G hG D P U G hG D P U

  have dc : ∀ u v, (d u).comp (c v) = if v = u then AddMonoidHom.id _ else 0 := by
    intro u v
    have h := torMatch_comp V₁ hB G₀ hG₀ D₀ A₀ U₀ V₁ hB G hG D P U (RingHom.id V₁) (q v).left V₁ hB G₀ hG₀ D₀ A₀ U₀
      (RingHom.id V₁) (sc u).left Function.injective_id (fun k hk => hk) (c v) (d u) (hc v) (hd u)
    rw [RingHom.id_comp, ← Over.comp_left, hsc] at h
    by_cases huv : v = u
    · simp only [y, huv, if_true, Over.id_left] at h ⊢
      exact torMatch_unique V₁ hB G₀ hG₀ D₀ A₀ U₀ V₁ hB G₀ hG₀ D₀ A₀ U₀ (RingHom.id V₁) _ Function.injective_id _ _ h hid₀
    · simp only [y, huv, if_false] at h ⊢
      exact torMatch_unique V₁ hB G₀ hG₀ D₀ A₀ U₀ V₁ hB G₀ hG₀ D₀ A₀ U₀ (RingHom.id V₁) _ Function.injective_id _ _ h hone₀
  have dsum : ∀ (χ : Fin 8 → D₀.toPre.X) w, d w (∑ u, c u (χ u)) = χ w := by
    intro χ w

    rw [map_sum, Finset.sum_eq_single w]
    · have := DFunLike.congr_fun (dc w w) (χ w)
      simpa using this
    · intro b _ hb
      have := DFunLike.congr_fun (dc w b) (χ b)
      simpa [hb] using this
    · intro h; exact absurd (Finset.mem_univ w) h

  have hprod : (∏ v, q v ≫ sc v) = 𝟙 G := by
    refine (huniv G q).unique (fun w => ?_) (fun w => Category.id_comp _)
    haveI := hq w
    rw [prod_comp, Finset.prod_eq_single w]
    · rw [Category.assoc, hsc]; simp only [y, if_true, Category.comp_id]
    · intro b _ hb
      rw [Category.assoc, hsc]
      simp only [y, Ne.symm hb, if_false, comp_one]
    · intro h; exact absurd (Finset.mem_univ w) h
  have hs : ∀ s : Finset (Fin 8), TorMatch U U (RingHom.id V₁) (∏ v ∈ s, q v ≫ sc v).left
      (∑ v ∈ s, (c v).comp (d v)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => rw [Finset.prod_empty, Finset.sum_empty]; exact hone
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      refine hmul _ _ _ _ ?_ ih
      have h := torMatch_comp V₁ hB G hG D P U V₁ hB G₀ hG₀ D₀ A₀ U₀ (RingHom.id V₁) (sc a).left V₁ hB G hG D P U
        (RingHom.id V₁) (q a).left Function.injective_id (fun k hk => hk) (d a) (c a) (hd a) (hc a)
      rwa [RingHom.id_comp, ← Over.comp_left] at h
  have hsum : (∑ v, (c v).comp (d v)) = AddMonoidHom.id _ := by
    have h := hs Finset.univ
    rw [hprod, Over.id_left] at h
    exact torMatch_unique V₁ hB G hG D P U V₁ hB G hG D P U (RingHom.id V₁) _ Function.injective_id _ _ h hid
  refine ⟨c, hc, fun χ χ' h => funext fun w => ?_, fun z => ⟨fun v => d v z, ?_⟩⟩
  · rw [← dsum χ w, ← dsum χ' w]; exact congrArg (d w) h
  · have := DFunLike.congr_fun hsum z
    rw [AddMonoidHom.finsetSum_apply] at this
    simpa using this

end GlobalTheory.Poinc.Eq8.Chars8

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PrimExt

theorem refl_of_isLB {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) : LBIso L L := by
  refine ⟨⟨fun p => L.g p.1 p.2⟩, fun p q => unit_ext fun y hy => ?_⟩
  refine (gm_res _ y _ hy _).trans (Eq.symm ((map_mul _ _ _).trans ((congrArg₂ (· * ·)
    (gm_div L L (𝟙 X) y p q hy) (gm_res _ y _ hy _)).trans ?_)))
  have a := gm_cocycle hL (𝟙 X) y hy.1.1 hy.2.1 hy.2.2
  have b := gm_cocycle hL (𝟙 X) y hy.1.1 hy.1.2 hy.2.2
  show gm (𝟙 X) y _ (L.g p.1 q.1) * (gm (𝟙 X) y _ (L.g p.2 q.2))⁻¹ * gm (𝟙 X) y _ (L.g q.1 q.2) =
    gm (𝟙 X) y _ (L.g p.1 p.2)
  rw [mul_right_comm, a, ← b, mul_inv_cancel_right]

theorem lbIso_pull_of_range_subset {X Y Y' : Scheme.{0}} (e : Y ⟶ X) [IsOpenImmersion e] (f : Y' ⟶ X)
    (hf : Set.range f.base ⊆ Set.range e.base) (L M : LB X) (h : LBIso (L.pull e) (M.pull e)) :
    LBIso (L.pull f) (M.pull f) := by
  have hc : f = IsOpenImmersion.lift e f hf ≫ e := (IsOpenImmersion.lift_fac e f hf).symm
  exact LBIso.chartPull (chartPullSame L _ _ _ _ fun _ => hc) (chartPullSame M _ _ _ _ fun _ => hc) h

theorem prim_pull {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    (tF : SAB H S') (G : Over S) [GrpObj G] [IsCommMonObj G] (j : S' ⟶ S) (e : tF.G.left ⟶ G.left)
    (he : IsGrpPullback tF.G G j e) (act : OAct (𝓞 E) G)
    (hact : ∀ a, (tF.act.act a).left ≫ e = e ≫ (act.act a).left) (PP : RigLB G)
    (hw : LBIso tF.PP.L (PP.L.pull e)) :
    LBIso (PP.L.pull e) ((cubeLB G ![𝟙 G, act.act H.w0] PP.L).pull e) := by
  have hP : (PP.L.pull e).IsLB := pull_isLB PP.isLB e
  have hC : (cubeLB G ![𝟙 G, act.act H.w0] PP.L).IsLB := GlobalTheory.SabPullCompare.cubeLB_isLB _ PP.isLB
  let U := pushPt he.1.w (𝟙 tF.G)
  have hU : U.left = e := by simp [U, pushPt]
  have hc : ∀ I : ULift.{0} (Finset (Fin 2)),
      (psum tF.G ![𝟙 tF.G, tF.act.act H.w0] I.down).left ≫ e = e ≫ (psum G ![𝟙 G, act.act H.w0] I.down).left :=
    fun I => (psum_push he ![𝟙 tF.G, tF.act.act H.w0] ![𝟙 G, act.act H.w0] U (fun i => by
      fin_cases i
      · apply Over.OverMorphism.ext
        simp [U, pushPt]
      · apply Over.OverMorphism.ext
        simp [U, pushPt, hact]) I.down).trans (by rw [hU])
  have h4 : LBIso (cubeLB tF.G ![𝟙 tF.G, tF.act.act H.w0] (PP.L.pull e))
      ((cubeLB G ![𝟙 G, act.act H.w0] PP.L).pull e) :=
    LBIso.chartPull (chartPullLinComb PP.L e _ _ _ e hc) (chartPullPull _ e) (refl_of_isLB hC)
  refine LBIso.trans hP tF.PP.isLB (pull_isLB hC e) hw.symm ?_
  refine LBIso.trans tF.PP.isLB (GlobalTheory.SabPullCompare.cubeLB_isLB _ tF.PP.isLB) (pull_isLB hC e) tF.prim ?_
  exact LBIso.trans (GlobalTheory.SabPullCompare.cubeLB_isLB _ tF.PP.isLB) (GlobalTheory.SabPullCompare.cubeLB_isLB _ hP)
    (pull_isLB hC e) (GlobalTheory.SabPullCompare.lbIso_cubeLB _ hw) h4

theorem lbIso_prim_ext : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → ∀ (tF : SAB H (Xo.XF c)), SABMap tF Xo.univ.t (pullback.fst _ _) → ∀ (G : Over S) [GrpObj G] [IsCommMonObj G] (e : tF.G.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback tF.G G j e → (∀ {k : Type} [Field k] {m n : ℕ} (C : MonoFam Xo c φ (ChartRing k m n)), IsTaut C → ∀ ξ : Sp (ChartRing k m n) ⟶ S, C.y ≫ j = jK _ ≫ ξ → ∀ (tK : SAB H (Sp (FractionRing (ChartRing k m n)))) (a : SABMap tK C.t (jK _)) (b : SABMap tK tF C.y), ∃ πC : C.t.G.left ⟶ G.left, IsGrpPullback C.t.G G ξ πC ∧ a.φ ≫ πC = b.φ ≫ e) → ∀ (act : OAct (𝓞 E) G), (∀ a, (tF.act.act a).left ≫ e = e ≫ (act.act a).left) → ∀ (PP : RigLB G) (cub : CubicalStr G PP) (cm : CubeMap tF.G G), cm.F = e → cm.e = j → cm.IsPullCubical tF.cub cub → LBIso PP.L (cubeLB G ![𝟙 G, act.act H.w0] PP.L) := by
  intro E _ _ _ H Dw l Xo c φ _ _ _ Z zs i OZ N d J S π j _ BD hUP _ tF _ G _ _ e hG he _ act hact PP cub cm hF _ hlin
  obtain ⟨-, -, -, -, ⟨⟨hS, -⟩, hproj, -, hdense, -⟩, -⟩ := hUP
  have : IsLocallyNoetherian S := by
    obtain ⟨N', im, _, h⟩ := hproj
    have : LocallyOfFiniteType (π ≫ zs) := h ▸ inferInstance
    exact LocallyOfFiniteType.isLocallyNoetherian (π ≫ zs)
  have hS' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S := by haveI := hS; exact GlobalTheory.IsNormalScheme.pred S
  have hw : LBIso tF.PP.L (PP.L.pull e) := by
    obtain ⟨w, hw, -⟩ := hlin
    exact hF ▸ ⟨w, hw⟩
  have : IsOpenImmersion e := MorphismProperty.of_isPullback he.1.flip inferInstance
  have hr : Set.range e.base = G.hom.base ⁻¹' Set.range j.base := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      show (e ≫ G.hom) y ∈ Set.range j
      rw [he.1.w]
      exact ⟨_, rfl⟩
    · intro hx
      have hx' : x ∈ Set.range (pullback.fst G.hom j) := by
        rw [Scheme.Pullback.range_fst]
        exact hx
      obtain ⟨z, rfl⟩ := hx'
      refine ⟨he.1.isoPullback.inv z, ?_⟩
      rw [← Scheme.Hom.comp_apply, he.1.isoPullback_inv_fst]
  haveI := act.hom H.w0
  haveI := hG.smooth
  haveI : GeometricallyIntegral G.hom := @GlobalTheory.geometricallyIntegral_of_isSemiAbelian _ G _ hG
  let V : S.Opens := j.opensRange
  haveI : IsDominant V.ι := ⟨by
    show Dense (Set.range V.ι)
    rw [Scheme.Opens.range_ι]
    simpa [V] using hdense⟩
  have hC : (cubeLB G ![𝟙 G, act.act H.w0] PP.L).IsLB := GlobalTheory.SabPullCompare.cubeLB_isLB _ PP.isLB
  have hsec : eSec G ≫ G.hom = 𝟙 S := Over.w η[G]
  have hrig : CechPic.pull (eSec G) (CechPic.cls PP.L PP.isLB) = 0 :=
    (CechPic.cls_eq_zero_iff (pull_isLB PP.isLB _)).2 ⟨PP.rig, PP.rigGen⟩
  refine (CechPic.cls_eq_iff PP.isLB hC).1 (GlobalTheory.ZH.EndoExtend.pic_ext V.ι hS' G (eSec G) hsec ?_ ?_)
  · rw [hrig, GlobalTheory.ZH.EndoExtend.cls_cubeLB G _ PP.isLB]
    have hp := GlobalTheory.ZH.EndoExtend.pull_cubeCls G ![𝟙 G, act.act H.w0]
      (fun _ : Fin 2 => (η[G] : 𝟙_ (Over S) ⟶ G)) η[G]
      (fun i => by
        fin_cases i
        · simp
        · simp [IsMonHom.one_hom]) (CechPic.cls PP.L PP.isLB)
    exact (GlobalTheory.ZH.EndoExtend.cubeCls_one G _ hrig).symm.trans hp.symm
  · refine (CechPic.cls_eq_iff (pull_isLB PP.isLB _) (pull_isLB hC _)).2 ?_
    refine lbIso_pull_of_range_subset e _ ?_ _ _ (prim_pull tF G j e he act hact PP hw)
    rw [Scheme.Pullback.range_fst, hr, Scheme.Opens.range_ι]
    rfl

end GlobalTheory.PrimExt
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ExtAdj

section Gen
variable {X Y B : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]

theorem exists_normalized {ψ : K → (Y ⟶ X)} {ε : K → ℤ} (p : Y ⟶ B) (e : B ⟶ Y) (he : e ≫ p = 𝟙 B)
    (s : LB.Gen (LB.LinComb L ψ ε)) (hs : s.IsGen) :
    ∃ s₂ : LB.Gen (LB.LinComb L (Sum.elim ψ (fun k => p ≫ e ≫ ψ k)) (Sum.elim ε (fun k => -ε k))),
      s₂.IsGen ∧ ∀ y J, Good L y J → val s₂ e y J = 1 := by
  refine ⟨LB.mulGen L _ _ _ _ s (LB.pullGen L _ _ (LB.invGen L _ _ (LB.pullGen L ψ ε s e)) p),
    DVR.mulGen_isGen _ _ _ _ _ _ _ hs (DVR.pullGen_isGen _ _ _ _ (DVR.invGen_isGen _ _ _ _
      (DVR.pullGen_isGen _ _ _ _ hs e)) p), fun y J hJ => ?_⟩
  rw [val_mul hJ, val_pull hJ, val_inv, val_pull hJ, he, Category.id_comp, mul_inv_cancel]

theorem formEq_sec {ψ : K → (Y ⟶ X)} {ε : K → ℤ} (p : Y ⟶ B) (e : B ⟶ Y) (he : e ≫ p = 𝟙 B) :
    FormEq (K := PEmpty) (PEmpty.elim : PEmpty → (B ⟶ X)) PEmpty.elim
      (fun k => e ≫ Sum.elim ψ (fun k => p ≫ e ≫ ψ k) k) (Sum.elim ε (fun k => -ε k)) := by
  intro U _ h
  rw [Fintype.prod_empty, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, ← Category.assoc, he, Category.id_comp, zpow_neg, Finset.prod_inv_distrib,
    mul_inv_cancel]
end Gen

section Cube
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {T : Over S}

def cφ (x : Fin 2 → (T ⟶ G)) : ULift.{0} (Finset (Fin 2)) → (T.left ⟶ G.left) := fun I => (psum G x I.down).left

def cε : ULift.{0} (Finset (Fin 2)) → ℤ := fun I => (-1) ^ (2 - I.down.card)

theorem cls_diff {L : LB G.left} (hL : L.IsLB) (x₁ x₂ : Fin 2 → (T ⟶ G))
    (h : (LB.LinComb L (Sum.elim (cφ x₁) (cφ x₂)) (Sum.elim cε (fun I => -cε I))).IsLB) :
    CechPic.cls _ h = CechPic.cls (LB.LinComb L (cφ x₁) cε) (LB.isLB_linComb hL _ _) -
      CechPic.cls (LB.LinComb L (cφ x₂) cε) (LB.isLB_linComb hL _ _) := by
  rw [CechPic.cls_linComb hL, CechPic.cls_linComb hL, CechPic.cls_linComb hL, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, neg_smul, Finset.sum_neg_distrib, sub_eq_add_neg]

theorem lbIso_of_gen {L : LB G.left} (hL : L.IsLB) (x₁ x₂ : Fin 2 → (T ⟶ G))
    (t : LB.Gen (LB.LinComb L (Sum.elim (cφ x₁) (cφ x₂)) (Sum.elim cε (fun I => -cε I)))) (ht : t.IsGen) :
    LBIso (cubeLB G x₁ L) (cubeLB G x₂ L) := by
  have z := (CechPic.cls_eq_zero_iff (LB.isLB_linComb hL _ _)).2 ⟨t, ht⟩
  rw [cls_diff hL x₁ x₂, sub_eq_zero] at z
  exact (CechPic.cls_eq_iff _ _).1 z

theorem gen_of_lbIso {L : LB G.left} (hL : L.IsLB) (x₁ x₂ : Fin 2 → (T ⟶ G))
    (H : LBIso (cubeLB G x₁ L) (cubeLB G x₂ L)) :
    ∃ t : LB.Gen (LB.LinComb L (Sum.elim (cφ x₁) (cφ x₂)) (Sum.elim cε (fun I => -cε I))), t.IsGen := by
  refine (CechPic.cls_eq_zero_iff (LB.isLB_linComb hL _ _)).1 ?_
  rw [cls_diff hL x₁ x₂, sub_eq_zero]
  exact (CechPic.cls_eq_iff (LB.isLB_linComb hL (cφ x₁) cε) (LB.isLB_linComb hL (cφ x₂) cε)).2 H

end Cube

section Origin
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

theorem eSec_cφ (x : Fin 2 → (G2 G ⟶ G)) (hx : ∀ i, η[G2 G] ≫ x i = 1) (I : ULift.{0} (Finset (Fin 2))) :
    eSec (G2 G) ≫ cφ x I = eSec G := by
  have h1 : η[G2 G] ≫ psum G x I.down = 1 := by
    have a := psum_hom (preHom (G := G) η[G2 G]) x I.down
    have b := psum_hom (1 : (𝟙_ (Over S) ⟶ G) →* (𝟙_ (Over S) ⟶ G)) (fun _ => 1) I.down
    simp only [MonoidHom.one_apply] at b
    exact a.trans ((congrArg (fun z => psum G z I.down) (funext hx)).trans b.symm)
  have h2 := congrArg (fun z => z.left) h1
  simp only [Over.comp_left] at h2
  refine h2.trans ?_
  simp [Hom.one_def, eSec]

theorem eSec_x2 (i : Fin 2) : η[G2 G] ≫ x2 G i = η[G] := by
  fin_cases i <;> simp [x2]

theorem one_cube₁ (f : G ⟶ G) [IsMonHom f] (i : Fin 2) : η[G2 G] ≫ (![fst G G ≫ f, snd G G] : Fin 2 → (G2 G ⟶ G)) i = 1 := by
  fin_cases i <;> simp [Hom.one_def]

theorem one_cube₂ (f : G ⟶ G) [IsMonHom f] (i : Fin 2) : η[G2 G] ≫ (![fst G G, snd G G ≫ f] : Fin 2 → (G2 G ⟶ G)) i = 1 := by
  fin_cases i <;> simp [Hom.one_def]
end Origin

section Push
variable {S U : Scheme.{0}} {j : U ⟶ S} {G : Over S} [GrpObj G] [IsCommMonObj G]
  {A : Over U} [GrpObj A] [IsCommMonObj A] {e : A.left ⟶ G.left}

abbrev jTwo (he : IsGrpPullback A G j e) : (G2 A).left ⟶ (G2 G).left :=
  (lift (pushPt he.1.w (fst A A)) (pushPt he.1.w (snd A A))).left

theorem doubleProductMapOfGrpPullback_comp_doubleCoordinate (he : IsGrpPullback A G j e) (i : Fin 2) : jTwo he ≫ (x2 G i).left = (x2 A i).left ≫ e := by
  fin_cases i
  · exact congrArg (fun z => z.left) (lift_fst (pushPt he.1.w (fst A A)) (pushPt he.1.w (snd A A)))
  · exact congrArg (fun z => z.left) (lift_snd (pushPt he.1.w (fst A A)) (pushPt he.1.w (snd A A)))

theorem eSec_jTwo (he : IsGrpPullback A G j e) : eSec (G2 A) ≫ jTwo he = j ≫ eSec (G2 G) := by
  refine GlobalTheory.Mum.PowCart.square_over_hom_ext _ fun i => ?_
  have a : eSec (G2 A) ≫ (x2 A i).left = eSec A := congrArg (fun z => Over.Hom.left z) (eSec_x2 (G := A) i)
  have b : eSec (G2 G) ≫ (x2 G i).left = eSec G := congrArg (fun z => Over.Hom.left z) (eSec_x2 (G := G) i)
  rw [Category.assoc, doubleProductMapOfGrpPullback_comp_doubleCoordinate, ← Category.assoc, a, Category.assoc, b]
  exact (cubeMapOf he).e_comm

theorem cφ_push (he : IsGrpPullback A G j e) (x' : Fin 2 → (G2 A ⟶ A)) (x : Fin 2 → (G2 G ⟶ G))
    (hx : ∀ i, (x' i).left ≫ e = jTwo he ≫ (x i).left) (I : ULift.{0} (Finset (Fin 2))) :
    cφ x' I ≫ e = jTwo he ≫ cφ x I :=
  psum_push he x' x (lift (pushPt he.1.w (fst A A)) (pushPt he.1.w (snd A A)))
    (fun i => Over.OverMorphism.ext (by rw [Over.comp_left]; exact hx i)) I.down
end Push

section Drop
variable {X Y B : Scheme.{0}} {K0 : Type} [Fintype K0]

theorem formEq_drop {ψ : K0 ⊕ K0 → (Y ⟶ X)} {ε₀ : K0 → ℤ} (p : Y ⟶ B) (e : B ⟶ Y) (z : B ⟶ X)
    (hz : ∀ k, e ≫ ψ k = z) :
    FormEq (Sum.elim ψ (fun k => p ≫ e ≫ ψ k))
      (Sum.elim (Sum.elim ε₀ (fun k => -ε₀ k)) (fun k => -(Sum.elim ε₀ (fun k => -ε₀ k)) k))
      ψ (Sum.elim ε₀ (fun k => -ε₀ k)) := by
  intro U _ h
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, hz, zpow_neg, neg_neg, inv_inv,
    Finset.prod_inv_distrib]
  group
end Drop

theorem adj_extends : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → ∀ (tF : SAB H (Xo.XF c)), SABMap tF Xo.univ.t (pullback.fst _ _) → ∀ (G : Over S) [GrpObj G] [IsCommMonObj G] (e : tF.G.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback tF.G G j e → (∀ {k : Type} [Field k] {m n : ℕ} (C : MonoFam Xo c φ (ChartRing k m n)), IsTaut C → ∀ ξ : Sp (ChartRing k m n) ⟶ S, C.y ≫ j = jK _ ≫ ξ → ∀ (tK : SAB H (Sp (FractionRing (ChartRing k m n)))) (a : SABMap tK C.t (jK _)) (b : SABMap tK tF C.y), ∃ πC : C.t.G.left ⟶ G.left, IsGrpPullback C.t.G G ξ πC ∧ a.φ ≫ πC = b.φ ≫ e) → ∀ (act : OAct (𝓞 E) G), (∀ a, (tF.act.act a).left ≫ e = e ≫ (act.act a).left) → ∀ (PP : RigLB G) (cub : CubicalStr G PP) (cm : CubeMap tF.G G), cm.F = e → cm.e = j → cm.IsPullCubical tF.cub cub → ∀ a, LBIso (cubeLB G ![fst G G ≫ act.act a, snd G G] PP.L) (cubeLB G ![fst G G, snd G G ≫ act.act (H.bar a)] PP.L) := by
  intro E _ _ _ H Dw l Xo c φ _ _ _ Z zs i OZ N d J S π j _ BD hU _ tF _ G _ _ e hsa he _ act hact PP cub cm hF _ hpc a
  obtain ⟨⟨-, -, -, -, -, -⟩, -, -, -, ⟨⟨hnorm, -⟩, hproj, -, hdense, -, -⟩, -⟩ := hU
  have := hsa.smooth
  have := hsa.geomConnected
  haveI : LocallyOfFiniteType (π ≫ zs) := by
    obtain ⟨M, i', hi', hcomp⟩ := hproj
    haveI := hi'
    haveI := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str c.F M
    rw [← hcomp]
    infer_instance
  haveI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian (π ≫ zs)
  haveI : IsDominant j := ⟨hdense⟩
  have hS : Geo.Tor.IsNormalScheme S := (GlobalTheory.isNormalScheme_iff_pred S).mp hnorm
  obtain ⟨w, hw, -, -⟩ := hpc
  have hw' := (isGen_iff w).1 hw
  haveI := act.hom a
  haveI := act.hom (H.bar a)
  haveI := tF.act.hom a
  haveI := tF.act.hom (H.bar a)
  let x₁ : Fin 2 → (G2 G ⟶ G) := ![fst G G ≫ act.act a, snd G G]
  let x₂ : Fin 2 → (G2 G ⟶ G) := ![fst G G, snd G G ≫ act.act (H.bar a)]
  let y₁ : Fin 2 → (G2 tF.G ⟶ tF.G) := ![fst tF.G tF.G ≫ tF.act.act a, snd tF.G tF.G]
  let y₂ : Fin 2 → (G2 tF.G ⟶ tF.G) := ![fst tF.G tF.G, snd tF.G tF.G ≫ tF.act.act (H.bar a)]
  let ψ := Sum.elim (cφ x₁) (cφ x₂)
  let ψ' := Sum.elim (cφ y₁) (cφ y₂)
  let ε₁ : ULift.{0} (Finset (Fin 2)) ⊕ ULift.{0} (Finset (Fin 2)) → ℤ := Sum.elim cε (fun I => -cε I)
  obtain ⟨s, hs⟩ := gen_of_lbIso tF.PP.isLB y₁ y₂ (tF.adj a)
  obtain ⟨s₂, hs₂, h1⟩ := exists_normalized (G2 tF.G).hom (eSec (G2 tF.G)) (CubeExtension.eSec_comp _) s hs
  have hsm := CubeExtension.smooth_tensor G G
  have hgc := CubeExtension.geometricallyConnected_tensor G G
  have hpb : IsPullback (jTwo he) (G2 tF.G).hom (G2 G).hom j := GlobalTheory.Mum.PowCart.isPullback_two he.1
  have f0 : jTwo he ≫ (fst G G).left = (fst tF.G tF.G).left ≫ e := doubleProductMapOfGrpPullback_comp_doubleCoordinate he 0
  have f1 : jTwo he ≫ (snd G G).left = (snd tF.G tF.G).left ≫ e := doubleProductMapOfGrpPullback_comp_doubleCoordinate he 1
  have hψ : ∀ k, ψ' k ≫ e = jTwo he ≫ ψ k := by
    rintro (I | I)
    · refine cφ_push he y₁ x₁ (fun i => ?_) I
      fin_cases i
      · show (fst tF.G tF.G ≫ tF.act.act a).left ≫ e = jTwo he ≫ (fst G G ≫ act.act a).left
        rw [Over.comp_left, Over.comp_left, Category.assoc, hact a, ← Category.assoc, ← f0, Category.assoc]
      · exact f1.symm
    · refine cφ_push he y₂ x₂ (fun i => ?_) I
      fin_cases i
      · exact f0.symm
      · show (snd tF.G tF.G ≫ tF.act.act (H.bar a)).left ≫ e = jTwo he ≫ (snd G G ≫ act.act (H.bar a)).left
        rw [Over.comp_left, Over.comp_left, Category.assoc, hact (H.bar a), ← Category.assoc, ← f1, Category.assoc]
  have hφ : ∀ k, Sum.elim ψ' (fun k => (G2 tF.G).hom ≫ eSec (G2 tF.G) ≫ ψ' k) k ≫ cm.F =
      jTwo he ≫ Sum.elim ψ (fun k => (G2 G).hom ≫ eSec (G2 G) ≫ ψ k) k := by
    rw [hF]
    rintro (k | k)
    · exact hψ k
    · simp only [Sum.elim_inr, Category.assoc]
      rw [hψ k, ← Category.assoc (eSec (G2 tF.G)), eSec_jTwo he, Category.assoc, ← Category.assoc (G2 tF.G).hom,
        ← hpb.w, Category.assoc]
  obtain ⟨c', hc', -⟩ := DenseCubeExt.exists_extension hS j (G2 G).hom (eSec (G2 G)) (jTwo he) (G2 tF.G).hom
    (eSec (G2 tF.G)) hsm hgc (CubeExtension.eSec_comp _) hpb (eSec_jTwo he) PP.isLB tF.PP.isLB hw'
    (Sum.elim ψ (fun k => (G2 G).hom ≫ eSec (G2 G) ≫ ψ k)) (Sum.elim ψ' (fun k => (G2 tF.G).hom ≫ eSec (G2 tF.G) ≫ ψ' k))
    (Sum.elim ε₁ (fun k => -ε₁ k)) hφ (formEq_sec _ _ (CubeExtension.eSec_comp _))
    (formEq_sec _ _ (CubeExtension.eSec_comp _)) s₂ hs₂ h1
  have hz : ∀ k, eSec (G2 G) ≫ ψ k = eSec G := by
    rintro (I | I)
    · exact eSec_cφ x₁ (one_cube₁ (act.act a)) I
    · exact eSec_cφ x₂ (one_cube₂ (act.act (H.bar a))) I
  obtain ⟨t, ht, -⟩ := exists_gen PP.isLB (formEq_drop (ε₀ := cε) (G2 G).hom (eSec (G2 G)) (eSec G) hz) c' hc'
  exact lbIso_of_gen PP.isLB x₁ x₂ t ht

end GlobalTheory.ExtAdj
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DescAct

theorem exists_oAct_extend_toSemiAbelian_normBl : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → ∀ (tF : SAB H (Xo.XF c)), SABMap tF Xo.univ.t (pullback.fst _ _) → ∀ (G : Over S) [GrpObj G] [IsCommMonObj G] (e : tF.G.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback tF.G G j e → (∀ {k : Type} [Field k] {m n : ℕ} (C : MonoFam Xo c φ (ChartRing k m n)), IsTaut C → ∀ ξ : Sp (ChartRing k m n) ⟶ S, C.y ≫ j = jK _ ≫ ξ → ∀ (tK : SAB H (Sp (FractionRing (ChartRing k m n)))) (a : SABMap tK C.t (jK _)) (b : SABMap tK tF C.y), ∃ πC : C.t.G.left ⟶ G.left, IsGrpPullback C.t.G G ξ πC ∧ a.φ ≫ πC = b.φ ≫ e) → ∃ act : OAct (𝓞 E) G, ∀ a, (tF.act.act a).left ≫ e = e ≫ (act.act a).left := by
  intro E _ _ _ H Dw l Xo c φ _ _ _ Z zs i OZ N d J S π j _ BD hU _ tF _ G _ _ e hG he _
  obtain ⟨-, -, -, -, ⟨hBl, hP, -, hd, -⟩, -⟩ := hU
  have : AlgebraicGeometry.IsNoetherian S := GlobalTheory.isNoetherian_of_isProjOver hP
  have : IsDominant j := ⟨hd⟩
  haveI : GlobalTheory.IsNormalScheme S := hBl.1
  obtain ⟨a, ha, -⟩ := GlobalTheory.Published.SemiAbelianHomExtension.existsUnique_oAct_of_isGrpPullback
    GlobalTheory.semiAbelianHomExtension_holds (GlobalTheory.IsNormalScheme.pred S) hG he tF.act
  exact ⟨a, ha⟩

end GlobalTheory.DescAct
end
