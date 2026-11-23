module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle025
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.IBIsKernel
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle042
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.HtPt.Cg

theorem lbIso_refl {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) : LBIso L L := by
  refine ⟨⟨fun p => L.g p.1 p.2⟩, fun p q => unit_ext fun y hy => ?_⟩
  refine (gm_res _ y _ hy _).trans (Eq.symm ?_)
  refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_div L L (𝟙 X) y p q hy) (gm_res _ y _ hy _))).trans ?_
  have a := gm_cocycle hL (𝟙 X) y hy.1.1 hy.2.1 hy.2.2
  have b := gm_cocycle hL (𝟙 X) y hy.1.1 hy.1.2 hy.2.2
  exact (mul_right_comm _ _ _).trans (mul_inv_eq_of_eq_mul (a.trans b.symm))

theorem unif_pf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R)) (_ : PELUnif (IsLocalRing.maximalIdeal R) t), GeomPF t (spMap (IsLocalRing.residue R)) := by
  intro E _ _ _ H R _ _ _ t P
  let I := IsLocalRing.maximalIdeal R
  let D := P.D.toPre
  let c := P.U.toUnifPre.gt 0
  let g : Sp (IsLocalRing.ResidueField R) ⟶ Sp (R ⧸ I ^ (0 + 1)) :=
    spMap (Ideal.Quotient.factor (show I ^ (0 + 1) ≤ I by simp))
  have hg : g ≫ Out.thick R I 0 = spMap (IsLocalRing.residue R) := by
    exact (Spec.map_comp _ _).symm.trans (congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun _ => rfl)))
  obtain ⟨eG, mG, hG⟩ := grpPullback_iso (isGrpPullback_pullback t.G (spMap (IsLocalRing.residue R)))
    (((isGrpPullback_pullback (Out.thickObj R I 0 t.G) g).comp (isGrpPullback_pullback t.G _)).congr hg rfl)
  obtain ⟨eB, mB, hB⟩ := grpPullback_iso (isGrpPullback_pullback D.P.A (spMap (IsLocalRing.residue R)))
    (((isGrpPullback_pullback (Out.thickObj R I 0 D.P.A) g).comp (isGrpPullback_pullback D.P.A _)).congr hg rfl)
  obtain ⟨eT, mT, -⟩ := GlobalTheory.TorusExtBaseChange.exists_splitTorus_iso g (AddEquiv.refl D.X)
  have := c.q_hom
  have := c.i_hom
  obtain ⟨q, i, hq, hf, hs, ha, hi, hk, hqc, -⟩ := GlobalTheory.TorusExtBaseChange.exists_extension g eT eG eB c.i c.q
    c.q_flat c.q_surj c.q_affine c.isKernel
  have hM := pull_isLB D.P.isLB (pullback.fst D.P.A.hom (spMap (IsLocalRing.residue R)))
  refine ⟨{ X := D.X
            free := D.freeX
            finite := D.finX
            B := (Over.pullback (spMap (IsLocalRing.residue R))).obj D.P.A
            isAbelian := Out.TLinPf.isAb_pullback _ _ D.P.isAb
            q := q
            q_hom := hq
            q_flat := hf
            q_surjective := hs
            q_quasiCompact := inferInstance
            i := i
            i_hom := hi
            isKernel := hk }, D.P.L.pull (pullback.fst D.P.A.hom (spMap (IsLocalRing.residue R))), hM, ?_, ?_⟩
  · obtain ⟨w, hw⟩ := lbIso_refl hM
    exact kTriv_pull (isGrpPullback_pullback D.P.A _) D.P.isLB hM ((isGen_iff w).1 hw) D.P.ktriv
  · have h0 : LBIso (P.U.toUnifPre.LG.L.pull (Out.fstG I 0 t.G).left) (D.P.L.pull c.pG.left) :=
      ⟨P.U.toUnifPre.w 0, P.U.toUnifPre.w_gen 0⟩
    rw [show P.U.toUnifPre.LG = t.PP from P.bundle] at h0
    refine h0.chartPull (h := eG.hom.left ≫ pullback.fst (Out.thickObj R I 0 t.G).hom g)
      (chartPullSame _ _ _ _ _ fun _ => ?_) (chartPullLinComb _ _ _ _ _ _ fun _ => ?_)
    · rw [Category.assoc]; exact hG.symm
    · show q.left ≫ _ = _ ≫ c.q.left ≫ pullback.fst D.P.A.hom (Out.thick R I 0)
      rw [← hB, ← Category.assoc _ c.q.left, ← hqc]
      simp only [Category.assoc]

end PositivityTheory.HtPt.Cg
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace PositivityTheory.HtPt.Cf

def PF {k : Type} [Field k] (G : Over (Sp k)) [GrpObj G] (L : LB G.left) : Prop :=
  ∃ (T : TorusExtension G) (M : LB T.B.left),
    letI := T.grpB
    M.IsLB ∧ Out.KTriv T.B M ∧ LBIso L (M.pull T.q.left)

def teBC {k k₂ : Type} [Field k] [Field k₂] (f : Sp k₂ ⟶ Sp k) {G : Over (Sp k)} [GrpObj G]
    (T : TorusExtension G) : TorusExtension ((Over.pullback f).obj G) :=
  letI := T.grpB
  letI := T.addCommGroup
  haveI := T.q_hom
  haveI := T.i_hom
  { X := T.X
    addCommGroup := T.addCommGroup
    free := T.free
    finite := T.finite
    B := (Over.pullback f).obj T.B
    isAbelian :=
      { comm := by have := T.isAbelian.comm; infer_instance
        smooth := by have := T.isAbelian.smooth; show Smooth (pullback.snd _ _); infer_instance
        proper := by have := T.isAbelian.proper; show IsProper (pullback.snd _ _); infer_instance
        geomConnected := by
          have := T.isAbelian.geomConnected; show GeometricallyConnected (pullback.snd _ _); infer_instance }
    q := Out.GtBCPf.qB f T.q
    q_hom := inferInstance
    q_flat := Out.GtBCPf.qB_flat f T.q T.q_flat
    q_surjective := Out.GtBCPf.qB_surj f T.q T.q_surjective
    q_quasiCompact := MorphismProperty.of_isPullback (P := @QuasiCompact) (Out.GtBCPf.qB_sq f T.q) T.q_quasiCompact
    i := Out.GtBCPf.iB f T.X T.i
    i_hom := Out.GtBCPf.iB_hom f T.X T.i
    isKernel := Out.GtBCPf.iB_isKernel f T.X T.q T.i T.isKernel }

theorem lbIso_refl {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) : LBIso L L := by
  refine ⟨⟨fun p => L.g p.1 p.2⟩, fun p q => unit_ext fun y hy => ?_⟩
  refine (gm_res _ y _ hy _).trans (Eq.symm ((map_mul _ _ _).trans ?_))
  refine (congrArg₂ (· * ·) (gm_div L L (𝟙 X) y p q hy) (gm_res _ y _ hy _)).trans ?_
  have a := gm_cocycle hL (𝟙 X) y hy.1.1 hy.2.1 hy.2.2
  have b := gm_cocycle hL (𝟙 X) y hy.1.1 hy.1.2 hy.2.2
  show _ * _ * gm (𝟙 X) y (L.U q.1 ⊓ L.U q.2) (L.g q.1 q.2) = gm (𝟙 X) y (L.U p.1 ⊓ L.U p.2) (L.g p.1 p.2)
  rw [mul_right_comm, a, ← b, mul_inv_cancel_right]

theorem lbIso_pull_pull {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (F : Y ⟶ X) (g : Z ⟶ Y) (h : Z ⟶ X)
    (e : g ≫ F = h) : LBIso (L.pull h) ((L.pull F).pull g) :=
  LBIso.chartPull (chartPullId _) (chartPullLinComb L F (fun _ : PUnit => g) (fun _ => h) (fun _ => 1) (𝟙 Z)
    fun _ => e.trans (Category.id_comp _).symm) (lbIso_refl (LB.isLB_pull hL h))

theorem pf_pull {k k₂ : Type} [Field k] [Field k₂] (f : Sp k₂ ⟶ Sp k) {G : Over (Sp k)} [GrpObj G]
    {G₂ : Over (Sp k₂)} [GrpObj G₂] {φ : G₂.left ⟶ G.left} (h : IsGrpPullback G₂ G f φ) {L : LB G.left}
    {L₂ : LB G₂.left} (hL : L.IsLB) (hL₂ : L₂.IsLB) (w : LBIso L₂ (L.pull φ)) (H : PF G L) : PF G₂ L₂ := by
  obtain ⟨T, M, hM, hK, hi⟩ := H
  let := T.grpB
  obtain ⟨e, he, hφ⟩ := grpPullback_iso (isGrpPullback_pullback G f) h
  have hM₂ := LB.isLB_pull hM (pullback.fst T.B.hom f)
  obtain ⟨u, hu⟩ := lbIso_refl hM₂
  have hK₂ := kTriv_pull (isGrpPullback_pullback T.B f) hM hM₂ ((isGen_iff u).1 hu) hK
  refine ⟨torusExtOfIso e (teBC f T), M.pull (pullback.fst T.B.hom f), hM₂, hK₂, ?_⟩
  have hc : (e.inv ≫ Out.GtBCPf.qB f T.q).left ≫ pullback.fst T.B.hom f = φ ≫ T.q.left := by
    rw [Over.comp_left, Category.assoc, Out.GtBCPf.qB_h, ← hφ, ← Category.assoc, ← Category.assoc, ← Over.comp_left,
      e.inv_hom_id, Over.id_left, Category.id_comp]
  exact LBIso.trans hL₂ (LB.isLB_pull hL φ) (LB.isLB_pull hM₂ _) w
    (LBIso.chartPull (chartPullPull L φ φ rfl) (chartPullLinComb M (pullback.fst T.B.hom f)
      (fun _ : PUnit => (e.inv ≫ Out.GtBCPf.qB f T.q).left) (fun _ => T.q.left) (fun _ => 1) φ fun _ => hc) hi)

theorem geompf_bc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0), (∀ (k k₂ : Type) [Field k] [Field k₂] (f : k →+* k₂) (x : Sp k ⟶ X0), GeomPF t x → GeomPF t (spMap f ≫ x)) ∧ ∀ (X₂ : Scheme.{0}) (t₂ : SAB H X₂) (f : X₂ ⟶ X0) (_ : SABMap t₂ t f) (k : Type) [Field k] (x : Sp k ⟶ X₂), GeomPF t₂ x ↔ GeomPF t (x ≫ f) := by
  intro E _ _ _ H X0 t
  have hL := t.PP.isLB
  refine ⟨fun k k₂ _ _ f x h => ?_, fun X₂ t₂ f m k _ x => ?_⟩
  · let φ : pullback t.G.hom (spMap f ≫ x) ⟶ pullback t.G.hom x :=
      pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ spMap f) (by rw [Category.assoc, pullback.condition])
    have e : φ ≫ pullback.fst t.G.hom x = pullback.fst _ _ := pullback.lift_fst _ _ _
    have hg : IsGrpPullback ((Over.pullback (spMap f ≫ x)).obj t.G) ((Over.pullback x).obj t.G) (spMap f) φ :=
      (isGrpPullback_pullback t.G x).cancel ((isGrpPullback_pullback t.G _).congr rfl e.symm) (pullback.lift_snd _ _ _)
    exact pf_pull (spMap f) hg (LB.isLB_pull hL _) (LB.isLB_pull hL _) (lbIso_pull_pull hL _ φ _ e) h
  · have hL₂ := t₂.PP.isLB
    have h₁ := (isGrpPullback_pullback t₂.G x).comp m.cart
    have h₂ := isGrpPullback_pullback t.G (x ≫ f)
    obtain ⟨w, hw, -⟩ := m.lin
    have w₁ : LBIso (t₂.PP.L.pull (pullback.fst t₂.G.hom x)) ((t.PP.L.pull m.cm.F).pull (pullback.fst t₂.G.hom x)) :=
      LBIso.chartPull (chartPullPull _ _ _ rfl) (chartPullPull _ _ _ rfl) ⟨w, hw⟩
    have w₂ := LBIso.trans (LB.isLB_pull hL₂ _) (LB.isLB_pull (LB.isLB_pull hL _) _) (LB.isLB_pull hL _) w₁
      (lbIso_pull_pull hL m.cm.F (pullback.fst t₂.G.hom x) _ rfl).symm
    constructor
    · intro h
      obtain ⟨e, he, hφ⟩ := grpPullback_iso h₂ h₁
      refine pf_pull (𝟙 _) (isGrpPullback_of_iso e) (LB.isLB_pull hL₂ _) (LB.isLB_pull hL _) ?_ h
      refine LBIso.trans (LB.isLB_pull hL _) (LB.isLB_pull (LB.isLB_pull hL _) _) (LB.isLB_pull (LB.isLB_pull hL₂ _) _)
        (lbIso_pull_pull hL _ e.hom.left _ hφ) ?_
      exact LBIso.chartPull (chartPullPull _ _ _ rfl) (chartPullPull _ _ _ rfl) w₂.symm
    · intro h
      obtain ⟨e, he, hφ⟩ := grpPullback_iso h₁ h₂
      refine pf_pull (𝟙 _) (isGrpPullback_of_iso e) (LB.isLB_pull hL _) (LB.isLB_pull hL₂ _) ?_ h
      exact LBIso.trans (LB.isLB_pull hL₂ _) (LB.isLB_pull hL _) (LB.isLB_pull (LB.isLB_pull hL _) _) w₂
        (lbIso_pull_pull hL _ e.hom.left _ hφ)

theorem exists_common {X₂ X0 : Scheme.{0}} (f : X₂ ⟶ X0) (z : X₂) {k : Type} [Field k] (x : Sp k ⟶ X0)
    (hx : x (IsLocalRing.closedPoint k) = f z) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (y : Sp Ω ⟶ X₂) (a : k →+* Ω),
      y (IsLocalRing.closedPoint Ω) = z ∧ y ≫ f = spMap a ≫ x := by
  obtain ⟨s, hs, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := x) z _ hx.symm
  let P := pullback f x
  let Ω := AlgebraicClosure (P.residueField s)
  let r : Sp Ω ⟶ P := spMap (algebraMap (P.residueField s) Ω) ≫ P.fromSpecResidueField s
  have hr : r (IsLocalRing.closedPoint Ω) = s := Scheme.fromSpecResidueField_apply s _
  refine ⟨Ω, inferInstance, inferInstance, r ≫ pullback.fst f x, (Spec.preimage (r ≫ pullback.snd f x)).hom, ?_, ?_⟩
  · exact (Scheme.Hom.comp_apply _ _ _).trans ((congrArg (pullback.fst f x) hr).trans hs)
  · show _ = Spec.map (Spec.preimage (r ≫ pullback.snd f x)) ≫ x
    rw [Spec.map_preimage, Category.assoc r, Category.assoc r, pullback.condition]

theorem fibpf_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (X₂ : Scheme.{0}) (t₂ : SAB H X₂) (f : X₂ ⟶ X0) (_ : SABMap t₂ t f) (z : X₂), FibPF t₂ z ↔ FibPF t (f z) := by
  intro E _ _ _ H X0 t X₂ t₂ f m z
  constructor
  · rintro ⟨k, _, _, x, rfl, h⟩
    exact ⟨k, _, inferInstance, x ≫ f, Scheme.Hom.comp_apply _ _ _, ((geompf_bc E H X0 t).2 X₂ t₂ f m k x).1 h⟩
  · rintro ⟨k, _, _, x, hx, h⟩
    obtain ⟨Ω, _, _, y, a, hy, e⟩ := exists_common f z x hx
    exact ⟨Ω, _, inferInstance, y, hy,
      ((geompf_bc E H X0 t).2 X₂ t₂ f m Ω y).2 (e ▸ (geompf_bc E H X0 t).1 k Ω a x h)⟩

end PositivityTheory.HtPt.Cf
end
end

section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace PositivityTheory.HtPt.Ci

theorem exists_base {S : Scheme.{0}} {G : Over S} [GrpObj G] {A R : Type} [CommRing A] [CommRing R] (φ : A →+* R)
    (x : Spec (CommRingCat.of A) ⟶ S) (z : Spec (CommRingCat.of R) ⟶ S)
    (hz : Spec.map (CommRingCat.ofHom φ) ≫ x = z) {E F : Type} [AddCommGroup E] [Module A E] [AddCommGroup F]
    [Module R F] (M : LieModel G x E) (N : LieModel G z F) :
    ∃ j : E →+ F, (∀ e, N.pt (j e) = LieTangent.epsBase φ hz ≫ M.pt e) ∧
      (∀ (a : A) e, j (a • e) = φ a • j e) ∧
      (Smooth G.hom → ∀ (n : ℕ) (b : Module.Basis (Fin n) A E),
        ∃ b' : Module.Basis (Fin n) R F, ∀ k, b' k = j (b k)) := by
  subst hz
  letI := φ.toAlgebra
  obtain ⟨j, h1, h2, h3⟩ := PositivityTheory.HtPt.Htat.lie_bc S G A R x E F M N
  refine ⟨j, fun e => Over.OverMorphism.ext (h1 e), h2, fun hs n b => ?_⟩
  exact ⟨Module.Basis.mk (h3 hs n b).1 (h3 hs n b).2.ge, fun k => Module.Basis.mk_apply _ _ _⟩

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {G : Over X} [GrpObj G]
  {V : Type} [AddCommGroup V] [Module Ω V]

theorem lieValAt_base (hξ : IsCptGen ξ) {M : LieModel G ξ V} {R R' : Type} [CommRing R] [IsLocalRing R]
    [CommRing R'] [IsLocalRing R'] (φ : R →+* R') {x : Spec (CommRingCat.of R) ⟶ X}
    {z : Spec (CommRingCat.of R') ⟶ X} (hz : Spec.map (CommRingCat.ofHom φ) ≫ x = z) {e : V} {w : epsAt x ⟶ G}
    (h : M.ValAt x e w) : M.ValAt z e (LieTangent.epsBase φ hz ≫ w) := by
  subst hz
  rw [LieModel.valAt_iff] at h ⊢
  obtain ⟨hc, v, hv, rfl⟩ := h
  have hsp := LieTangent.centre_specializes φ x
  have hc' := LieTangent.specializes_of_injective (hξ.inj ⟨_, hc⟩) hsp
  have F1 : Spec.map (CommRingCat.ofHom (X.presheaf.stalkSpecializes hsp).hom) ≫ X.fromSpecStalk (centre x) =
      X.fromSpecStalk (centre (Spec.map (CommRingCat.ofHom φ) ≫ x)) :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp
  have hd : ∀ {A B D : Type} [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (g : B →+* D),
      (dualMap g).comp (dualMap f) = dualMap (g.comp f) := by
    intro A B D _ _ _ f g
    refine RingHom.ext fun a => ?_
    ext <;> simp
  rw [LieModel.extends_iff] at hv
  refine ⟨hc', LieTangent.epsBase (X.presheaf.stalkSpecializes hsp).hom F1 ≫ v,
    (M.extends_iff _ _ _).2 ⟨LieTangent.isTanAt_base _ _ hv.1, ?_⟩, ?_⟩
  · rw [hv.2, ← Category.assoc]
    congr 1
    refine Over.OverMorphism.ext ?_
    change Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [LieTangent.spec_comp, hd]
    congr 3
    exact RingHom.ext fun s => (LieTangent.genMap_specializes ⟨_, hc⟩ hc' hsp s).symm
  · rw [← Category.assoc, ← Category.assoc]
    congr 1
    refine Over.OverMorphism.ext ?_
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [LieTangent.spec_comp, hd, LieTangent.spec_comp, hd]
    congr 3
    exact (congrArg CommRingCat.Hom.hom (LieTangent.stalk_base φ x)).symm

theorem frame_basis [IsCommMonObj G] (hξ : IsCptGen ξ) (hs : Smooth G.hom) (M : LieModel G ξ V) {R : Type}
    [CommRing R] [IsLocalRing R] (z : Spec (CommRingCat.of R) ⟶ X) (h : genPt ξ ⤳ centre z) {ER : Type}
    [AddCommGroup ER] [Module R ER] (MR : LieModel G z ER) {n : ℕ} {b : Fin n → V}
    (hb : M.lat.IsFrameAt b ⟨centre z, h⟩) :
    ∃ bz : Module.Basis (Fin n) R ER, ∀ q, M.ValAt z (b q) (MR.pt (bz q)) := by
  obtain ⟨EA, _, _, ⟨MA⟩⟩ := lieModel_exists X G (X.presheaf.stalk (centre z)) (X.fromSpecStalk (centre z))
  obtain ⟨j, hj, -, hjb⟩ := exists_base (A := X.presheaf.stalk (centre z)) (Scheme.stalkClosedPointTo z).hom _ z
    (LieTangent.spec_centre z) MA MR
  obtain ⟨i, hi, his, -⟩ := exists_base (genMap ξ ⟨centre z, h⟩) _ ξ
    (LieTangent.spec_genMap ξ ⟨centre z, h⟩) MA M
  have hext : ∀ a, M.Extends ⟨centre z, h⟩ (i a) (MA.pt a) := fun a =>
    (M.extends_iff _ _ _).2 ⟨MA.tan a, hi a⟩
  have hinj : ∀ a b, i a = i b → a = b := fun a b hab =>
    MA.inj ((hext a).unique (hξ.inj _) (hab ▸ hext b))
  have hsurj : ∀ e ∈ M.lat ⟨centre z, h⟩, ∃ a, i a = e := by
    intro e he
    obtain ⟨v, hv⟩ := (M.mem_lat_iff _ _).1 he
    obtain ⟨a, rfl⟩ := MA.onto v hv.1
    exact ⟨a, M.inj ((hi a).trans ((M.extends_iff _ _ _).1 hv).2.symm)⟩
  choose a ha using fun q => hsurj (b q) (by rw [hb.2]; exact Submodule.subset_span ⟨q, rfl⟩)
  have hsum : ∀ c : Fin n → X.presheaf.stalk (centre z),
      i (∑ q, c q • a q) = ∑ q, genMap ξ ⟨centre z, h⟩ (c q) • b q := by
    intro c

    rw [map_sum]
    exact Finset.sum_congr rfl fun q _ => by rw [his, ha]
  have li : LinearIndependent (X.presheaf.stalk (centre z)) a := by
    rw [Fintype.linearIndependent_iff]
    intro c hc q
    have h1 := hsum c
    rw [hc, map_zero] at h1
    exact hξ.inj ⟨_, h⟩ ((Fintype.linearIndependent_iff.1 hb.1 _ h1.symm q).trans (map_zero _).symm)
  have sp : ⊤ ≤ Submodule.span (X.presheaf.stalk (centre z)) (Set.range a) := by
    intro e _
    have h1 : i e ∈ M.lat ⟨centre z, h⟩ := (M.mem_lat_iff _ _).2 ⟨_, hext e⟩
    rw [hb.2, Submodule.mem_span_range_iff_exists_fun] at h1
    obtain ⟨c, hc⟩ := h1
    choose s hs using fun q => (c q).2
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨s, hinj _ _ ?_⟩
    rw [hsum, ← hc]
    exact Finset.sum_congr rfl fun q _ => by rw [hs]; rfl
  obtain ⟨bz, hbz⟩ := hjb hs n (Module.Basis.mk li sp)
  refine ⟨bz, fun q => (M.valAt_iff _ _ _).2 ⟨h, MA.pt (a q), ha q ▸ hext (a q), ?_⟩⟩
  rw [hbz, hj, Module.Basis.mk_apply]

theorem frame_lat [IsCommMonObj G] (hξ : IsCptGen ξ) (hs : Smooth G.hom) (M : LieModel G ξ V) {K : Type} [Field K]
    {C : ACurve K} {z : Spec (CommRingCat.of K) ⟶ X} (Y : CurveIn C z) {Vz : Type} [AddCommGroup Vz] [Module K Vz]
    (Mz : LieModel G z Vz) {n : ℕ} {b : Fin n → V} (i : C.I) (h : genPt ξ ⤳ centre (Y.x i))
    (hb : M.lat.IsFrameAt b ⟨centre (Y.x i), h⟩) :
    ∃ bz : Module.Basis (Fin n) K Vz, (∀ q, M.ValAt z (b q) (Mz.pt (bz q))) ∧ IsLatOf C i bz (Y.lieLat Mz i) := by
  obtain ⟨ER, _, _, ⟨MR⟩⟩ := lieModel_exists X G _ (Y.x i)
  obtain ⟨bR, hbR⟩ := frame_basis hξ hs M (Y.x i) h MR hb
  obtain ⟨j, hj, hjs, hjb⟩ := exists_base (C.v i).valuationSubring.subtype _ z (Y.gen i) MR Mz
  obtain ⟨bz, hbz⟩ := hjb hs n bR
  refine ⟨bz, fun q => ?_, fun x => ?_⟩
  · rw [hbz, hj]
    exact lieValAt_base hξ _ _ (hbR q)
  · have hr : Y.lieLat Mz i = j.range := by
      refine le_antisymm ((AddSubgroup.closure_le _).2 ?_) ?_
      · rintro e ⟨v, hv, he⟩
        obtain ⟨u, rfl⟩ := MR.onto v hv
        exact ⟨u, Mz.inj ((hj u).trans (Over.OverMorphism.ext he.symm))⟩
      · rintro _ ⟨u, rfl⟩
        exact AddSubgroup.subset_closure ⟨MR.pt u, MR.tan u, congrArg (fun q => q.left) (hj u)⟩
    have hsum : ∀ c : Fin n → (C.v i).valuationSubring, j (∑ q, c q • bR q) = ∑ q, (c q : K) • bz q := by
      intro c

      rw [map_sum]
      exact Finset.sum_congr rfl fun q _ => by rw [hjs, hbz]; rfl
    rw [hr]
    constructor
    · rintro ⟨u, rfl⟩ q
      rw [← bR.sum_repr u, hsum, bz.repr_sum_self]
      exact (bR.repr u q).2
    · intro hx
      exact ⟨∑ q, (⟨bz.repr x q, hx q⟩ : (C.v i).valuationSubring) • bR q, by rw [hsum]; exact bz.sum_repr x⟩

end PositivityTheory.HtPt.Ci
end
end
