module

public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.ImmersionBiholo


open Topology in
theorem ker_fderiv_comp_biholo : ∀ (e : ℕ) (X₁ X₂ V : Type) [TopologicalSpace X₁] [TopologicalSpace X₂] [NormedAddCommGroup V] [NormedSpace ℂ V] (A₁ : ReciprocityTheory.AnForm.M.FinHolAtlas e X₁) (A₂ : ReciprocityTheory.AnForm.M.FinHolAtlas e X₂) (π : X₁ → X₂) (inv : X₂ → X₁), ReciprocityTheory.AnForm.M.HoloMap A₁ A₂ π → ReciprocityTheory.AnForm.M.HoloMap A₂ A₁ inv → Function.Bijective π → (∀ x, inv (π x) = x) → ∀ (Φ : X₁ → V) (x : X₂) (j₁ : Fin A₁.n) (j₂ : Fin A₂.n), inv x ∈ (A₁.chart j₁).source → x ∈ (A₂.chart j₂).source → DifferentiableAt ℂ (fun v => Φ ((A₁.chart j₁).symm v)) (A₁.chart j₁ (inv x)) → (fderiv ℂ (fun v => Φ ((A₁.chart j₁).symm v)) (A₁.chart j₁ (inv x))).ker = ⊥ → (fderiv ℂ (fun v => Φ (inv ((A₂.chart j₂).symm v))) (A₂.chart j₂ x)).ker = ⊥ := by
  intro e X₁ X₂ V _ _ _ _ A₁ A₂ π inv hπ hinv hbij hleft Φ x j₁ j₂ hx₁ hx₂ hdiff hker
  have hright : ∀ y, π (inv y) = y := fun y => by
    obtain ⟨w, rfl⟩ := hbij.2 y
    rw [hleft]
  have hy : A₂.chart j₂ x ∈ (A₂.chart j₂).target := (A₂.chart j₂).map_source hx₂
  have hsy : (A₂.chart j₂).symm (A₂.chart j₂ x) = x := (A₂.chart j₂).left_inv hx₂
  have hz : A₁.chart j₁ (inv x) ∈ (A₁.chart j₁).target := (A₁.chart j₁).map_source hx₁
  have hsz : (A₁.chart j₁).symm (A₁.chart j₁ (inv x)) = inv x := (A₁.chart j₁).left_inv hx₁
  have hτ : DifferentiableAt ℂ (⇑(A₁.chart j₁) ∘ inv ∘ ⇑(A₂.chart j₂).symm) (A₂.chart j₂ x) := by
    have hmem : A₂.chart j₂ x ∈ (A₂.chart j₂).target ∩
        ⇑(A₂.chart j₂).symm ⁻¹' (inv ⁻¹' (A₁.chart j₁).source) := by
      refine ⟨hy, ?_⟩
      show inv ((A₂.chart j₂).symm (A₂.chart j₂ x)) ∈ (A₁.chart j₁).source
      rw [hsy]
      exact hx₁
    exact (hinv.2 j₂ j₁ _ hmem).differentiableAt
  have hσ : DifferentiableAt ℂ (⇑(A₂.chart j₂) ∘ π ∘ ⇑(A₁.chart j₁).symm) (A₁.chart j₁ (inv x)) := by
    have hmem : A₁.chart j₁ (inv x) ∈ (A₁.chart j₁).target ∩
        ⇑(A₁.chart j₁).symm ⁻¹' (π ⁻¹' (A₂.chart j₂).source) := by
      refine ⟨hz, ?_⟩
      show π ((A₁.chart j₁).symm (A₁.chart j₁ (inv x))) ∈ (A₂.chart j₂).source
      rw [hsz, hright]
      exact hx₂
    exact (hπ.2 j₁ j₂ _ hmem).differentiableAt
  have hev : ∀ᶠ v in 𝓝 (A₂.chart j₂ x),
      v ∈ (A₂.chart j₂).target ∧ inv ((A₂.chart j₂).symm v) ∈ (A₁.chart j₁).source := by
    refine Filter.Eventually.and ((A₂.chart j₂).open_target.mem_nhds hy) ?_
    have hc : ContinuousAt (inv ∘ ⇑(A₂.chart j₂).symm) (A₂.chart j₂ x) :=
      hinv.1.continuousAt.comp ((A₂.chart j₂).continuousAt_symm hy)
    have hs : (A₁.chart j₁).source ∈ 𝓝 ((inv ∘ ⇑(A₂.chart j₂).symm) (A₂.chart j₂ x)) := by
      rw [Function.comp_apply, hsy]
      exact (A₁.chart j₁).open_source.mem_nhds hx₁
    exact hc.preimage_mem_nhds hs
  have hτz : (⇑(A₁.chart j₁) ∘ inv ∘ ⇑(A₂.chart j₂).symm) (A₂.chart j₂ x) = A₁.chart j₁ (inv x) := by
    simp only [Function.comp_apply, hsy]
  have hσ' : DifferentiableAt ℂ (⇑(A₂.chart j₂) ∘ π ∘ ⇑(A₁.chart j₁).symm)
      ((⇑(A₁.chart j₁) ∘ inv ∘ ⇑(A₂.chart j₂).symm) (A₂.chart j₂ x)) := by
    rw [hτz]
    exact hσ
  have hid : (⇑(A₂.chart j₂) ∘ π ∘ ⇑(A₁.chart j₁).symm) ∘ (⇑(A₁.chart j₁) ∘ inv ∘ ⇑(A₂.chart j₂).symm)
      =ᶠ[𝓝 (A₂.chart j₂ x)] id := by
    filter_upwards [hev] with v hv
    simp only [Function.comp_apply, id_eq]
    rw [(A₁.chart j₁).left_inv hv.2, hright, (A₂.chart j₂).right_inv hv.1]
  have hcomp : (fderiv ℂ (⇑(A₂.chart j₂) ∘ π ∘ ⇑(A₁.chart j₁).symm)
      ((⇑(A₁.chart j₁) ∘ inv ∘ ⇑(A₂.chart j₂).symm) (A₂.chart j₂ x))).comp
      (fderiv ℂ (⇑(A₁.chart j₁) ∘ inv ∘ ⇑(A₂.chart j₂).symm) (A₂.chart j₂ x))
      = ContinuousLinearMap.id ℂ (Fin e → ℂ) := by
    rw [← fderiv_comp _ hσ' hτ, hid.fderiv_eq, fderiv_id]
  have hτinj : ∀ w, fderiv ℂ (⇑(A₁.chart j₁) ∘ inv ∘ ⇑(A₂.chart j₂).symm) (A₂.chart j₂ x) w = 0 → w = 0 := by
    intro w hw
    have h := congrArg (fun L : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ) => L w) hcomp
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, hw, map_zero] at h
    exact h.symm
  have hdiff' : DifferentiableAt ℂ (fun v => Φ ((A₁.chart j₁).symm v))
      ((⇑(A₁.chart j₁) ∘ inv ∘ ⇑(A₂.chart j₂).symm) (A₂.chart j₂ x)) := by
    rw [hτz]
    exact hdiff
  have hker' : (fderiv ℂ (fun v => Φ ((A₁.chart j₁).symm v))
      ((⇑(A₁.chart j₁) ∘ inv ∘ ⇑(A₂.chart j₂).symm) (A₂.chart j₂ x))).ker = ⊥ := by
    rw [hτz]
    exact hker
  have hfeq : (fun v => Φ (inv ((A₂.chart j₂).symm v))) =ᶠ[𝓝 (A₂.chart j₂ x)]
      (fun v => Φ ((A₁.chart j₁).symm v)) ∘ (⇑(A₁.chart j₁) ∘ inv ∘ ⇑(A₂.chart j₂).symm) := by
    filter_upwards [hev] with v hv
    simp only [Function.comp_apply]
    rw [(A₁.chart j₁).left_inv hv.2]
  rw [hfeq.fderiv_eq, fderiv_comp _ hdiff' hτ, eq_bot_iff]
  intro w hw
  rw [Submodule.mem_bot]
  apply hτinj
  have h1 : fderiv ℂ (⇑(A₁.chart j₁) ∘ inv ∘ ⇑(A₂.chart j₂).symm) (A₂.chart j₂ x) w ∈
      (fderiv ℂ (fun v => Φ ((A₁.chart j₁).symm v))
        ((⇑(A₁.chart j₁) ∘ inv ∘ ⇑(A₂.chart j₂).symm) (A₂.chart j₂ x))).ker := hw
  rw [hker'] at h1
  exact h1

end GlobalTheory.CompanionTheory.Ar.ImmersionBiholo
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LiePull

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
  {φ : G'.left ⟶ G.left}

def push (h : IsGrpPullback G' G f φ) {T : Over S'} {g : T.left ⟶ S} (hg : T.hom ≫ f = g) (v : T ⟶ G') :
    Over.mk g ⟶ G :=
  Over.homMk (v.left ≫ φ) (by
    have e : (v.left ≫ φ) ≫ G.hom = g := by
      rw [Category.assoc, h.1.w, ← Category.assoc, Over.w v, hg]
    exact e)

def pull (h : IsGrpPullback G' G f φ) {T : Over S'} {g : T.left ⟶ S} (hg : T.hom ≫ f = g)
    (a : Over.mk g ⟶ G) : T ⟶ G' :=
  Over.homMk (h.1.lift a.left T.hom (by rw [hg]; exact Over.w a)) (h.1.lift_snd _ _ _)

def pts (h : IsGrpPullback G' G f φ) {T : Over S'} {g : T.left ⟶ S} (hg : T.hom ≫ f = g) :
    (T ⟶ G') ≃* (Over.mk g ⟶ G) where
  toFun := push h hg
  invFun := pull h hg
  left_inv v := by
    apply Over.OverMorphism.ext
    apply h.1.hom_ext
    · exact h.1.lift_fst _ _ _
    · exact (h.1.lift_snd _ _ _).trans (Over.w v).symm
  right_inv a := Over.OverMorphism.ext (h.1.lift_fst _ _ _)
  map_mul' v w := by
    subst hg
    exact Over.OverMorphism.ext (h.2 T v w _ _ rfl rfl).symm

theorem pts_left (h : IsGrpPullback G' G f φ) {T : Over S'} {g : T.left ⟶ S} (hg : T.hom ≫ f = g)
    (v : T ⟶ G') : (pts h hg v).left = v.left ≫ φ := rfl

variable {R : Type} [CommRing R]

theorem one_left (h : IsGrpPullback G' G f φ) (x' : Sp R ⟶ S') :
    (1 : Over.mk x' ⟶ G').left ≫ φ = (1 : Over.mk (x' ≫ f) ⟶ G).left := by
  have e := map_one (pts h (T := Over.mk x') (g := x' ≫ f) rfl)
  exact (pts_left h rfl _).symm.trans (congrArg (fun z => z.left) e)

theorem eps_assoc (x' : Sp R ⟶ S') : (epsAt x').hom ≫ f = (epsAt (x' ≫ f)).hom :=
  Category.assoc _ _ _

abbrev tanPts (h : IsGrpPullback G' G f φ) (x' : Sp R ⟶ S') :
    (epsAt x' ⟶ G') ≃* (epsAt (x' ≫ f) ⟶ G) :=
  pts h (T := epsAt x') (g := (epsAt (x' ≫ f)).hom) (eps_assoc x')

theorem fst_comp_base (x' : Sp R ⟶ S') :
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) ≫ (epsAt x').hom = x' := by
  have e : (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫
      CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom = 𝟙 _ := by
    ext r
    simp
  have e' := congrArg Spec.map e
  simp only [Spec.map_comp, Spec.map_id] at e'
  show _ ≫ Spec.map _ ≫ x' = x'
  rw [← Category.assoc, e', Category.id_comp]

theorem epsMul_comp_base (x' : Sp R ⟶ S') (c : R) :
    Spec.map (CommRingCat.ofHom (epsMul c)) ≫ (epsAt x').hom = (epsAt x').hom := by
  have e : (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ CommRingCat.ofHom (epsMul c) =
      CommRingCat.ofHom (algebraMap R (DualNumber R)) := by
    refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
    show epsMul c (algebraMap R (DualNumber R) r) = algebraMap R (DualNumber R) r
    rw [TrivSqZeroExt.algebraMap_eq_inl]
    ext <;> simp [epsMul]
  have e' := congrArg Spec.map e
  simp only [Spec.map_comp] at e'
  show _ ≫ Spec.map _ ≫ x' = Spec.map _ ≫ x'
  rw [← Category.assoc, e']

theorem isTan_iff (h : IsGrpPullback G' G f φ) (x' : Sp R ⟶ S') (v : epsAt x' ⟶ G') :
    IsTanAt G (x' ≫ f) (tanPts h x' v) ↔ IsTanAt G' x' v := by
  unfold IsTanAt
  constructor
  · intro t
    apply h.1.hom_ext
    · rw [Category.assoc, one_left h x', ← pts_left h (eps_assoc x') v]
      exact t
    · rw [Category.assoc, Over.w v, fst_comp_base]
      exact (Over.w (1 : Over.mk x' ⟶ G')).symm
  · intro t
    rw [← one_left h x', ← t, pts_left h (eps_assoc x') v, Category.assoc]

def modelPull (h : IsGrpPullback G' G f φ) (x' : Sp R ⟶ S') {E : Type} [AddCommGroup E] [Module R E]
    (M : LieModel G (x' ≫ f) E) : LieModel G' x' E where
  pt e := (tanPts h x').symm (M.pt e)
  tan e := (isTan_iff h x' _).1 (by rw [MulEquiv.apply_symm_apply]; exact M.tan e)
  inj e e' w := M.inj ((tanPts h x').symm.injective w)
  onto v t := by
    obtain ⟨e, he⟩ := M.onto _ ((isTan_iff h x' v).2 t)
    exact ⟨e, by rw [he, MulEquiv.symm_apply_apply]⟩
  add e e' := by rw [M.add, map_mul]
  smul c e := by
    apply h.1.hom_ext
    · have a : ∀ e, ((tanPts h x').symm (M.pt e)).left ≫ φ = (M.pt e).left := fun e => by
        rw [← pts_left h (eps_assoc x'), MulEquiv.apply_symm_apply]
      rw [Category.assoc, a, a]
      exact M.smul c e
    · have b : ((tanPts h x').symm (M.pt e)).left ≫ G'.hom = (epsAt x').hom := Over.w _
      rw [Category.assoc, Over.w, b]
      exact (epsMul_comp_base x' c).symm

def modelPush (h : IsGrpPullback G' G f φ) (x' : Sp R ⟶ S') {E : Type} [AddCommGroup E] [Module R E]
    (M : LieModel G' x' E) : LieModel G (x' ≫ f) E where
  pt e := tanPts h x' (M.pt e)
  tan e := (isTan_iff h x' _).2 (M.tan e)
  inj e e' w := M.inj ((tanPts h x').injective w)
  onto v t := by
    have t' : IsTanAt G (x' ≫ f) (tanPts h x' ((tanPts h x').symm v)) := by
      rw [MulEquiv.apply_symm_apply]; exact t
    obtain ⟨e, he⟩ := M.onto _ ((isTan_iff h x' _).1 t')
    exact ⟨e, by rw [he, MulEquiv.apply_symm_apply]⟩
  add e e' := by rw [M.add, map_mul]
  smul c e := by
    show (M.pt (c • e)).left ≫ φ = _ ≫ (M.pt e).left ≫ φ
    rw [M.smul, Category.assoc]

theorem lieModel_pullback : ∀ (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → ∀ (R : Type) [CommRing R] (x' : Sp R ⟶ S') (E : Type) [AddCommGroup E] [Module R E], (∀ M : LieModel G (x' ≫ f) E, ∃ M' : LieModel G' x' E, ∀ e, (M'.pt e).left ≫ φ = (M.pt e).left) ∧ ∀ M' : LieModel G' x' E, ∃ M : LieModel G (x' ≫ f) E, ∀ e, (M'.pt e).left ≫ φ = (M.pt e).left := by
  intro S S' G G' _ _ f φ h R _ x' E _ _
  refine ⟨fun M => ⟨modelPull h x' M, fun e => ?_⟩, fun M' => ⟨modelPush h x' M', fun e => rfl⟩⟩
  show ((tanPts h x').symm (M.pt e)).left ≫ φ = _
  rw [← pts_left h (eps_assoc x'), MulEquiv.apply_symm_apply]

end GlobalTheory.CompanionTheory.Ar.LiePull
end
end
