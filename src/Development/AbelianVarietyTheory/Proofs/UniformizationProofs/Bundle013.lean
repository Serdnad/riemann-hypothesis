module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIsoOfIsClosedImmersionOfThickenings
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.QSurjective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IsoLimit

open ThickeningClosed

theorem isIso_of_isClosedImmersion {V : Type} [CommRing V] [IsLocalRing V] [IsNoetherianRing V]
    {X Z : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of V)) [IsProper f] (j : Z ⟶ X)
    [IsClosedImmersion j]
    (h : ∀ n : ℕ, ∃ l : pullback f (thick V (IsLocalRing.maximalIdeal V) n) ⟶ Z,
      l ≫ j = pullback.fst f (thick V (IsLocalRing.maximalIdeal V) n)) : IsIso j := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have key : ∀ x, x ∈ zeroLocusOpen j.ker := by
    intro x
    by_contra hx
    have hc : IsClosed (f '' (zeroLocusOpen j.ker)ᶜ) :=
      f.isClosedMap _ (isOpen_zeroLocusOpen _).isClosed_compl
    obtain ⟨y, hy, hy'⟩ :=
      (IsLocalRing.specializes_closedPoint (R := V) (f x)).mem_closed hc ⟨x, hx, rfl⟩
    refine hy (mem_of_thickenings _ f j h y ?_)
    rw [hy']
    exact le_rfl
  rw [IsClosedImmersion.isIso_iff_ker_eq_bot]
  refine le_bot_iff.1 fun U a ha ↦ ?_
  change a = 0
  refine eq_zero_of_localization a fun J hJ ↦ ?_
  obtain ⟨s, hs, hsa⟩ := exists_mul_eq_zero_of_mem j.ker U ⟨J, hJ.isPrime⟩ (key _) ha
  exact (IsLocalization.map_eq_zero_iff J.primeCompl _ a).2 ⟨⟨s, hs⟩, hsa⟩

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V] (Γ₁ Y : Over (Spec (CommRingCat.of V))) (p : Γ₁ ⟶ Y) [IsProper Y.hom] [IsProper p.left], (∀ e, IsIso ((Over.pullback (thick V (IsLocalRing.maximalIdeal V) e)).map p)) → IsIso p := by
  intro V _ _ _ _ Γ₁ Y p _ _ h
  have hw : p.left ≫ Y.hom = Γ₁.hom := Over.w p
  let q (e : ℕ) : pullback Γ₁.hom (thick V (IsLocalRing.maximalIdeal V) e) ⟶
      pullback Y.hom (thick V (IsLocalRing.maximalIdeal V) e) :=
    ((Over.pullback (thick V (IsLocalRing.maximalIdeal V) e)).map p).left
  have hq (e : ℕ) : IsIso (q e) := by
    haveI := h e
    exact inferInstanceAs (IsIso ((Over.forget _).map
      ((Over.pullback (thick V (IsLocalRing.maximalIdeal V) e)).map p)))
  have q1 (e : ℕ) : q e ≫ pullback.fst _ _ = pullback.fst _ _ ≫ p.left := pullback.lift_fst _ _ _
  have q2 (e : ℕ) : q e ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  have hd : IsIso (pullback.diagonal p.left) := by
    refine isIso_of_isClosedImmersion (pullback.fst p.left p.left ≫ p.left ≫ Y.hom) _ fun n ↦ ?_
    have c := pullback.condition (f := pullback.fst p.left p.left ≫ p.left ≫ Y.hom)
      (g := thick V (IsLocalRing.maximalIdeal V) n)
    have c' := pullback.condition (f := p.left) (g := p.left)
    set u := pullback.fst (pullback.fst p.left p.left ≫ p.left ≫ Y.hom)
      (thick V (IsLocalRing.maximalIdeal V) n)
    set v := pullback.snd (pullback.fst p.left p.left ≫ p.left ≫ Y.hom)
      (thick V (IsLocalRing.maximalIdeal V) n)
    have e : pullback.lift (f := Γ₁.hom) (u ≫ pullback.fst _ _) v
          (by rw [← c, ← hw, Category.assoc]) =
        pullback.lift (f := Γ₁.hom) (u ≫ pullback.snd _ _) v
          (by rw [← c, ← hw, Category.assoc, ← reassoc_of% c']) := by
      haveI := hq n
      rw [← cancel_mono (q n)]
      apply pullback.hom_ext
      · simp only [Category.assoc, q1, pullback.lift_fst_assoc, c']
      · simp only [Category.assoc, q2, pullback.lift_snd]
    have e' := congrArg (· ≫ pullback.fst _ _) e
    simp only [pullback.lift_fst] at e'
    refine ⟨u ≫ pullback.fst _ _, ?_⟩
    apply pullback.hom_ext
    · simp
    · simp [e']
  have hm : Mono p.left := (pullback.isIso_diagonal_iff p.left).1 hd
  have hc : IsClosedImmersion p.left :=
    (IsClosedImmersion.iff_isProper_and_mono p.left).2 ⟨‹_›, hm⟩
  have hi : IsIso p.left := by
    refine isIso_of_isClosedImmersion Y.hom _ fun n ↦ ?_
    haveI := hq n
    exact ⟨inv (q n) ≫ pullback.fst _ _, by rw [Category.assoc, ← q1, IsIso.inv_hom_id_assoc]⟩
  have : IsIso ((Over.forget _).map p) := hi
  exact isIso_of_reflects_iso p (Over.forget _)

end GlobalTheory.IsoLimit
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RatLift

theorem exists_lift_of_retraction {X B Z : Scheme.{0}} [IsAffine Z] (q : X ⟶ B) [IsAffineHom q] {V : B.Opens}
    (hV : IsAffineOpen V) (r : Γ(X, q ⁻¹ᵁ V) ⟶ Γ(B, V)) (hr : q.app V ≫ r = 𝟙 _) (b : Z ⟶ B)
    (hb : ⊤ ≤ b ⁻¹ᵁ V) : ∃ x : Z ⟶ X, x ≫ q = b := by
  refine ⟨Z.isoSpec.hom ≫ Spec.map (b.appLE V ⊤ hb) ≫ Spec.map r ≫ (hV.preimage q).fromSpec, ?_⟩
  simp only [Category.assoc]
  rw [← hV.SpecMap_appLE_fromSpec q (hV.preimage q) le_rfl, Scheme.Hom.appLE_eq_app, ← Spec.map_comp_assoc (q.app V) r, hr,
    Spec.map_id, Category.id_comp, hV.SpecMap_appLE_fromSpec b (isAffineOpen_top Z) hb, IsAffineOpen.fromSpec_top,
    Iso.hom_inv_id_assoc]

theorem exists_retraction {A C X : Type} [CommRing A] [CommRing C] [AddCommGroup X] (f : A →+* C)
    (g : Multiplicative X →* C)
    (h : Function.Bijective (AddMonoidAlgebra.liftNCRingHom f g (fun _ _ => Commute.all _ _))) :
    ∃ r : C →+* A, r.comp f = RingHom.id A := by
  let e := RingEquiv.ofBijective _ h
  let a : AddMonoidAlgebra A X →+* A :=
    AddMonoidAlgebra.liftNCRingHom (RingHom.id A) (1 : Multiplicative X →* A) (fun _ _ => Commute.all _ _)
  refine ⟨a.comp e.symm.toRingHom, RingHom.ext fun c => ?_⟩
  have : e.symm (f c) = AddMonoidAlgebra.single 0 c := by
    rw [RingEquiv.symm_apply_eq]
    simp [e, AddMonoidAlgebra.liftNCRingHom]
  simp [this, a, AddMonoidAlgebra.liftNCRingHom]

attribute [local instance] SplitExt.free SplitExt.finite

theorem exists_point_over :
    ∀ (F : Type) [Field F] (E : SplitExt (Spec (CommRingCat.of F))) (G : Over (Spec (CommRingCat.of F))) [GrpObj G] (Dat : E.GtDatum G) (b : 𝟙_ (Over (Spec (CommRingCat.of F))) ⟶ E.B), ∃ x : 𝟙_ (Over (Spec (CommRingCat.of F))) ⟶ G, x ≫ Dat.q = b := by
  intro F _ E G _ Dat b
  let b' : Spec (CommRingCat.of F) ⟶ E.B.left := b.left
  let p : Spec (CommRingCat.of F) := default
  choose j hj using fun k => exists_chart (E.O (E.basis k)).isLB (b' p)
  have hp : b' p ∈ E.chart j := by
    have : ((E.chart j : E.B.left.Opens) : Set E.B.left) =
      ⋂ k, ((E.O (E.basis k)).L.U (j k) : Set E.B.left) := TopologicalSpace.Opens.coe_iInf _
    exact this.ge (Set.mem_iInter.2 hj)
  obtain ⟨_, ⟨V, hV, rfl⟩, hpV, hVj⟩ :=
    E.B.left.isBasis_affineOpens.exists_subset_of_mem_open hp (E.chart j).2
  obtain ⟨r, hr⟩ := exists_retraction _ _ (Dat.coord j V hV hVj)
  have := Dat.q_affine
  obtain ⟨x, hx⟩ := exists_lift_of_retraction Dat.q.left hV (CommRingCat.ofHom r) (CommRingCat.hom_ext hr) b'
    (fun y _ => by
      obtain rfl : y = p := Subsingleton.elim _ _
      exact hpV)
  refine ⟨Over.homMk x ?_, Over.OverMorphism.ext hx⟩
  rw [← Over.w Dat.q, ← Category.assoc, hx]
  exact Over.w b

end GlobalTheory.RatLift
end
