module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle107
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle105
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle987
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.EventuallyDifferentiableAtOfContDiffAtTwo
public import ReciprocityTheory.L2DbarEstimates.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle344
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle990
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle989
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsHolFormConst
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
import Development.AbelianVarietyTheory.Definitions.Divisors.LeTwoMulOfForallScale
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleNilThickening

theorem exists_pow_eq_bot_of_isNilDP {R : Type} [CommRing R] {I : Ideal R} {κ : DividedPowers I}
    (h : IsNilDP κ) : ∃ N : ℕ, I ^ N = ⊥ := by
  obtain ⟨N, hN⟩ := h
  have hlen : ∀ l : List R, ((l.map fun x => ((1 : ℕ), x)).map Prod.fst).sum = l.length := by
    intro l; induction l with
    | nil => simp
    | cons a l ih => simp only [List.map_cons, List.sum_cons, List.length_cons] at ih ⊢; omega
  have hprod : ∀ l : List R, (∀ x ∈ l, x ∈ I) →
      ((l.map fun x => ((1 : ℕ), x)).map fun p => κ.dpow p.1 p.2).prod = l.prod := by
    intro l hl; induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [κ.dpow_one (hl a (by simp)), ih fun x hx => hl x (by simp [hx])]
  have hl : ∀ l : List R, (∀ x ∈ l, x ∈ I) → N ≤ l.length → l.prod = 0 := by
    intro l hl' hle
    rw [← hprod l hl']
    exact hN _ (by simpa using hl') (by rw [hlen]; exact hle)
  have key : ∀ k : ℕ, ∀ y ∈ I ^ k, ∀ l : List R, (∀ x ∈ l, x ∈ I) → N ≤ k + l.length → l.prod * y = 0 := by
    intro k
    induction k with
    | zero => intro y _ l hl' hle; rw [hl l hl' (by omega), zero_mul]
    | succ k ih =>
      intro y hy l hl' hle
      rw [pow_succ] at hy
      refine Submodule.mul_induction_on (C := fun y => l.prod * y = 0) hy ?_ ?_
      · intro a ha b hb
        have := ih a ha (b :: l) (by simpa [hb] using hl') (by simp; omega)
        rw [List.prod_cons] at this
        rw [← this]; ring
      · intro y z hy hz; rw [mul_add, hy, hz, add_zero]
  refine ⟨N, eq_bot_iff.2 fun y hy => ?_⟩
  have := key N y hy [] (fun x hx => by cases hx) (Nat.le_add_right N _)
  simpa using this

end GlobalTheory.AmpleNilThickening

namespace GlobalTheory.AmpleNilThickening

theorem relAmple_of_pow_eq_bot : ∀ (n : ℕ) (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π ^ n = ⊥ →
    ∀ (X : Over (Sp R)) (X₀ : Over (Sp R₀)) (β : X₀.left ⟶ X.left), IsPullback β X₀.hom X.hom (spMap π) →
      LocallyOfFiniteType X.hom → ∀ (L : LB X.left) (L₀ : LB X₀.left), L.IsLB → L₀.IsLB → LBIso L₀ (L.pull β) →
      Out.RelAmple X₀ L₀ → Out.RelAmple X L := by
  intro n
  induction n with
  | zero =>
    intro R R₀ _ _ π hπ hn X X₀ β hβ hX L L₀ hL hL₀ hw hA
    have h2 : RingHom.ker π ^ 2 = ⊥ := eq_bot_iff.2 ((Ideal.pow_le_pow_right (by omega)).trans hn.le)
    exact GlobalTheory.AmpleThickening.relAmple_of_sq_zero R R₀ π hπ h2 X X₀ β hβ hX L L₀ hL hL₀ hw hA
  | succ n ih =>
    intro R R₀ _ _ π hπ hn X X₀ β hβ hX L L₀ hL hL₀ hw hA
    by_cases h0 : n = 0
    · subst h0
      have h2 : RingHom.ker π ^ 2 = ⊥ := eq_bot_iff.2 ((Ideal.pow_le_pow_right (by omega)).trans hn.le)
      exact GlobalTheory.AmpleThickening.relAmple_of_sq_zero R R₀ π hπ h2 X X₀ β hβ hX L L₀ hL hL₀ hw hA
    set I := RingHom.ker π with hI
    let J : Ideal R := I ^ n
    let q : R →+* R ⧸ J := Ideal.Quotient.mk J
    have hJI : J ≤ RingHom.ker π := Ideal.pow_le_self h0
    let π₁ : R ⧸ J →+* R₀ := Ideal.Quotient.lift J π fun a ha => (RingHom.mem_ker).1 (hJI ha)
    have hfac : π = π₁.comp q := RingHom.ext fun _ => rfl
    have hπ₁ : Function.Surjective π₁ := fun y => by
      obtain ⟨x, hx⟩ := hπ y
      exact ⟨q x, hx⟩
    have hker₁ : RingHom.ker π₁ ^ n = ⊥ := by
      have hle : RingHom.ker π₁ ≤ I.map q := by
        intro z hz
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
        have hx : x ∈ I := RingHom.mem_ker.2 (RingHom.mem_ker.1 hz)
        exact Ideal.mem_map_of_mem q hx
      refine eq_bot_iff.2 ((Ideal.pow_right_mono hle n).trans ?_)
      rw [← Ideal.map_pow]
      exact (Ideal.map_quotient_self J).le
    have hsq : RingHom.ker q ^ 2 = ⊥ := by
      rw [Ideal.mk_ker, ← pow_mul]
      exact eq_bot_iff.2 ((Ideal.pow_le_pow_right (by omega)).trans hn.le)
    have hcomp : spMap π = spMap π₁ ≫ spMap q := by
      rw [hfac]; simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
    let f : Sp (R ⧸ J) ⟶ Sp R := spMap q
    let X₁ : Over (Sp (R ⧸ J)) := Over.mk (pullback.snd X.hom f)
    have hw' : β ≫ X.hom = (X₀.hom ≫ spMap π₁) ≫ f := by
      rw [hβ.w, hcomp, Category.assoc]
    let β₀ : X₀.left ⟶ X₁.left := pullback.lift β (X₀.hom ≫ spMap π₁) hw'
    have hβ₀ : β₀ ≫ pullback.fst X.hom f = β := pullback.lift_fst _ _ _
    have hpb : IsPullback β₀ X₀.hom X₁.hom (spMap π₁) := by
      refine IsPullback.of_right (h₁₂ := pullback.fst X.hom f) (h₂₂ := f) (v₁₃ := X.hom) ?_
        (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback X.hom f)
      rw [hβ₀, ← hcomp]
      exact hβ
    have hX₁ : LocallyOfFiniteType X₁.hom :=
      inferInstanceAs (LocallyOfFiniteType (pullback.snd X.hom f))
    let L₁ : LB X₁.left := L.pull (pullback.fst X.hom f)
    have hL₁ : L₁.IsLB := LB.isLB_pull hL _
    have hw₁ : LBIso L₀ (L₁.pull β₀) :=
      LBIso.trans hL₀ (LB.isLB_pull hL β) (LB.isLB_pull hL₁ β₀) hw
        (GlobalTheory.GenSpread.lbIso_pull_pull hL β₀ hβ₀.symm)
    have hA₁ : Out.RelAmple X₁ L₁ := ih (R ⧸ J) R₀ π₁ hπ₁ hker₁ X₁ X₀ β₀ hpb hX₁ L₁ L₀ hL₁ hL₀ hw₁ hA
    exact GlobalTheory.AmpleThickening.relAmple_of_sq_zero R (R ⧸ J) q Ideal.Quotient.mk_surjective hsq X X₁
      (pullback.fst X.hom f) (IsPullback.of_hasPullback X.hom f) hX L L₁ hL hL₁
      (lbIso_refl hL₁) hA₁

theorem relAmple_of_isNilDP : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (κ : DividedPowers I), IsNilDP κ →
    ∀ (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I →
    ∀ (X : Over (Sp R)) (X₀ : Over (Sp R₀)) (β : X₀.left ⟶ X.left), IsPullback β X₀.hom X.hom (spMap π) →
      LocallyOfFiniteType X.hom → ∀ (L : LB X.left) (L₀ : LB X₀.left), L.IsLB → L₀.IsLB → LBIso L₀ (L.pull β) →
      Out.RelAmple X₀ L₀ → Out.RelAmple X L := by
  intro R R₀ _ _ I κ hκ π hπ hker X X₀ β hβ hX L L₀ hL hL₀ hw hA
  obtain ⟨N, hN⟩ := exists_pow_eq_bot_of_isNilDP hκ
  exact relAmple_of_pow_eq_bot N R R₀ π hπ (hker ▸ hN) X X₀ β hβ hX L L₀ hL hL₀ hw hA

end GlobalTheory.AmpleNilThickening
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PresCharts

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {X₀ : Scheme.{0}}
  {s₀ : X₀ ⟶ Sp R₀} {S : Sys I π s₀} {X : Scheme.{0}} {s : X ⟶ Sp R} {i : X₀ ⟶ X}

theorem appLE_congr {A Y : Scheme.{0}} {f g : A ⟶ Y} (h : f = g) (U : Y.Opens) (W : A.Opens)
    (e : W ≤ f ⁻¹ᵁ U) : f.appLE U W e = g.appLE U W (h ▸ e) := by
  subst h; rfl

theorem specMap_appLE_top {A B : CommRingCat.{0}} (f : A ⟶ B) (e : (⊤ : (Spec B).Opens) ≤ Spec.map f ⁻¹ᵁ ⊤) :
    (Spec.map f).appLE ⊤ ⊤ e ≫ (Scheme.ΓSpecIso B).hom = (Scheme.ΓSpecIso A).hom ≫ f := by
  rw [← Scheme.ΓSpecIso_naturality]
  rfl

def chartOpen (P : S.Presents s i) (T : AffOp X₀) : X.Opens :=
  haveI := P.isOpen T
  (P.y T).opensRange

theorem preimage_chartOpen (P : S.Presents s i) (T : AffOp X₀) : P.y T ⁻¹ᵁ chartOpen P T = ⊤ := by
  haveI := P.isOpen T
  exact Scheme.Hom.preimage_opensRange _

def chartSec (P : S.Presents s i) (T : AffOp X₀) : Γ(X, chartOpen P T) ⟶ CommRingCat.of (S.F.obj T) :=
  (P.y T).appLE (chartOpen P T) ⊤ (preimage_chartOpen P T).ge ≫ (Scheme.ΓSpecIso _).hom

instance isIso_chartSec (P : S.Presents s i) (T : AffOp X₀) : IsIso (chartSec P T) := by
  haveI := P.isOpen T
  haveI : IsIso ((P.y T).app (chartOpen P T)) := Scheme.Hom.isIso_app _ _ le_rfl
  have h : homOfLE (preimage_chartOpen P T).ge = eqToHom (preimage_chartOpen P T).symm :=
    Subsingleton.elim _ _
  unfold chartSec Scheme.Hom.appLE
  rw [h]
  infer_instance

theorem chartOpen_le (P : S.Presents s i) ⦃T T' : AffOp X₀⦄ (a : T ⟶ T') : chartOpen P T' ≤ chartOpen P T := by
  haveI := P.isOpen T
  haveI := P.isOpen T'
  intro x hx
  change x ∈ ((P.y T').opensRange : Set X) at hx
  change x ∈ ((P.y T).opensRange : Set X)
  rw [Scheme.Hom.coe_opensRange] at hx ⊢
  obtain ⟨q, rfl⟩ := hx
  rw [← P.nat a, Scheme.Hom.comp_apply]
  exact Set.mem_range_self _

theorem res_chartSec (P : S.Presents s i) ⦃T T' : AffOp X₀⦄ (a : T ⟶ T') :
    X.presheaf.map (homOfLE (chartOpen_le P a)).op ≫ chartSec P T' =
      chartSec P T ≫ CommRingCat.ofHom (mp S.F a : S.F.obj T →+* S.F.obj T') := by
  have e1 : (⊤ : (Sp (S.F.obj T')).Opens) ≤ P.y T' ⁻¹ᵁ chartOpen P T :=
    (preimage_chartOpen P T').ge.trans (Scheme.Hom.preimage_mono _ (chartOpen_le P a))
  unfold chartSec
  rw [← Category.assoc, Scheme.Hom.map_appLE _ _ (homOfLE (chartOpen_le P a)).op]
  rw [appLE_congr (P.nat a).symm _ _ e1]
  rw [← Scheme.Hom.appLE_comp_appLE _ _ _ _ _ (preimage_chartOpen P T).ge le_top]
  rw [Category.assoc, Category.assoc]
  congr 1
  exact specMap_appLE_top _ _

theorem injective_of_isPullback {R R₀ : Type} [CommRing R] [CommRing R₀] {π : R →+* R₀}
    (hπ : Function.Surjective π) {s₀ : X₀ ⟶ Sp R₀} {s : X ⟶ Sp R} {i : X₀ ⟶ X}
    (h : IsPullback i s₀ s (spMap π)) : Function.Injective i := by
  haveI : IsClosedImmersion i := MorphismProperty.of_isPullback (P := @IsClosedImmersion) h.flip
    (IsClosedImmersion.spec_of_surjective _ hπ)
  exact i.isClosedEmbedding.injective

theorem fromSpec_appLE_ΓSpecIso {Y : Scheme.{0}} {U : Y.Opens} (hU : IsAffineOpen U) (e : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U) :
    hU.fromSpec.appLE U ⊤ e ≫ (Scheme.ΓSpecIso Γ(Y, U)).hom = 𝟙 _ := by
  rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, Category.assoc,
    ← Functor.map_comp_assoc]
  have : ((eqToHom hU.fromSpec_preimage_self).op ≫ (homOfLE e).op : Opposite.op _ ⟶ Opposite.op _) = 𝟙 _ :=
    Subsingleton.elim _ _
  rw [this, CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id]

theorem range_affPt (T : AffOp X₀) : Set.range (affPt s₀ T.unop) = T.unop.1 :=
  IsAffineOpen.range_fromSpec T.unop.2

theorem exists_of_mem_chartOpen (hI : I ^ 2 = 0) (P : S.Presents s i) (T : AffOp X₀) (x : X)
    (hx : x ∈ chartOpen P T) : ∃ x₀ ∈ T.unop.1, i x₀ = x := by
  haveI := P.isOpen T
  change x ∈ ((P.y T).opensRange : Set X) at hx
  rw [Scheme.Hom.coe_opensRange] at hx
  obtain ⟨q, rfl⟩ := hx
  obtain ⟨q₀, rfl⟩ := (S.surjective_spMap_p hI T).surj q
  refine ⟨affPt s₀ T.unop q₀, ?_, ?_⟩
  · have : affPt s₀ T.unop q₀ ∈ Set.range (affPt s₀ T.unop) := Set.mem_range_self _
    rw [range_affPt] at this
    exact this
  · rw [← Scheme.Hom.comp_apply, ← P.red T, Scheme.Hom.comp_apply]

theorem le_preimage_chartOpen (P : S.Presents s i) (T : AffOp X₀) :
    T.unop.1 ≤ i ⁻¹ᵁ chartOpen P T := by
  haveI := P.isOpen T
  intro x₀ hx₀
  have hx' : x₀ ∈ Set.range (affPt s₀ T.unop) := by rw [range_affPt]; exact hx₀
  obtain ⟨q, rfl⟩ := hx'
  change i (affPt s₀ T.unop q) ∈ ((P.y T).opensRange : Set X)
  rw [Scheme.Hom.coe_opensRange, ← Scheme.Hom.comp_apply, ← P.red T, Scheme.Hom.comp_apply]
  exact Set.mem_range_self _

theorem preimage_chartOpen_eq (hI : I ^ 2 = 0) (hinj : Function.Injective i) (P : S.Presents s i)
    (T : AffOp X₀) : i ⁻¹ᵁ chartOpen P T = T.unop.1 := by
  refine le_antisymm (fun x₀ hx₀ ↦ ?_) (le_preimage_chartOpen P T)
  obtain ⟨y₀, hy₀, e⟩ := exists_of_mem_chartOpen hI P T (i x₀) hx₀
  rw [← hinj e]
  exact hy₀

theorem appLE_chartSec (P : S.Presents s i) (T : AffOp X₀) (hT : T.unop.1 ≤ i ⁻¹ᵁ chartOpen P T) :
    i.appLE (chartOpen P T) T.unop.1 hT = chartSec P T ≫ CommRingCat.ofHom (S.p T) := by
  have hf : ⊤ ≤ (affPt s₀ T.unop) ⁻¹ᵁ T.unop.1 := (IsAffineOpen.fromSpec_preimage_self T.unop.2).ge
  have k : (affPt s₀ T.unop).appLE T.unop.1 ⊤ hf ≫ (Scheme.ΓSpecIso Γ(X₀, T.unop.1)).hom = 𝟙 _ :=
    fromSpec_appLE_ΓSpecIso T.unop.2 hf
  have e1 : (⊤ : (Sp (Sec s₀ T.unop.1)).Opens) ≤ (affPt s₀ T.unop ≫ i) ⁻¹ᵁ chartOpen P T :=
    hf.trans (Scheme.Hom.preimage_mono _ hT)
  calc i.appLE (chartOpen P T) T.unop.1 hT
      = i.appLE (chartOpen P T) T.unop.1 hT ≫ ((affPt s₀ T.unop).appLE T.unop.1 ⊤ hf ≫
          (Scheme.ΓSpecIso Γ(X₀, T.unop.1)).hom) := by rw [k, Category.comp_id]
    _ = (affPt s₀ T.unop ≫ i).appLE (chartOpen P T) ⊤ e1 ≫ (Scheme.ΓSpecIso Γ(X₀, T.unop.1)).hom := by
        rw [← Scheme.Hom.appLE_comp_appLE (affPt s₀ T.unop) i _ _ _ hT hf]
        exact (Category.assoc _ _ _).symm
    _ = (spMap (S.p T) ≫ P.y T).appLE (chartOpen P T) ⊤ ((P.red T) ▸ e1) ≫
          (Scheme.ΓSpecIso Γ(X₀, T.unop.1)).hom := by
        rw [appLE_congr (P.red T).symm _ _ e1]
    _ = (chartSec P T ≫ CommRingCat.ofHom (S.p T) : Γ(X, chartOpen P T) ⟶ Γ(X₀, T.unop.1)) := by
        rw [← Scheme.Hom.appLE_comp_appLE _ _ _ _ _ (preimage_chartOpen P T).ge le_top]
        refine (Category.assoc _ _ _).trans ?_
        unfold chartSec
        refine Eq.trans ?_ (Category.assoc _ _ _).symm
        congr 1
        exact specMap_appLE_top _ _

def chartInv (P : S.Presents s i) (T : AffOp X₀) : S.F.obj T →+* Γ(X, chartOpen P T) :=
  (RingEquiv.ofBijective (chartSec P T).hom (ConcreteCategory.bijective_of_isIso (chartSec P T))).symm.toRingHom

theorem chartSec_chartInv (P : S.Presents s i) (T : AffOp X₀) (b : S.F.obj T) :
    (chartSec P T).hom (chartInv P T b) = b :=
  (RingEquiv.ofBijective (chartSec P T).hom (ConcreteCategory.bijective_of_isIso (chartSec P T))).apply_symm_apply b

theorem chartInv_eq_iff (P : S.Presents s i) (T : AffOp X₀) (b : S.F.obj T) (c : Γ(X, chartOpen P T)) :
    chartInv P T b = c ↔ (chartSec P T).hom c = b := by
  constructor
  · rintro rfl; exact chartSec_chartInv P T b
  · rintro rfl
    exact (ConcreteCategory.bijective_of_isIso (chartSec P T)).1 (chartSec_chartInv P T _)

end GlobalTheory.PresCharts


open GlobalTheory.PresCharts in
theorem GlobalTheory.PresCharts.exists_charts : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (S : Sys I π s₀) (X : Scheme.{0}) (s : X ⟶ Sp R) (i : X₀ ⟶ X) (P : S.Presents s i), IsPullback i s₀ s (spMap π) → ∃ (V : AffOp X₀ → X.Opens) (hV : ∀ ⦃T T' : AffOp X₀⦄, (T ⟶ T') → V T' ≤ V T) (hi : ∀ T, T.unop.1 ≤ i ⁻¹ᵁ V T) (e : ∀ T, S.F.obj T →+* Γ(X, V T)), (∀ T, i ⁻¹ᵁ V T = T.unop.1) ∧ (∀ (T T' : AffOp X₀) (a : T ⟶ T') (b : S.F.obj T), e T' (mp S.F a b) = resG X (hV a) (e T b)) ∧ ∀ T b, (i.appLE (V T) T.unop.1 (hi T)).hom (e T b) = S.p T b := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ S X s i P h
  have hinj := injective_of_isPullback hπ h
  refine ⟨chartOpen P, chartOpen_le P, le_preimage_chartOpen P, chartInv P,
    preimage_chartOpen_eq hI hinj P, fun T T' a b ↦ ?_, fun T b ↦ ?_⟩
  · rw [chartInv_eq_iff]
    have := congrArg (fun f ↦ f.hom (chartInv P T b)) (res_chartSec P a)
    refine this.trans ?_
    change (mp S.F a) ((chartSec P T).hom (chartInv P T b)) = _
    rw [chartSec_chartInv]
  · have := congrArg (fun f ↦ f.hom (chartInv P T b)) (appLE_chartSec P T (le_preimage_chartOpen P T))
    refine this.trans ?_
    change S.p T ((chartSec P T).hom (chartInv P T b)) = _
    rw [chartSec_chartInv]
end
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

theorem _root_.GlobalTheory.T.pDivisibleGroup_exists_factor_through_isogeny : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (G Q H : PDivGroup p k) (m : ℕ) (q : G ⟶ Q) (q' : Q ⟶ G) (f : G ⟶ H), q ≫ q' = (p : ℤ_[p]) ^ m • 𝟙 G → q' ≫ q = (p : ℤ_[p]) ^ m • 𝟙 Q → kerIdeal (f.app m) ≤ kerIdeal (q.app m) → ∃ g : Q ⟶ H, q ≫ g = f := by
  first | exact @GlobalTheory.Dieu.exists_comp_eq_of_kerIdeal_le | exact GlobalTheory.Dieu.exists_comp_eq_of_kerIdeal_le | (intros; apply GlobalTheory.Dieu.exists_comp_eq_of_kerIdeal_le <;> assumption)
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem _root_.GlobalTheory.T.finrank_span_pow_pDivGroup_level_le : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0) (G : PDivGroup p K), ∀ r : ℕ, Module.finrank K (Submodule.span K (Set.range fun a : G.A r => a ^ p ^ r)) ≤ (p ^ r) ^ Module.finrank K G.dual.omega := by
  first | exact @GlobalTheory.finrank_span_pow_le | exact GlobalTheory.finrank_span_pow_le | (intros; apply GlobalTheory.finrank_span_pow_le <;> assumption)
end

section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem _root_.GlobalTheory.T.cmType_unit_phase_prod_eq_one_of_congruent_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsCMField E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) (q : ℕ), q.Prime → 2 < q → ¬ q ∣ Nat.card (Units.torsion E) → ∀ u : (𝓞 E)ˣ, (u : 𝓞 E) - 1 ∈ Ideal.span {((q : ℕ) : 𝓞 E)} → ∏ w : InfinitePlace F, ((emb w).1 ((u : 𝓞 E) : E) / ((‖(emb w).1 ((u : 𝓞 E) : E)‖ : ℝ) : ℂ)) = 1 := by
  first | exact @GlobalTheory.weil_unit_phase_prod | exact GlobalTheory.weil_unit_phase_prod | (intros; apply GlobalTheory.weil_unit_phase_prod <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.Cartier
open scoped ComplexOrder ContDiff

namespace GlobalTheory.CurveDens

theorem cHess_apply_eq_ddbar {n : ℕ} {g : ReciprocityTheory.L2DbarEstimates.V n → ℂ} {x : ReciprocityTheory.L2DbarEstimates.V n}
    (hg : ContDiffAt ℝ 2 g x) (j k : Fin n) :
    ReciprocityTheory.L2DbarEstimates.cHess n g x j k =
      ddbar g x (EuclideanSpace.single j 1) (EuclideanSpace.single k 1) := by
  have e : ReciprocityTheory.L2DbarEstimates.wdb n k g = fun y => dbar g y (EuclideanSpace.single k 1) := by
    funext y
    simp only [ReciprocityTheory.L2DbarEstimates.wdb, dbar_apply, ReciprocityTheory.L2DbarEstimates.bas, smul_eq_mul]
    ring
  rw [ddbar_eq_del_dbar hg, del_apply, ReciprocityTheory.L2DbarEstimates.cHess, Matrix.of_apply, e]
  simp only [ReciprocityTheory.L2DbarEstimates.wd, ReciprocityTheory.L2DbarEstimates.bas, smul_eq_mul]
  ring

end GlobalTheory.CurveDens

namespace GlobalTheory.CurveDens

end GlobalTheory.CurveDens
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

def TwoTorsRat {R : Type} [CommRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G] : Prop :=
  ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (x : Over.mk (spMap (algebraMap (FractionRing R) F) ≫ jK R) ⟶ G),
    x * x = 1 → ∃ y : Over.mk (jK R) ⟶ G, x.left = spMap (algebraMap (FractionRing R) F) ≫ y.left

def SplitClosed {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] : Prop :=
  ∃ (X : Type) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X),
    Nonempty (GlobalTheory.UU.TQ (thickObj R (maximalIdeal R) 0 G) X)

end GlobalTheory.Mum
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.kummerReductionChernDefectSection_res : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (U : Scheme.{0}) (u : (Γ(U, ⊤))ˣ), IsUnit (Q : Γ(U, ⊤)) → ∀ (V : Scheme.{0}) (g : V ⟶ U), Sec.res g (GlobalTheory.EtC.RedChern.defectSec Q q U u) = GlobalTheory.EtC.RedChern.defectSec Q q V (Units.map g.appTop.hom.toMonoidHom u) := by
  first
  | exact @GlobalTheory.EtC.RedChern.defectSec_res
  | exact GlobalTheory.EtC.RedChern.defectSec_res
  | (intros; apply GlobalTheory.EtC.RedChern.defectSec_res <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.reducedChernCocycle_deg_one_sub_eq_differential : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (U : Scheme.{0}) (u : (Γ(U, ⊤))ˣ), IsUnit (Q : Γ(U, ⊤)) → ∀ (a : Sec ((res _ (tw Q 1)).X 1) U) (b : Sec ((res _ (tw q 1)).X 1) U), (∀ (V : Scheme.{0}) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ), v ^ Q = Units.map g.appTop.hom.toMonoidHom u → Sec.res g a = Sec.map ((res _ (tw Q 1)).d 0 1) (kumT Q V v)) → (∀ (V : Scheme.{0}) (g : V ⟶ U) (w : (Γ(V, ⊤))ˣ), w ^ q = Units.map g.appTop.hom.toMonoidHom u → Sec.res g b = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q V w)) → (redMap Q q 1).app U 1 a - b = Sec.map ((res _ (tw q 1)).d 0 1) (GlobalTheory.EtC.RedChern.defectSec Q q U u) := by
  first
  | exact @GlobalTheory.EtC.RedChern.red_chern_deg_one
  | exact GlobalTheory.EtC.RedChern.red_chern_deg_one
  | (intros; apply GlobalTheory.EtC.RedChern.red_chern_deg_one <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.reducedChernCocycle_deg_two_sub_eq_defects : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (U : Scheme.{0}) (u₁ u₂ : (Γ(U, ⊤))ˣ), IsUnit (Q : Γ(U, ⊤)) → ∀ (a : Sec ((res _ (tw Q 1)).X 0) U) (b : Sec ((res _ (tw q 1)).X 0) U), (∀ (V : Scheme.{0}) (g : V ⟶ U) (v w : (Γ(V, ⊤))ˣ), v ^ Q = Units.map g.appTop.hom.toMonoidHom u₁ → w ^ Q = Units.map g.appTop.hom.toMonoidHom u₂ → Sec.res g a = kumT Q V v + kumT Q V w - kumT Q V (v * w)) → (∀ (V : Scheme.{0}) (g : V ⟶ U) (v w : (Γ(V, ⊤))ˣ), v ^ q = Units.map g.appTop.hom.toMonoidHom u₁ → w ^ q = Units.map g.appTop.hom.toMonoidHom u₂ → Sec.res g b = kumT q V v + kumT q V w - kumT q V (v * w)) → (redMap Q q 1).app U 0 a - b = GlobalTheory.EtC.RedChern.defectSec Q q U u₂ - GlobalTheory.EtC.RedChern.defectSec Q q U (u₁ * u₂) + GlobalTheory.EtC.RedChern.defectSec Q q U u₁ := by
  first
  | exact @GlobalTheory.RedChern.redMap_cocycle_sub_eq_defects
  | exact GlobalTheory.RedChern.redMap_cocycle_sub_eq_defects
  | (intros; apply GlobalTheory.RedChern.redMap_cocycle_sub_eq_defects <;> assumption)
end
