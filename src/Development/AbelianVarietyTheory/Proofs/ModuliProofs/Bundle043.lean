module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle027
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle031
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.CoverGlue

theorem exists_grpObj_of_cover : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left) (m n : A ⊗ A ⟶ A) (e : Out.baseOver S ⟶ A), iSup U = ⊤ → (∀ i, IsPullback (ψ i) (G i).hom A.hom (U i).ι) → (∀ i (T : Over (U i).toScheme) (x y : T ⟶ G i) (x₀ y₀ : Over.mk (T.hom ≫ (U i).ι) ⟶ A), x₀.left = x.left ≫ ψ i → y₀.left = y.left ≫ ψ i → (lift x₀ y₀ ≫ m).left = (x * y).left ≫ ψ i ∧ (lift x₀ y₀ ≫ n).left = (x⁻¹).left ≫ ψ i) → (∀ i, (1 : Out.baseOver (U i).toScheme ⟶ G i).left ≫ ψ i = (U i).ι ≫ e.left) → ∃ _ : GrpObj A, ∀ i, IsGrpPullback (G i) A (U i).ι (ψ i) := by
  intro S I U A G _ ψ m n e hU hpb hgrp hone

  have hl : ∀ i (T' : Over (U i).toScheme) (a : Over.mk (T'.hom ≫ (U i).ι) ⟶ A),
      ∃ x : T' ⟶ G i, a.left = x.left ≫ ψ i :=
    fun i _ a => GlobalTheory.CoverGlue.exists_lift (hpb i) a
  have hm : ∀ i (T' : Over (U i).toScheme) (a b : Over.mk (T'.hom ≫ (U i).ι) ⟶ A) (x y : T' ⟶ G i),
      a.left = x.left ≫ ψ i → b.left = y.left ≫ ψ i → (lift a b ≫ m).left = (x * y).left ≫ ψ i :=
    fun i T' a b x y ha hb => (hgrp i T' x y a b ha hb).1
  have hn : ∀ i (T' : Over (U i).toScheme) (a b : Over.mk (T'.hom ≫ (U i).ι) ⟶ A) (x y : T' ⟶ G i),
      a.left = x.left ≫ ψ i → b.left = y.left ≫ ψ i → (lift a b ≫ n).left = (x⁻¹).left ≫ ψ i :=
    fun i T' a b x y ha hb => (hgrp i T' x y a b ha hb).2
  obtain ⟨e', he'⟩ : ∃ e' : 𝟙_ (Over S) ⟶ A, e' = e := ⟨e, rfl⟩
  subst he'

  have h1 : ∀ i (T' : Over (U i).toScheme) (p : Over.mk (T'.hom ≫ (U i).ι) ⟶ 𝟙_ (Over S)),
      (p ≫ e').left = (1 : T' ⟶ G i).left ≫ ψ i := by
    intro i T' p
    have hp : p.left = T'.hom ≫ (U i).ι := by
      have h := Over.w p
      first | simpa using h | simpa [Over.tensorUnit_hom] using h | exact (Category.comp_id _).symm.trans h
    have hT : (toUnit T').left = T'.hom := by
      have h := Over.w (toUnit T')
      first | simpa using h | simpa [Over.tensorUnit_hom] using h | exact (Category.comp_id _).symm.trans h
    have h1' : (1 : T' ⟶ G i) = toUnit T' ≫ (1 : Out.baseOver (U i).toScheme ⟶ G i) := by
      rw [CategoryTheory.Hom.one_def, CategoryTheory.Hom.one_def, ← Category.assoc]
      first | exact congrArg (· ≫ _) (toUnit_unique _ _) | (congr 1; exact toUnit_unique _ _)
    rw [h1']
    first
      | (rw [Over.comp_left, Over.comp_left, Category.assoc, hone i, hp, hT, Category.assoc])
      | (simp only [Over.comp_left, Category.assoc, hone i, hp, hT])
  have ax1 : e' ▷ A ≫ m = (λ_ A).hom := by
    apply GlobalTheory.CoverGlue.over_ext hU
    intro i T' r
    obtain ⟨p, c, rfl⟩ : ∃ p c, r = lift p c := ⟨_, _, (lift_comp_fst_snd r).symm⟩
    obtain ⟨z, hz⟩ := hl i T' c
    simp only [lift_whiskerRight_assoc, leftUnitor_hom, lift_snd]
    apply Over.OverMorphism.ext
    rw [hm i T' _ _ 1 z (h1 i T' p) hz, _root_.one_mul, hz]
  have ax2 : A ◁ e' ≫ m = (ρ_ A).hom := by
    apply GlobalTheory.CoverGlue.over_ext hU
    intro i T' r
    obtain ⟨c, p, rfl⟩ : ∃ c p, r = lift c p := ⟨_, _, (lift_comp_fst_snd r).symm⟩
    obtain ⟨z, hz⟩ := hl i T' c
    simp only [lift_whiskerLeft_assoc, rightUnitor_hom, lift_fst]
    apply Over.OverMorphism.ext
    rw [hm i T' _ _ z 1 hz (h1 i T' p), _root_.mul_one, hz]
  have ax3 : m ▷ A ≫ m = (α_ A A A).hom ≫ A ◁ m ≫ m := by
    apply GlobalTheory.CoverGlue.over_ext hU
    intro i T' r
    obtain ⟨q, c, rfl⟩ : ∃ q c, r = lift q c := ⟨_, _, (lift_comp_fst_snd r).symm⟩
    obtain ⟨a, b, rfl⟩ : ∃ a b, q = lift a b := ⟨_, _, (lift_comp_fst_snd q).symm⟩
    obtain ⟨x, hx⟩ := hl i T' a
    obtain ⟨y, hy⟩ := hl i T' b
    obtain ⟨z, hz⟩ := hl i T' c
    simp only [lift_whiskerRight_assoc, lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc]
    apply Over.OverMorphism.ext
    rw [hm i T' _ _ (x * y) z (hm i T' a b x y hx hy) hz,
      hm i T' _ _ x (y * z) hx (hm i T' b c y z hy hz), _root_.mul_assoc]
  have ax4 : lift (lift (𝟙 A) (𝟙 A) ≫ n) (𝟙 A) ≫ m = toUnit A ≫ e' := by
    apply GlobalTheory.CoverGlue.over_ext hU
    intro i T' r
    obtain ⟨z, hz⟩ := hl i T' r
    simp only [comp_lift_assoc, Category.comp_id]
    rw [← Category.assoc r (toUnit A) e']
    apply Over.OverMorphism.ext
    rw [hm i T' _ _ z⁻¹ z (hn i T' r r z z hz hz) hz, _root_.inv_mul_cancel, h1 i T' (r ≫ toUnit A)]
  have ax5 : lift (𝟙 A) (lift (𝟙 A) (𝟙 A) ≫ n) ≫ m = toUnit A ≫ e' := by
    apply GlobalTheory.CoverGlue.over_ext hU
    intro i T' r
    obtain ⟨z, hz⟩ := hl i T' r
    simp only [comp_lift_assoc, comp_lift, Category.comp_id]
    rw [← Category.assoc r (toUnit A) e']
    apply Over.OverMorphism.ext
    rw [hm i T' _ _ z z⁻¹ hz (hn i T' r r z z hz hz), _root_.mul_inv_cancel, h1 i T' (r ≫ toUnit A)]
  let inst : GrpObj A :=
    { one := e', mul := m, inv := lift (𝟙 A) (𝟙 A) ≫ n,
      one_mul := ax1, mul_one := ax2, mul_assoc := ax3, left_inv := ax4, right_inv := ax5 }
  refine ⟨inst, fun i => ⟨hpb i, fun T x y x₀ y₀ hx hy => ?_⟩⟩
  rw [CategoryTheory.Hom.mul_def]
  exact hm i T x₀ y₀ x y hx hy

end GlobalTheory.CoverGlue
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.CoverGlue

theorem of_isPullback_cover (Q : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget Q]
    {S X : Scheme.{0}} {I : Type} {U : I → S.Opens} (hU : iSup U = ⊤) {Z : I → Scheme.{0}} {p : X ⟶ S}
    {q : ∀ i, Z i ⟶ (U i).toScheme} {ψ : ∀ i, Z i ⟶ X} (h : ∀ i, IsPullback (ψ i) (q i) p (U i).ι)
    (hq : ∀ i, Q (q i)) : Q p := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top U hU fun i => ?_
  have hr := (isPullback_morphismRestrict p (U i)).flip
  rw [← IsPullback.isoIsPullback_hom_snd _ _ hr (h i)]
  exact (MorphismProperty.cancel_left_of_respectsIso Q _ _).2 (hq i)

theorem isCommMonObj_of_cover {S : Scheme.{0}} {I : Type} {U : I → S.Opens} (hU : iSup U = ⊤) {A : Over S}
    [GrpObj A] {G : ∀ i, Over (U i).toScheme} [∀ i, GrpObj (G i)] {ψ : ∀ i, (G i).left ⟶ A.left}
    (h : ∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) (hc : ∀ i, IsCommMonObj (G i)) : IsCommMonObj A := by
  refine (isCommMonObj_iff_isMulCommutative A).2 fun T => ⟨⟨fun x y => ?_⟩⟩
  refine over_ext hU fun i T' r => ?_
  have := hc i
  rw [MonObj.comp_mul, MonObj.comp_mul]
  obtain ⟨a, ha⟩ := exists_lift (h i).1 (r ≫ x)
  obtain ⟨b, hb⟩ := exists_lift (h i).1 (r ≫ y)
  ext1
  rw [(h i).2 T' a b _ _ ha hb, (h i).2 T' b a _ _ hb ha, mul_comm a b]

theorem isAbelianScheme_and_relDim_of_cover : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) [GrpObj A] (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left), iSup U = ⊤ → (∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) → ((∀ i, IsAbelianScheme (G i)) → IsAbelianScheme A) ∧ ∀ g : ℕ, (∀ i, SmoothOfRelativeDimension g (G i).hom) → SmoothOfRelativeDimension g A.hom := by
  intro S I U A _ G _ ψ hU h
  refine ⟨fun hab => ?_, fun g hg => ?_⟩
  · constructor
    · exact isCommMonObj_of_cover hU h fun i => (hab i).comm
    · exact @of_isPullback_cover @Smooth (HasRingHomProperty.instIsZariskiLocalAtTarget @Smooth) _ _ _ _ hU _ _ _ _
        (fun i => (h i).1) fun i => (hab i).smooth
    · exact of_isPullback_cover @IsProper hU (fun i => (h i).1) fun i => (hab i).proper
    · refine ⟨?_⟩
      exact of_isPullback_cover (geometrically (ConnectedSpace ·)) hU (fun i => (h i).1)
        fun i => (hab i).geomConnected.geometrically_connectedSpace
  · exact @of_isPullback_cover (@SmoothOfRelativeDimension g)
      (HasRingHomProperty.instIsZariskiLocalAtTarget (@SmoothOfRelativeDimension g)) _ _ _ _ hU _ _ _ _
      (fun i => (h i).1) hg

end GlobalTheory.CoverGlue
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

noncomputable section

namespace GlobalTheory.EpsThick

theorem existsUnique_of_isPushout {R : Type} [CommRing R] {A A' : CommRingCat.{0}} (s : R →+* A) (p : A ⟶ A')
    (s' : DualNumber R →+* A')
    (H : IsPushout (CommRingCat.ofHom s) (CommRingCat.ofHom (algebraMap R (DualNumber R))) p
      (CommRingCat.ofHom s')) :
    Function.Bijective fun ab : A × A => p.hom ab.1 + s' DualNumber.eps * p.hom ab.2 := by
  let _ : Algebra R A := s.toAlgebra
  let _ : Algebra A A' := p.hom.toAlgebra
  let _ : Algebra (DualNumber R) A' := s'.toAlgebra
  let _ : Algebra R A' := (s'.comp (algebraMap R (DualNumber R))).toAlgebra
  have : IsScalarTower R (DualNumber R) A' := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower R A A' := .of_algebraMap_eq fun r => (congrArg (fun q => q.hom r) H.w).symm
  have h : Algebra.IsPushout R (DualNumber R) A A' := (CommRingCat.isPushout_iff_isPushout.mp H).symm
  let e : DualNumber R ⊗[R] A ≃+ A' := h.out.equiv.toAddEquiv
  have he : ∀ c v, e (c ⊗ₜ v) = s' c * p.hom v :=
    fun c v => (h.out.equiv_tmul c v).trans (Algebra.smul_def _ _)
  have key : ∀ ab : A × A, p.hom ab.1 + s' DualNumber.eps * p.hom ab.2 =
      e ((1 : DualNumber R) ⊗ₜ ab.1 + (DualNumber.eps : DualNumber R) ⊗ₜ ab.2) := fun ab => by
    rw [map_add (f := _), he, he, map_one, _root_.one_mul]
  simp only [key]
  refine e.bijective.comp (f := fun ab : A × A =>
    ((1 : DualNumber R) ⊗ₜ[R] ab.1 + (DualNumber.eps : DualNumber R) ⊗ₜ[R] ab.2)) ⟨fun x y hxy => ?_, fun t => ?_⟩
  · have h1 := congrArg ((TensorProduct.lid R A).toLinearMap ∘ₗ
      ((TrivSqZeroExt.fstHom R R R).toLinearMap).rTensor A) hxy
    have h2 := congrArg ((TensorProduct.lid R A).toLinearMap ∘ₗ
      (TrivSqZeroExt.sndHom R R).rTensor A) hxy
    ext
    · simpa using h1
    · simpa using h2
  · induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul c v =>
      refine ⟨(c.fst • v, c.snd • v), ?_⟩
      dsimp only
      rw [← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul, ← TensorProduct.add_tmul]
      congr 1
      ext <;> simp
    | add x y hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      refine ⟨a + b, ?_⟩
      simp only [Prod.fst_add, Prod.snd_add, TensorProduct.tmul_add]
      abel

variable {R : Type} [CommRing R] {Y Y' : Scheme.{0}} {q : Y ⟶ Sp R} {π : Y' ⟶ Sp (DualNumber R)} {ρ : Y' ⟶ Y}

def comb (π : Y' ⟶ Sp (DualNumber R)) (ρ : Y' ⟶ Y) (O : Y.Opens) (ab : Γ(Y, O) × Γ(Y, O)) : Γ(Y', ρ ⁻¹ᵁ O) :=
  (ρ.app O).hom ab.1 + constFn π _ DualNumber.eps * (ρ.app O).hom ab.2

theorem comb_bijective_of_isAffineOpen (H : IsPullback ρ π q (spMap (algebraMap R (DualNumber R))))
    {U : Y.Opens} (hU : IsAffineOpen U) : Function.Bijective (comb π ρ U) := by
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := U) (UY := ρ ⁻¹ᵁ U) le_top
    le_top (by simp)).mp (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hU)
  refine existsUnique_of_isPushout
    ((Scheme.ΓSpecIso (.of R)).inv ≫ q.appLE ⊤ U (fun _ _ => trivial)).hom (ρ.app U)
    ((Scheme.ΓSpecIso (.of (DualNumber R))).inv ≫ π.appLE ⊤ (ρ ⁻¹ᵁ U) (fun _ _ => trivial)).hom ?_
  refine po.of_iso (Scheme.ΓSpecIso (.of R)) (Iso.refl _) (Scheme.ΓSpecIso (.of (DualNumber R))) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · simp
  · rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  · simp [Scheme.Hom.app_eq_appLE]
  · simp

theorem res_comb {U O : Y.Opens} (h : U ≤ O) (ab : Γ(Y, O) × Γ(Y, O)) :
    (Y'.presheaf.map (homOfLE (ρ.preimage_mono h)).op).hom (comb π ρ O ab) =
      comb π ρ U ((Y.presheaf.map (homOfLE h).op).hom ab.1, (Y.presheaf.map (homOfLE h).op).hom ab.2) := by
  have h1 : ∀ a, (Y'.presheaf.map (homOfLE (ρ.preimage_mono h)).op).hom ((ρ.app O).hom a) =
      (ρ.app U).hom ((Y.presheaf.map (homOfLE h).op).hom a) := fun a =>
    (congrArg (fun φ => φ.hom a) (ρ.naturality (homOfLE h).op)).symm
  have h2 : (Y'.presheaf.map (homOfLE (ρ.preimage_mono h)).op).hom (constFn π _ DualNumber.eps) =
      constFn π (ρ ⁻¹ᵁ U) DualNumber.eps := by
    exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (.of (DualNumber R))).inv.hom DualNumber.eps))
      (π.appLE_map (U := ⊤) (V := ρ ⁻¹ᵁ O) le_top (homOfLE (ρ.preimage_mono h)).op)
  simp only [comb, map_add (f := _), map_mul, h1, h2]

theorem le_iSup_affine (O : Y.Opens) :
    O ≤ ⨆ U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O}, U.1 := by
  intro x hx
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUO⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hx O.isOpen
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U, hU, hUO⟩, hxU⟩

theorem comb_injective (H : IsPullback ρ π q (spMap (algebraMap R (DualNumber R)))) (O : Y.Opens) :
    Function.Injective (comb π ρ O) := by
  intro x y hxy
  have key : ∀ U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O},
      ((Y.presheaf.map (homOfLE U.2.2).op).hom x.1, (Y.presheaf.map (homOfLE U.2.2).op).hom x.2) =
      ((Y.presheaf.map (homOfLE U.2.2).op).hom y.1, (Y.presheaf.map (homOfLE U.2.2).op).hom y.2) := fun U => by
    apply (comb_bijective_of_isAffineOpen H U.2.1).1
    rw [← res_comb, ← res_comb, hxy]
  ext
  · exact Y.sheaf.eq_of_locally_eq' _ O (fun U => homOfLE U.2.2) (le_iSup_affine O) _ _
      fun U => congrArg Prod.fst (key U)
  · exact Y.sheaf.eq_of_locally_eq' _ O (fun U => homOfLE U.2.2) (le_iSup_affine O) _ _
      fun U => congrArg Prod.snd (key U)

theorem comb_surjective (H : IsPullback ρ π q (spMap (algebraMap R (DualNumber R)))) (O : Y.Opens) :
    Function.Surjective (comb π ρ O) := by
  intro F
  choose s hs using fun U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O} =>
    (comb_bijective_of_isAffineOpen H U.2.1).2 ((Y'.presheaf.map (homOfLE (ρ.preimage_mono U.2.2)).op).hom F)
  have key : ∀ U V : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O},
      ((Y.presheaf.map (homOfLE (inf_le_left : U.1 ⊓ V.1 ≤ U.1)).op).hom (s U).1,
        (Y.presheaf.map (homOfLE (inf_le_left : U.1 ⊓ V.1 ≤ U.1)).op).hom (s U).2) =
      ((Y.presheaf.map (homOfLE (inf_le_right : U.1 ⊓ V.1 ≤ V.1)).op).hom (s V).1,
        (Y.presheaf.map (homOfLE (inf_le_right : U.1 ⊓ V.1 ≤ V.1)).op).hom (s V).2) := fun U V => by
    apply comb_injective H
    rw [← res_comb, ← res_comb, hs, hs, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
      ← Functor.map_comp, ← Functor.map_comp]
    rfl
  obtain ⟨a, ha, -⟩ := Y.sheaf.existsUnique_gluing' _ O (fun U => homOfLE U.2.2) (le_iSup_affine O)
    (fun U => (s U).1) fun U V => congrArg Prod.fst (key U V)
  obtain ⟨b, hb, -⟩ := Y.sheaf.existsUnique_gluing' _ O (fun U => homOfLE U.2.2) (le_iSup_affine O)
    (fun U => (s U).2) fun U V => congrArg Prod.snd (key U V)
  refine ⟨(a, b), ?_⟩
  refine Y'.sheaf.eq_of_locally_eq' (fun U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O} => ρ ⁻¹ᵁ U.1) _
    (fun U => homOfLE (ρ.preimage_mono U.2.2)) ?_ _ _ fun U => ?_
  · rw [← Scheme.Hom.preimage_iSup]
    exact ρ.preimage_mono (le_iSup_affine O)
  · refine (res_comb U.2.2 (a, b)).trans (Eq.trans ?_ (hs U))
    exact congrArg _ (Prod.ext (ha U) (hb U))

theorem isPullback_special (H : IsPullback ρ π q (spMap (algebraMap R (DualNumber R)))) {j : Y ⟶ Y'}
    (h₁ : j ≫ ρ = 𝟙 Y) (h₂ : j ≫ π = q ≫ spMap (TrivSqZeroExt.fstHom R R R).toRingHom) :
    IsPullback j q π (spMap (TrivSqZeroExt.fstHom R R R).toRingHom) := by
  refine (IsPullback.of_bot ?_ h₂.symm H.flip).flip
  have : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (algebraMap R (DualNumber R)) = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
  rw [h₁, this]
  exact IsPullback.of_vert_isIso ⟨by simp⟩

theorem surjective_spMap_fst : Surjective (spMap (TrivSqZeroExt.fstHom R R R).toRingHom) := by
  refine ⟨fun x => ?_⟩
  have h : x ∈ Set.range (PrimeSpectrum.comap (TrivSqZeroExt.fstHom R R R).toRingHom) := by
    rw [range_comap_of_surjective _ _ (fun r => ⟨TrivSqZeroExt.inl r, rfl⟩)]
    intro z hz
    have hz' : z.fst = 0 := hz
    refine x.isPrime.mem_of_pow_mem 2 ?_
    have : z ^ 2 = 0 := by
      ext <;> simp [pow_two, hz']
    rw [this]
    exact zero_mem _
  exact h

theorem thickening_functions : ∀ (Y Y' : Scheme.{0}) (q : Y ⟶ Sp ℂ) (π : Y' ⟶ Sp (DualNumber ℂ)) (ρ : Y' ⟶ Y) (j : Y ⟶ Y'), IsPullback ρ π q (spMap (algebraMap ℂ (DualNumber ℂ))) → j ≫ ρ = 𝟙 Y → j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) → (∀ O : Y'.Opens, ρ ⁻¹ᵁ (j ⁻¹ᵁ O) = O) ∧ IsPullback j q π (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ∧ ∀ (O : Y.Opens) (F : Γ(Y', ρ ⁻¹ᵁ O)), ∃! ab : Γ(Y, O) × Γ(Y, O), F = (ρ.app O).hom ab.1 + constFn π _ DualNumber.eps * (ρ.app O).hom ab.2 := by
  intro Y Y' q π ρ j H h₁ h₂
  have P := isPullback_special H h₁ h₂
  refine ⟨fun O => ?_, P, fun O F => ?_⟩
  · have hj : Surjective j := MorphismProperty.of_isPullback (P := @Surjective) P.flip surjective_spMap_fst
    ext x
    obtain ⟨y, rfl⟩ := hj.surj x
    have : ρ (j y) = y := by rw [← Scheme.Hom.comp_apply, h₁]; rfl
    change j (ρ (j y)) ∈ O ↔ j y ∈ O
    rw [this]
  · obtain ⟨ab, hab⟩ := comb_surjective H O F
    exact ⟨ab, hab.symm, fun y hy => comb_injective H O (hy.symm.trans hab.symm)⟩

end GlobalTheory.EpsThick
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.ConjBound

open GlobalTheory.EigenNorm

variable {g : ℕ}

theorem im_adjoint_of_span (Hm : Matrix (Fin g) (Fin g) ℂ) (t u : Fin g → ℂ) (S : Set (Fin g → ℂ))
    (hS : Submodule.span ℝ S = ⊤)
    (h : ∀ z ∈ S, ∀ w ∈ S, (hermForm Hm (t * z) w).im = (hermForm Hm z (u * w)).im) (z w : Fin g → ℂ) :
    (hermForm Hm (t * z) w).im = (hermForm Hm z (u * w)).im := by
  have hz : z ∈ Submodule.span ℝ S := hS ▸ Submodule.mem_top
  have hw : w ∈ Submodule.span ℝ S := hS ▸ Submodule.mem_top
  have hr : ∀ (r : ℝ) (v : Fin g → ℂ), r • v = (r : ℂ) • v := fun r v => by
    funext i; simp
  induction hz, hw using Submodule.span_induction₂ with
  | mem_mem z w hz hw => exact h z hz w hw
  | zero_left w _ => simp [hermForm]
  | zero_right z _ => simp [hermForm]
  | add_left z z' w _ _ _ h1 h2 =>
    rw [mul_add, hermForm_add_left, hermForm_add_left, Complex.add_im, Complex.add_im, h1, h2]
  | add_right z w w' _ _ _ h1 h2 =>
    rw [mul_add, hermForm_add_right, hermForm_add_right, Complex.add_im, Complex.add_im, h1, h2]
  | smul_left r z w _ _ h1 =>
    rw [hr, mul_smul_comm, hermForm_smul_left, hermForm_smul_left, Complex.im_ofReal_mul, Complex.im_ofReal_mul, h1]
  | smul_right r z w _ _ h1 =>
    rw [hr, mul_smul_comm, hermForm_smul_right, hermForm_smul_right, Complex.conj_ofReal, Complex.im_ofReal_mul,
      Complex.im_ofReal_mul, h1]

theorem hermForm_eq_sum (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    hermForm Hm z w = ∑ i, ∑ j, z i * Hm i j * starRingEnd ℂ (w j) := by
  simp [hermForm, dotProduct, Matrix.mulVec, Finset.mul_sum, _root_.mul_assoc]

theorem entry_comm (Hm : Matrix (Fin g) (Fin g) ℂ) (t : Fin g → ℂ)
    (h : ∀ z w, (hermForm Hm (t * z) w).im = (hermForm Hm z (star t * w)).im) (i j : Fin g) :
    t i * Hm i j = Hm i j * t j := by
  have key : ∀ s : ℂ, (s * (t i * Hm i j)).im = (s * (Hm i j * t j)).im := fun s => by
    have := h (Pi.single i s) (Pi.single j 1)
    rw [hermForm_eq_sum, hermForm_eq_sum] at this
    simp only [Pi.mul_apply, Pi.single_apply, Pi.star_apply, mul_ite, mul_zero, _root_.mul_one, ite_mul, zero_mul,
      apply_ite (starRingEnd ℂ), map_zero, map_one, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      RCLike.star_def, Complex.conj_conj] at this
    convert this using 2 <;> ring
  have h1 := key 1
  have h2 := key Complex.I
  rw [_root_.one_mul, _root_.one_mul] at h1
  rw [Complex.I_mul_im, Complex.I_mul_im] at h2
  exact Complex.ext h2 h1

theorem re_lt_of_comm (Hm : Matrix (Fin g) (Fin g) ℂ) (t : Fin g → ℂ) (κ : ℝ)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re)
    (hc : ∀ i j, t i * Hm i j = Hm i j * t j) (ht : ∀ i, ‖t i‖ ^ 2 < κ) (y : Fin g → ℂ) (hy : y ≠ 0) :
    (hermForm Hm (t * y) (t * y)).re < κ * (hermForm Hm y y).re := by
  let s : Fin g → ℂ := fun i => (Real.sqrt (κ - ‖t i‖ ^ 2) : ℝ)
  have hs0 : ∀ i, s i ≠ 0 := fun i => by
    have : 0 < Real.sqrt (κ - ‖t i‖ ^ 2) := Real.sqrt_pos.2 (sub_pos.2 (ht i))
    exact Complex.ofReal_ne_zero.2 this.ne'
  have hsy : s * y ≠ 0 := fun h0 => hy (by
    funext i
    have := congrFun h0 i
    simpa [hs0 i] using this)
  have hss : ∀ i, s i * starRingEnd ℂ (s i) + t i * starRingEnd ℂ (t i) = κ := fun i => by
    rw [Complex.mul_conj', Complex.mul_conj']
    have : ‖s i‖ ^ 2 = κ - ‖t i‖ ^ 2 := by
      simp only [s, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      exact Real.sq_sqrt (sub_pos.2 (ht i)).le
    rw [← Complex.ofReal_pow, this]
    push_cast; ring
  have hsum : hermForm Hm (s * y) (s * y) + hermForm Hm (t * y) (t * y) = κ * hermForm Hm y y := by
    simp only [hermForm_eq_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases h0 : Hm i j = 0
    · simp [h0]
    · have hij : t i = t j := by
        have := hc i j
        rw [mul_comm] at this
        exact mul_left_cancel₀ h0 this
      have hsij : s i = s j := by simp only [s, hij]
      simp only [Pi.mul_apply, map_mul, hij, hsij, ← hss j]
      ring
  have h1 := hpos _ hsy
  have h2 := congrArg Complex.re hsum
  rw [Complex.add_re, Complex.re_ofReal_mul] at h2
  linarith

theorem exists_action_lt :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Q : D.La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (a : 𝓞 E) (κ : ℕ), (∀ (c : 𝓞 E) x i, Q (c • x) i = ty i (c : E) * Q x i) → (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = D.EF x y) → (∀ τ : E →+* ℂ, ‖τ (a : E)‖ ^ 2 < κ) → ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q (a • x)) ∧ ∀ y, y ≠ 0 → (hermForm Hm (F y) (F y)).re < κ * (hermForm Hm y y).re := by
  intro E _ _ _ H D g ty Q Hm a κ hlin ⟨_, _, hspan, _, hpos, him⟩ hκ
  let t : Fin g → ℂ := fun i => ty i (a : E)
  have h1 : ∀ x, t * Q x = Q (a • x) := fun x => funext fun i => (hlin a x i).symm
  have h2 : ∀ x, star t * Q x = Q (H.bar a • x) := fun x => funext fun i => by
    rw [hlin, H.bar_eq, IsCMField.complexEmbedding_complexConj]; rfl
  refine ⟨LinearMap.mulLeft ℂ t, h1, fun y hy => ?_⟩
  refine re_lt_of_comm Hm t κ hpos (entry_comm Hm t (im_adjoint_of_span Hm t (star t) _ hspan ?_))
    (fun i => hκ (ty i)) y hy
  rintro _ ⟨x, rfl⟩ _ ⟨x', rfl⟩
  rw [h1, h2, him, him, D.adj]

end GlobalTheory.ConjBound
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.exists_cechData_pullback_of_lineBundle_on_open : ∀ (X Y : Scheme.{0}) (ψ : Y ⟶ X) [IsOpenImmersion ψ] (L : LB Y), L.IsLB → ∃ M : LB X, ⨆ a, M.U a = ψ.opensRange ∧ (∀ (a : M.ι) (x : X), x ∈ M.U a → gm (𝟙 X) x (M.U a ⊓ M.U a) (M.g a a) = 1) ∧ (M.pull ψ).IsLB ∧ LBIso L (M.pull ψ) := by
  first | exact @GlobalTheory.LBPush.exists_push | exact GlobalTheory.LBPush.exists_push | (intros; apply GlobalTheory.LBPush.exists_push <;> assumption)
end
