module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002
public import Development.AbelianVarietyTheory.BlockTheory.AbelianSchemeLaw.MultiplicationEtaleTorsion
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.Torus2GammaBijective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.QSurjective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.ExtremalEpi
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
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.TorusInj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MulLawsCompare

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationEtaleTorsion


variable {S : Scheme.{0}}

theorem mulN_eq_mulA (A : Over S) [GrpObj A] (n : ℕ) : mulN A n = mulA A n := by
  rw [mulA, ← comp_mulN, Category.id_comp]

theorem finrank_mulN_eq_card (A : Over S) [GrpObj A] [IsCommMonObj A] (n : ℕ)
    [IsFinite (mulN A n).left] [Etale (mulN A n).left] [Surjective (mulN A n).left]
    {k : Type} [Field k] [IsAlgClosed k] (t : Spec (CommRingCat.of k) ⟶ A.left)
    (z : Spec (CommRingCat.of k)) :
    (mulN A n).left.finrank (t z) =
      Nat.card {y : Over.mk (t ≫ A.hom) ⟶ A // y ^ n = 1} := by
  obtain ⟨-, hc⟩ := GlobalTheory.FinEt.card_points_eq_finrank (mulN A n).left t z
  have h1 : 1 ≤ (mulN A n).left.finrank (t z) :=
    (Scheme.Hom.one_le_finrank_iff_surjective (mulN A n).left).2 inferInstance _
  rw [← hc] at h1 ⊢
  let t' : Over.mk (t ≫ A.hom) ⟶ A := Over.homMk t rfl
  let E : {x : Spec (CommRingCat.of k) ⟶ A.left // x ≫ (mulN A n).left = t} ≃
      {y : Over.mk (t ≫ A.hom) ⟶ A // y ^ n = t'} :=
    { toFun := fun x => ⟨Over.homMk x.1 (by
          have := x.2 =≫ A.hom
          rw [Category.assoc, Over.w] at this
          exact this), by
        rw [← comp_mulN]
        ext
        exact x.2⟩
      invFun := fun y => ⟨y.1.left, by
        have := y.2
        rw [← comp_mulN] at this
        exact congrArg (fun f => f.left) this⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  obtain ⟨x₀⟩ := (Nat.card_pos_iff.1 h1).1
  obtain ⟨y₀, hy₀⟩ := E x₀
  rw [Nat.card_congr E]
  refine Nat.card_congr ((Equiv.mulRight y₀⁻¹).subtypeEquiv fun y => ?_)
  rw [Equiv.coe_mulRight, mul_pow, inv_pow, hy₀, mul_inv_eq_one]

end GlobalTheory.MulLawsCompare
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DivisibleHom

variable {S : Scheme.{0}}


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {S : Scheme.{0}} in
theorem _root_.GlobalTheory.DivisibleHom.cancel_of_flat_surjective {X Y Z : Over S} (e : X ⟶ Y) [Flat e.left]
    [Surjective e.left] {f g : Y ⟶ Z} (h : e ≫ f = e ≫ g) : f = g := by
  haveI := Flat.epi_of_flat_of_surjective e.left
  ext1
  rw [← cancel_epi e.left]
  simpa using congrArg CommaMorphism.left h


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {S : Scheme.{0}} in
theorem _root_.GlobalTheory.DivisibleHom.exists_lift_point {A A' T : Over S} (m : A' ⟶ A) [Flat m.left]
    [Surjective m.left] (y : T ⟶ A) :
    ∃ (T' : Over S) (e : T' ⟶ T) (x : T' ⟶ A'), Flat e.left ∧ Surjective e.left ∧
      x ≫ m = e ≫ y := by
  refine ⟨Over.mk (pullback.snd m.left y.left ≫ T.hom), Over.homMk (pullback.snd m.left y.left) rfl,
    Over.homMk (pullback.fst m.left y.left) ?_, ?_, ?_, ?_⟩
  · show pullback.fst m.left y.left ≫ A'.hom = pullback.snd m.left y.left ≫ T.hom
    rw [← Over.w m, ← Category.assoc, pullback.condition, Category.assoc, Over.w y]
  · show Flat (pullback.snd m.left y.left)
    infer_instance
  · show Surjective (pullback.snd m.left y.left)
    infer_instance
  · ext1
    simp [pullback.condition]


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {S : Scheme.{0}} in
theorem _root_.GlobalTheory.DivisibleHom.isMonHom_of_mul_points {G H : Over S} [GrpObj G] [GrpObj H] (e : G ⟶ H)
    (mul : ∀ (T : Over S) (x y : T ⟶ G), (x * y) ≫ e = (x ≫ e) * (y ≫ e)) : IsMonHom e := by
  have hone : (1 : 𝟙_ (Over S) ⟶ G) ≫ e = 1 := by
    have h := mul (𝟙_ (Over S)) 1 1
    rw [_root_.mul_one] at h
    simpa using h
  have hG : (η : 𝟙_ (Over S) ⟶ G) = 1 := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  have hH : (η : 𝟙_ (Over S) ⟶ H) = 1 := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  have h := mul (G ⊗ G) (fst G G) (snd G G)
  rw [Hom.mul_def, lift_fst_snd, Category.id_comp, Hom.mul_def] at h
  have ht : lift (fst G G ≫ e) (snd G G ≫ e) = e ⊗ₘ e := by ext <;> simp
  refine ⟨?_, ?_⟩
  · rw [hG, hH, hone]
  · rw [h, ht]

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {S : Scheme.{0}} in
theorem _root_.GlobalTheory.DivisibleHom.comp_mulA {A T : Over S} [GrpObj A] (x : T ⟶ A) (n : ℕ) :
    x ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A n = x ^ n := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA
  rw [comp_pow, Category.comp_id]

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {S : Scheme.{0}} in
theorem _root_.GlobalTheory.DivisibleHom.mulA_comp {A B : Over S} [GrpObj A] [GrpObj B] (u : A ⟶ B) [IsMonHom u]
    (n : ℕ) : _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A n ≫ u = u ^ n := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA
  rw [pow_comp, Category.id_comp]


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {S : Scheme.{0}} in
theorem _root_.GlobalTheory.DivisibleHom.exists_factor {A B : Over S} [GrpObj A] [IsCommMonObj A]
    [GrpObj B] (M : ℕ)
    [QuasiCompact (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M).left] [Flat (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M).left] [Surjective (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M).left]
    (u : A ⟶ B) [IsMonHom u] (hu : ∀ (T : Over S) (x : T ⟶ A), x ^ M = 1 → x ≫ u = 1) :
    ∃ φ : A ⟶ B, _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M ≫ φ = u := by
  have key : ∀ {Z : Scheme.{0}} (g₁ g₂ : Z ⟶ A.left),
      g₁ ≫ (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M).left = g₂ ≫ (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M).left → g₁ ≫ u.left = g₂ ≫ u.left := by
    intro Z g₁ g₂ hg
    have hw : g₂ ≫ A.hom = g₁ ≫ A.hom := by
      rw [← Over.w (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M), ← Category.assoc, ← hg, Category.assoc]
    let x₁ : Over.mk (g₁ ≫ A.hom) ⟶ A := Over.homMk g₁ rfl
    let x₂ : Over.mk (g₁ ≫ A.hom) ⟶ A := Over.homMk g₂ hw
    have hx : x₁ ^ M = x₂ ^ M := by
      rw [← _root_.GlobalTheory.DivisibleHom.comp_mulA, ← _root_.GlobalTheory.DivisibleHom.comp_mulA]
      ext1
      simpa [x₁, x₂] using hg
    have h1 : (x₁ * x₂⁻¹) ^ M = 1 := by rw [mul_pow, inv_pow, hx, mul_inv_cancel]
    have h3 : IsMonHom.monoidHom u _ (x₁ * x₂⁻¹) = 1 := hu _ _ h1
    rw [map_mul, map_inv, mul_inv_eq_one] at h3
    simpa [x₁, x₂] using congrArg CommaMorphism.left h3
  refine ⟨Over.homMk (EffectiveEpi.desc _ _ key) ?_, ?_⟩
  · rw [← cancel_epi (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M).left, ← Category.assoc, EffectiveEpi.fac, Over.w u,
      Over.w (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M)]
  · ext1
    simp [EffectiveEpi.fac]


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {S : Scheme.{0}} in
theorem _root_.GlobalTheory.DivisibleHom.isMonHom_of_factor {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B]
    (M : ℕ) [Flat (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M).left] [Surjective (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M).left]
    (φ : A ⟶ B) [IsMonHom (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M ≫ φ)] : IsMonHom φ := by
  have hmm : ∀ (T : Over S) (a b : T ⟶ A),
      (a * b) ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M = (a ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M) * (b ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M) := by
    intro T a b
    simp only [_root_.GlobalTheory.DivisibleHom.comp_mulA, mul_pow]
  apply _root_.GlobalTheory.DivisibleHom.isMonHom_of_mul_points
  intro T x y
  obtain ⟨T₁, e₁, x', he₁, hs₁, hx'⟩ := _root_.GlobalTheory.DivisibleHom.exists_lift_point (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M) x
  haveI := he₁
  haveI := hs₁
  obtain ⟨T₂, e₂, y', he₂, hs₂, hy'⟩ :=
    _root_.GlobalTheory.DivisibleHom.exists_lift_point (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M) (e₁ ≫ y)
  haveI := he₂
  haveI := hs₂
  haveI : Flat (e₂ ≫ e₁).left := by rw [Over.comp_left]; infer_instance
  haveI : Surjective (e₂ ≫ e₁).left := by rw [Over.comp_left]; infer_instance
  have hxe : (e₂ ≫ e₁) ≫ x = (e₂ ≫ x') ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M := by
    rw [Category.assoc, ← hx', Category.assoc]
  have hye : (e₂ ≫ e₁) ≫ y = y' ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M := by
    rw [Category.assoc, ← hy']
  apply _root_.GlobalTheory.DivisibleHom.cancel_of_flat_surjective (e₂ ≫ e₁)
  calc (e₂ ≫ e₁) ≫ (x * y) ≫ φ = (((e₂ ≫ e₁) ≫ x) * ((e₂ ≫ e₁) ≫ y)) ≫ φ := by
        rw [← Category.assoc (e₂ ≫ e₁), comp_mul]
    _ = (((e₂ ≫ x') * y') ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M) ≫ φ := by rw [hxe, hye, hmm]
    _ = ((e₂ ≫ x') ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M ≫ φ) * (y' ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M ≫ φ) := by
        rw [Category.assoc, mul_comp]
    _ = (e₂ ≫ e₁) ≫ ((x ≫ φ) * (y ≫ φ)) := by
        rw [comp_mul, ← Category.assoc (e₂ ≫ e₁) x, ← Category.assoc (e₂ ≫ e₁) y, hxe, hye]
        simp only [Category.assoc]


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {S : Scheme.{0}} in
theorem _root_.GlobalTheory.DivisibleHom.exists_eq_pow_of_torsion_comp_eq_one :
    (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : _root_.ReciprocityTheory.ChartRestriction.G.Out.PolAV S) (n : ℕ), 1 ≤ n →
      IsFinite (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA P.A n).left ∧ Flat (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA P.A n).left ∧
        Surjective (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA P.A n).left ∧
          (IsUnit (n : Γ(S, ⊤)) → Etale (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA P.A n).left)) →
    ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : _root_.ReciprocityTheory.ChartRestriction.G.Out.PolAV S) (B : Over S) [GrpObj B]
      [IsCommMonObj B] (M : ℕ), 1 ≤ M → ∀ u : P.A ⟶ B, IsMonHom u →
        (∀ (T : Over S) (x : T ⟶ P.A), x ^ M = 1 → x ≫ u = 1) →
          (∃ φ : P.A ⟶ B, IsMonHom φ ∧ u = φ ^ M) ∧ (u ^ M = 1 → u = 1) := by
  intro H S _ P B _ _ M hM u hu hkill
  obtain ⟨hfin, hflat, hsurj, -⟩ := H S P M hM
  haveI := hfin
  haveI := hflat
  haveI := hsurj
  haveI := hu
  obtain ⟨φ, hφ⟩ := _root_.GlobalTheory.DivisibleHom.exists_factor M u hkill
  haveI : IsMonHom (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA P.A M ≫ φ) := by rw [hφ]; infer_instance
  haveI := _root_.GlobalTheory.DivisibleHom.isMonHom_of_factor M φ
  refine ⟨⟨φ, inferInstance, ?_⟩, fun h => ?_⟩
  · rw [← hφ, _root_.GlobalTheory.DivisibleHom.mulA_comp]
  · apply _root_.GlobalTheory.DivisibleHom.cancel_of_flat_surjective (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA P.A M)
    rw [_root_.GlobalTheory.DivisibleHom.mulA_comp, h, comp_one]

end GlobalTheory.DivisibleHom
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace SplitTorusPoints

open Rosenlicht

theorem ΓSpecIso_inv_comp_specMap {W : Scheme.{0}} {A B : CommRingCat.{0}} (g : W ⟶ Spec B)
    (f : A ⟶ B) :
    (Scheme.ΓSpecIso A).inv ≫ (g ≫ Spec.map f).appTop =
      f ≫ (Scheme.ΓSpecIso B).inv ≫ g.appTop := by
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Category.assoc, Scheme.ΓSpecIso_inv_naturality]

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {Z : Over S}

theorem map_left_fst {T : Scheme.{0}} (f : S ⟶ T) {A B : Over T} (g : A ⟶ B) :
    ((Over.pullback f).map g).left ≫ pullback.fst B.hom f = pullback.fst A.hom f ≫ g.left :=
  pullback.lift_fst _ _ _

theorem exists_mul_factor (a b : Z ⟶ splitTorus S X) :
    ∃ q : Z.left ⟶ (splitTorusAff ZU X ⊗ splitTorusAff ZU X).left,
      q ≫ (fst _ _ : _ ⟶ splitTorusAff ZU X).left = a.left ≫ torusFst S X ∧
      q ≫ (snd _ _ : _ ⟶ splitTorusAff ZU X).left = b.left ≫ torusFst S X ∧
      q ≫ μ[splitTorusAff ZU X].left = (a * b).left ≫ torusFst S X := by
  let F := Over.pullback (toZ S)
  let G := splitTorusAff ZU X
  let m : Z ⟶ F.obj (G ⊗ G) := lift (a : Z ⟶ F.obj G) (b : Z ⟶ F.obj G) ≫ Functor.LaxMonoidal.μ F G G
  have key : ∀ g : G ⊗ G ⟶ G, (m.left ≫ pullback.fst (G ⊗ G).hom (toZ S)) ≫ g.left =
      (m ≫ F.map g).left ≫ torusFst S X := by
    intro g
    rw [Category.assoc, ← map_left_fst, Over.comp_left]
    exact (Category.assoc _ _ _).symm
  refine ⟨m.left ≫ pullback.fst (G ⊗ G).hom (toZ S), ?_, ?_, ?_⟩
  · rw [key]
    congr 2
    exact (Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (Functor.Monoidal.μ_fst F G G)).trans (lift_fst _ _))
  · rw [key]
    congr 2
    exact (Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (Functor.Monoidal.μ_snd F G G)).trans (lift_snd _ _))
  · rw [key]
    congr 2

theorem coord_mul_single (a b : Z ⟶ splitTorus S X) (x : X) :
    (coord (a * b)).hom (AddMonoidAlgebra.single x 1) =
      (coord a).hom (AddMonoidAlgebra.single x 1) * (coord b).hom (AddMonoidAlgebra.single x 1) := by
  obtain ⟨q, h1, h2, h3⟩ := exists_mul_factor a b
  let A := torusRing ZU X
  let p : Z.left ⟶ Spec (.of (A ⊗[ZU.{0}] A)) := q ≫ (pullbackSpecIso ZU.{0} A A).hom
  let φ := (Scheme.ΓSpecIso (.of (A ⊗[ZU.{0}] A))).inv ≫ p.appTop
  have e1 : coord a = CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫ φ := by
    rw [← ΓSpecIso_inv_comp_specMap, coord, ← h1]
    congr 2
    exact (congrArg (q ≫ ·) (pullbackSpecIso_hom_fst ZU.{0} A A).symm).trans
      (Category.assoc _ _ _).symm
  have e2 : coord b = CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : A →ₐ[ZU.{0}] A ⊗[ZU.{0}] A).toRingHom ≫ φ := by
    rw [← ΓSpecIso_inv_comp_specMap, coord, ← h2]
    congr 2
    exact (congrArg (q ≫ ·) (pullbackSpecIso_hom_snd ZU.{0} A A).symm).trans
      (Category.assoc _ _ _).symm
  have e3 : coord (a * b) = CommRingCat.ofHom (Bialgebra.comulAlgHom ZU.{0} A) ≫ φ := by
    rw [← ΓSpecIso_inv_comp_specMap, coord, ← h3]
    congr 2
  rw [e1, e2, e3]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
  rw [← map_mul]
  congr 1
  change Coalgebra.comul (R := ULift.{0} ℤ) (AddMonoidAlgebra.single x (1 : ULift.{0} ℤ)) =
    (AddMonoidAlgebra.single x (1 : ULift.{0} ℤ) ⊗ₜ[ULift.{0} ℤ] (1 : AddMonoidAlgebra (ULift.{0} ℤ) X)) *
    ((1 : AddMonoidAlgebra (ULift.{0} ℤ) X) ⊗ₜ[ULift.{0} ℤ] AddMonoidAlgebra.single x (1 : ULift.{0} ℤ))
  simp

theorem coord_single (t : Z ⟶ splitTorus S X) (x : X) :
    (coord t).hom (AddMonoidAlgebra.single x 1) = t.left.appTop.hom (charUnit S X x).val := by
  rw [TorusInj.charUnit_val, coord, Scheme.Hom.comp_appTop]
  have : (TorusInj.tFst (S := S) X).appLE ⊤ ⊤ (TorusInj.tle _) = (torusFst S X).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [this]
  rfl

noncomputable def toHom (t : Z ⟶ splitTorus S X) : Multiplicative X →* Γ(Z.left, ⊤)ˣ :=
  ((coord t).hom.toMonoidHom.comp (AddMonoidAlgebra.of (ULift.{0} ℤ) X)).toHomUnits

theorem toHom_val (t : Z ⟶ splitTorus S X) (x : X) :
    (toHom t (Multiplicative.ofAdd x)).val = (coord t).hom (AddMonoidAlgebra.single x 1) := rfl

theorem exists_coord_eq (φ : torusRing ZU X ⟶ Γ(Z.left, ⊤)) :
    ∃ t : Z ⟶ splitTorus S X, coord t = φ := by
  refine ⟨Over.homMk (pullback.lift (Z.left.toSpecΓ ≫ Spec.map φ) Z.hom
    (specULiftZIsTerminal.hom_ext _ _)) (pullback.lift_snd _ _ _), ?_⟩
  have : (pullback.lift (Z.left.toSpecΓ ≫ Spec.map φ) Z.hom
    (specULiftZIsTerminal.hom_ext _ _) : Z.left ⟶ (splitTorus S X).left) ≫ torusFst S X =
      Z.left.toSpecΓ ≫ Spec.map φ := pullback.lift_fst _ _ _
  refine (congrArg (fun g => (Scheme.ΓSpecIso (torusRing ZU X)).inv ≫ Scheme.Hom.appTop g)
    this).trans ?_
  rw [ΓSpecIso_inv_comp_specMap, Scheme.toSpecΓ_appTop,
    Iso.inv_hom_id, Category.comp_id]

theorem toHom_bijective : Function.Bijective (toHom : (Z ⟶ splitTorus S X) → _) := by
  constructor
  · intro a b h
    apply coord_injective
    ext1
    refine ringHom_ext_ZU fun y => ?_
    rw [← toHom_val, ← toHom_val, h]
  · intro u
    letI : Algebra (ULift.{0} ℤ) Γ(Z.left, ⊤) := ULift.algebra' ℤ _
    obtain ⟨t, ht⟩ := exists_coord_eq (Z := Z) (X := X) (CommRingCat.ofHom
      (AddMonoidAlgebra.lift (ULift.{0} ℤ) Γ(Z.left, ⊤) X ((Units.coeHom _).comp u)).toRingHom)
    refine ⟨t, ?_⟩
    ext x
    change (toHom t (Multiplicative.ofAdd x)).val = _
    rw [toHom_val, ht]
    change AddMonoidAlgebra.lift (ULift.{0} ℤ) Γ(Z.left, ⊤) X ((Units.coeHom _).comp u)
      (AddMonoidAlgebra.single _ 1) = _
    simp

theorem toHom_mul (a b : Z ⟶ splitTorus S X) : toHom (a * b) = toHom a * toHom b := by
  ext x
  exact coord_mul_single a b x

end SplitTorusPoints

noncomputable def splitTorusPointsEquiv (S : Scheme.{0}) (X : Type) [AddCommGroup X] (Z : Over S) :
    (Z ⟶ splitTorus S X) ≃* (Multiplicative X →* Γ(Z.left, ⊤)ˣ) :=
  { Equiv.ofBijective _ SplitTorusPoints.toHom_bijective with
    map_mul' := SplitTorusPoints.toHom_mul }

theorem splitTorusPointsEquiv_val (S : Scheme.{0}) (X : Type) [AddCommGroup X] (Z : Over S)
    (t : Z ⟶ splitTorus S X) (χ : X) :
    (splitTorusPointsEquiv S X Z t (Multiplicative.ofAdd χ)).val =
      t.left.appTop.hom (charUnit S X χ).val :=
  SplitTorusPoints.coord_single t χ

theorem exists_splitTorus_points_mulEquiv :
    ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] (Z : Over S),
      ∃ e : (Z ⟶ splitTorus S X) ≃* (Multiplicative X →* Γ(Z.left, ⊤)ˣ),
        ∀ (t : Z ⟶ splitTorus S X) (χ : X),
          (e t (Multiplicative.ofAdd χ)).val = t.left.appTop.hom (charUnit S X χ).val :=
  fun S X _ Z => ⟨splitTorusPointsEquiv S X Z, splitTorusPointsEquiv_val S X Z⟩

end GlobalTheory
end
