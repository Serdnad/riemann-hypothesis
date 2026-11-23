module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.KeyFormula.DegProd
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section

namespace GlobalTheory.GrpDescent

variable {S S₀ : Scheme.{0}}

theorem grpObj_descends (f : S ⟶ S₀) [Flat f] [Surjective f] (A : Over S) [GrpObj A] (A₀ : Over S₀)
    (π : A.left ⟶ A₀.left) (e₀ : 𝟙_ (Over S₀) ⟶ A₀) (m₀ : A₀ ⊗ A₀ ⟶ A₀) (i₀ : A₀ ⟶ A₀)
    (π₂ : (A ⊗ A).left ⟶ (A₀ ⊗ A₀).left) (hπ : IsPullback π A.hom A₀.hom f)
    (h1 : π₂ ≫ (fst A₀ A₀).left = (fst A A).left ≫ π) (h2 : π₂ ≫ (snd A₀ A₀).left = (snd A A).left ≫ π)
    (he : η[A].left ≫ π = f ≫ e₀.left) (hm : μ[A].left ≫ π = π₂ ≫ m₀.left)
    (hi : (GrpObj.inv : A ⟶ A).left ≫ π = π ≫ i₀.left) :
    ∃ _ : GrpObj A₀, IsGrpPullback A A₀ f π := by

  have rmul : ∀ {T' : Over S} {T : Over S₀} (p : T'.left ⟶ T.left) {x' y' : T' ⟶ A} {x y : T ⟶ A₀},
      x'.left ≫ π = p ≫ x.left → y'.left ≫ π = p ≫ y.left →
      (x' * y').left ≫ π = p ≫ (lift x y ≫ m₀).left := by
    intro T' T p x' y' x y hx hy
    have : (lift x' y').left ≫ π₂ = p ≫ (lift x y).left := by
      apply pullback.hom_ext
      · change ((lift x' y').left ≫ π₂) ≫ (fst A₀ A₀).left = (p ≫ (lift x y).left) ≫ (fst A₀ A₀).left
        rw [Category.assoc, h1, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc, ← Over.comp_left,
          lift_fst, hx]
      · change ((lift x' y').left ≫ π₂) ≫ (snd A₀ A₀).left = (p ≫ (lift x y).left) ≫ (snd A₀ A₀).left
        rw [Category.assoc, h2, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc, ← Over.comp_left,
          lift_snd, hy]
    rw [Hom.mul_def, Over.comp_left, Category.assoc, hm, ← Category.assoc, this, Over.comp_left, Category.assoc]
  have rone : ∀ {T' : Over S} {T : Over S₀} (p : T'.left ⟶ T.left), p ≫ T.hom = T'.hom ≫ f →
      (1 : T' ⟶ A).left ≫ π = p ≫ (toUnit T ≫ e₀).left := by
    intro T' T p hp
    rw [Hom.one_def, Over.comp_left, Category.assoc, he, Over.comp_left, Over.toUnit_left, Over.toUnit_left]
    exact (Category.assoc _ _ _).symm.trans (by rw [← hp]; exact Category.assoc _ _ _)
  have rinv : ∀ {T' : Over S} {T : Over S₀} (p : T'.left ⟶ T.left) {x' : T' ⟶ A} {x : T ⟶ A₀},
      x'.left ≫ π = p ≫ x.left → (x'⁻¹).left ≫ π = p ≫ (x ≫ i₀).left := by
    intro T' T p x' x hx
    rw [Hom.inv_def, Over.comp_left, Category.assoc, hi, ← Category.assoc, hx, Over.comp_left, Category.assoc]

  have cov : ∀ T : Over S₀, ∃ (T' : Over S) (p : T'.left ⟶ T.left), p ≫ T.hom = T'.hom ≫ f ∧
      (∀ a b : T ⟶ A₀, p ≫ a.left = p ≫ b.left → a = b) ∧
      ∀ x : T ⟶ A₀, ∃ x' : T' ⟶ A, x'.left ≫ π = p ≫ x.left := by
    intro T
    refine ⟨Over.mk (pullback.snd T.hom f), pullback.fst T.hom f, pullback.condition, fun a b h => ?_, fun x => ?_⟩
    · have : Epi (pullback.fst T.hom f) := Flat.epi_of_flat_of_surjective _
      ext1
      exact (cancel_epi (pullback.fst T.hom f)).1 h
    · refine ⟨Over.homMk (hπ.lift (pullback.fst T.hom f ≫ x.left) (pullback.snd T.hom f) ?_) ?_, ?_⟩
      · rw [Category.assoc, Over.w x, pullback.condition]
      · exact hπ.lift_snd _ _ _
      · exact hπ.lift_fst _ _ _
  have one_mul' : ∀ {T : Over S₀} (x : T ⟶ A₀), lift (toUnit T ≫ e₀) x ≫ m₀ = x := by
    intro T x
    obtain ⟨T', p, hp, hinj, hl⟩ := cov T
    obtain ⟨x', hx⟩ := hl x
    apply hinj
    rw [← rmul p (rone p hp) hx, _root_.one_mul, hx]
  have mul_one' : ∀ {T : Over S₀} (x : T ⟶ A₀), lift x (toUnit T ≫ e₀) ≫ m₀ = x := by
    intro T x
    obtain ⟨T', p, hp, hinj, hl⟩ := cov T
    obtain ⟨x', hx⟩ := hl x
    apply hinj
    rw [← rmul p hx (rone p hp), _root_.mul_one, hx]
  have assoc' : ∀ {T : Over S₀} (x y z : T ⟶ A₀),
      lift (lift x y ≫ m₀) z ≫ m₀ = lift x (lift y z ≫ m₀) ≫ m₀ := by
    intro T x y z
    obtain ⟨T', p, hp, hinj, hl⟩ := cov T
    obtain ⟨x', hx⟩ := hl x
    obtain ⟨y', hy⟩ := hl y
    obtain ⟨z', hz⟩ := hl z
    apply hinj
    rw [← rmul p (rmul p hx hy) hz, ← rmul p hx (rmul p hy hz), _root_.mul_assoc]
  have linv' : ∀ {T : Over S₀} (x : T ⟶ A₀), lift (x ≫ i₀) x ≫ m₀ = toUnit T ≫ e₀ := by
    intro T x
    obtain ⟨T', p, hp, hinj, hl⟩ := cov T
    obtain ⟨x', hx⟩ := hl x
    apply hinj
    rw [← rmul p (rinv p hx) hx, ← rone p hp, inv_mul_cancel]
  have rinv' : ∀ {T : Over S₀} (x : T ⟶ A₀), lift x (x ≫ i₀) ≫ m₀ = toUnit T ≫ e₀ := by
    intro T x
    obtain ⟨T', p, hp, hinj, hl⟩ := cov T
    obtain ⟨x', hx⟩ := hl x
    apply hinj
    rw [← rmul p hx (rinv p hx), ← rone p hp, mul_inv_cancel]
  let G : GrpObj A₀ :=
    { one := e₀
      mul := m₀
      one_mul := by
        rw [← one_mul' (λ_ A₀).hom]
        congr 1
      mul_one := by
        rw [← mul_one' (ρ_ A₀).hom]
        congr 1
        apply CartesianMonoidalCategory.hom_ext
        · rw [whiskerLeft_fst, lift_fst, rightUnitor_hom]
        · rw [whiskerLeft_snd, lift_snd]
          congr 1
          exact toUnit_unique _ _
      mul_assoc := by
        have h := assoc' (fst (A₀ ⊗ A₀) A₀ ≫ fst A₀ A₀) (fst (A₀ ⊗ A₀) A₀ ≫ snd A₀ A₀) (snd (A₀ ⊗ A₀) A₀)
        have a1 : m₀ ▷ A₀ = lift (lift (fst (A₀ ⊗ A₀) A₀ ≫ fst A₀ A₀) (fst (A₀ ⊗ A₀) A₀ ≫ snd A₀ A₀) ≫ m₀)
            (snd (A₀ ⊗ A₀) A₀) := by
          apply CartesianMonoidalCategory.hom_ext
          · rw [whiskerRight_fst, lift_fst, ← comp_lift, lift_fst_snd, Category.comp_id]
          · rw [whiskerRight_snd, lift_snd]
        have a2 : (α_ A₀ A₀ A₀).hom ≫ A₀ ◁ m₀ = lift (fst (A₀ ⊗ A₀) A₀ ≫ fst A₀ A₀)
            (lift (fst (A₀ ⊗ A₀) A₀ ≫ snd A₀ A₀) (snd (A₀ ⊗ A₀) A₀) ≫ m₀) := by
          apply CartesianMonoidalCategory.hom_ext
          · rw [Category.assoc, whiskerLeft_fst, lift_fst, associator_hom_fst]
          · rw [Category.assoc, whiskerLeft_snd, lift_snd, ← Category.assoc]
            congr 1
            apply CartesianMonoidalCategory.hom_ext
            · rw [Category.assoc, lift_fst, associator_hom_snd_fst]
            · rw [Category.assoc, lift_snd, associator_hom_snd_snd]
        rw [← Category.assoc, a2, a1, h]
      inv := i₀
      left_inv := by simpa only [Category.id_comp] using linv' (𝟙 A₀)
      right_inv := by simpa only [Category.id_comp] using rinv' (𝟙 A₀) }
  refine ⟨G, hπ, fun T x y x₀ y₀ hx hy => ?_⟩
  have := rmul (T' := T) (T := Over.mk (T.hom ≫ f)) (𝟙 T.left) (x' := x) (y' := y) (x := x₀) (y := y₀)
    (hx.symm.trans (Category.id_comp _).symm) (hy.symm.trans (Category.id_comp _).symm)
  exact (this.trans (Category.id_comp _)).symm

theorem grpObj_descends_faithfullyFlat : ∀ (R₀ R : Type) [CommRing R₀] [CommRing R] [Algebra R₀ R] [Module.FaithfullyFlat R₀ R] (A : Over (Sp R)) [GrpObj A] (A₀ : Over (Sp R₀)) [Flat A₀.hom] [IsSeparated A₀.hom] [QuasiCompact A₀.hom] (π : A.left ⟶ A₀.left) (e₀ : 𝟙_ (Over (Sp R₀)) ⟶ A₀) (m₀ : A₀ ⊗ A₀ ⟶ A₀) (i₀ : A₀ ⟶ A₀) (π₂ : (A ⊗ A).left ⟶ (A₀ ⊗ A₀).left), IsPullback π A.hom A₀.hom (spMap (algebraMap R₀ R)) → π₂ ≫ (fst A₀ A₀).left = (fst A A).left ≫ π → π₂ ≫ (snd A₀ A₀).left = (snd A A).left ≫ π → η[A].left ≫ π = spMap (algebraMap R₀ R) ≫ e₀.left → μ[A].left ≫ π = π₂ ≫ m₀.left → (GrpObj.inv : A ⟶ A).left ≫ π = π ≫ i₀.left → ∃ _ : GrpObj A₀, IsGrpPullback A A₀ (spMap (algebraMap R₀ R)) π := by
  intro R₀ R _ _ _ _ A _ A₀ _ _ _ π e₀ m₀ i₀ π₂ hπ h1 h2 he hm hi
  have hff : (algebraMap R₀ R).FaithfullyFlat := RingHom.faithfullyFlat_algebraMap_iff.2 ‹_›
  obtain ⟨_, _⟩ := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap R₀ R))).2 hff
  exact grpObj_descends _ A A₀ π e₀ m₀ i₀ π₂ hπ h1 h2 he hm hi

end GlobalTheory.GrpDescent
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

noncomputable def holUnifReparam {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
    (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (e : (Fin g → ℂ) → ℂ) (he : Differentiable ℂ e) (hne : ∀ z, e z ≠ 0) :
    HolUnif A L g where
  ex z := u.ex (φ z)
  ex_add z w := by rw [map_add (f := _), u.ex_add]
  ex_onto := u.ex_onto.comp φ.surjective
  Λ := u.Λ.comap (φ.toLinearMap.restrictScalars ℤ)
  ker z := u.ker (φ z)
  discrete := by
    haveI := u.discrete
    have hc : Continuous (fun z : Fin g → ℂ => φ z) := φ.toContinuousLinearEquiv.continuous
    refine DiscreteTopology.of_continuous_injective
      (f := fun x : u.Λ.comap (φ.toLinearMap.restrictScalars ℤ) => (⟨φ x.1, x.2⟩ : u.Λ))
      ((hc.comp continuous_subtype_val).subtype_mk _) ?_
    intro x y h
    exact Subtype.ext (φ.injective (congrArg Subtype.val h))
  full := by
    have h1 : ((u.Λ.comap (φ.toLinearMap.restrictScalars ℤ) : Submodule ℤ (Fin g → ℂ)) : Set (Fin g → ℂ)) =
        (φ.symm.toLinearMap.restrictScalars ℝ) '' (u.Λ : Set (Fin g → ℂ)) := by
      ext z
      constructor
      · intro hz
        exact ⟨φ z, hz, φ.symm_apply_apply z⟩
      · rintro ⟨w, hw, rfl⟩
        show φ (φ.symm w) ∈ u.Λ
        rwa [φ.apply_symm_apply]
    rw [h1, ← Submodule.map_span, u.full, Submodule.map_top, LinearMap.range_eq_top]
    exact φ.symm.surjective
  hol U f := by
    have hc : Differentiable ℂ (fun z : Fin g → ℂ => φ z) := φ.toContinuousLinearEquiv.differentiable
    exact ⟨(u.hol U f).1.preimage hc.continuous, (u.hol U f).2.comp hc.differentiableOn (fun _ hz => hz)⟩
  fr i z := u.fr i (φ z) / e z
  fr_hol i := by
    have hc : Differentiable ℂ (fun z : Fin g → ℂ => φ z) := φ.toContinuousLinearEquiv.differentiable
    have h1 : DifferentiableOn ℂ (fun z => u.fr i (φ z)) {z | ⊤ ≤ (u.ex (φ z)).left ⁻¹ᵁ L.U i} :=
      (u.fr_hol i).comp hc.differentiableOn (fun _ hz => hz)
    have h2 : Differentiable ℂ (fun z => (e z)⁻¹) := he.inv hne
    simp only [div_eq_mul_inv]
    exact h1.mul h2.differentiableOn
  fr_ne i z hz := div_ne_zero (u.fr_ne i _ hz) (hne z)
  fr_compat i j z hz := by
    rw [u.fr_compat i j _ hz, mul_div_assoc]

theorem exists_holUnif_reparam :
    ∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ) (u : HolUnif A L g) (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (e : (Fin g → ℂ) → ℂ), Differentiable ℂ e → (∀ z, e z ≠ 0) → e 0 = 1 → ∃ u' : HolUnif A L g, (∀ z, u'.ex z = u.ex (φ z)) ∧ (∀ z, z ∈ u'.Λ ↔ φ z ∈ u.Λ) ∧ (∀ rig, u.IsRig rig → u'.IsRig rig) ∧ (∀ s θ, u.IsFn s θ → u'.IsFn s (fun z => e z * θ (φ z))) ∧ ∀ w v, u.IsDiff (φ w) v → u'.IsDiff w v := by
  intro A _ L g u φ e he hne h0
  refine ⟨holUnifReparam u φ e he hne, fun _ => rfl, fun _ => Iff.rfl, ?_, ?_, ?_⟩
  · intro rig hr j hj
    show u.fr _ (φ 0) / e 0 = _
    rw [map_zero, h0, div_one]
    exact hr j hj
  · intro s θ hs i z hz
    have h := hs i (φ z) hz
    show valAt' (u.ex (φ z)).left _ _ = e z * θ (φ z) * (u.fr i (φ z) / e z)
    rw [h]
    have := hne z
    field_simp
  · intro w v hv U h f
    rw [hv U h f]
    have key := φ.toContinuousLinearEquiv.comp_right_fderiv
      (f := fun z => valAt' (u.ex z).left U f) (x := 0)
    have h2 := congrArg (fun T => T w) key
    simp only [map_zero] at h2
    exact h2.symm

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PowLie

variable {R : Type} [CommRing R]

def sc (c : R) : epsR R ⟶ epsR R :=
  Over.homMk (spMap (epsScaleR c)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl])

def zeroPt (R : Type) [CommRing R] : 𝟙_ (Over (Sp R)) ⟶ epsR R :=
  Over.homMk (spMap (TrivSqZeroExt.fstHom R R R).toRingHom) (by
    change Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1)

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.PowLie.isTangent_iff {G : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R)} [GrpObj G]
    (w : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR R ⟶ G) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsTangent w ↔ _root_.GlobalTheory.PowLie.zeroPt R ≫ w = η[G] := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsTangent
  constructor
  · intro h
    ext
    simpa [_root_.GlobalTheory.PowLie.zeroPt] using h
  · intro h
    simpa [_root_.GlobalTheory.PowLie.zeroPt] using congrArg Over.Hom.left h

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.PowLie.isLieComb_iff_prod {G : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R)} [GrpObj G] [IsCommMonObj G]
    {n : ℕ} (c : Fin n → R) (v : Fin n → (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR R ⟶ G)) (w : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR R ⟶ G) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsLieComb c v w ↔ w = ∏ i, _root_.GlobalTheory.PowLie.sc (c i) ≫ v i := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsLieComb
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [List.prod_ofFn]
    refine Finset.prod_congr rfl fun i _ => ?_
    ext
    simp [_root_.GlobalTheory.PowLie.sc, hu i]
  · intro hw
    refine ⟨fun i => _root_.GlobalTheory.PowLie.sc (c i) ≫ v i, fun i => by
      simp [_root_.GlobalTheory.PowLie.sc], ?_⟩
    rw [List.prod_ofFn]
    exact hw

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {R : Type} [CommRing R] in
private theorem finset_prod_comp_of_isMonHom {X M N : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R)} [MonObj M] [IsCommMonObj M]
    [MonObj N] [IsCommMonObj N] {κ : Type*} (s : Finset κ) (f : κ → (X ⟶ M)) (h : M ⟶ N)
    [IsMonHom h] : (∏ i ∈ s, f i) ≫ h = ∏ i ∈ s, f i ≫ h :=
  map_prod (IsMonHom.monoidHom h X) f s

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {R : Type} [CommRing R] in
private theorem zeroPt_comp_one {G : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R)} [GrpObj G] :
    _root_.GlobalTheory.PowLie.zeroPt R ≫ (1 : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR R ⟶ G) = η[G] := by
  rw [comp_one, Hom.one_def]
  simp

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.PowLie.isLieBasis_pow : ∀ (R : Type) [CommRing R] (G' G : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R)) [GrpObj G']
    [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G] (j g : ℕ) (p : _root_.ReciprocityTheory.ChartRestriction.G.Out.IsPowGrp G' G j)
    (v : Fin g → (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR R ⟶ G)), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsLieBasis v → ∃ v' : Fin (j * g) → (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR R ⟶ G'),
      _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsLieBasis v' ∧ ∀ (i i' : Fin j) (k : Fin g),
        v' (finProdFinEquiv (i, k)) ≫ p.pr i' = if i = i' then v k else 1 := by
  intro R _ G' G _ _ _ _ j g p v hv
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsLieBasis at hv ⊢
  obtain ⟨htan, huniq⟩ := hv
  have hmon : ∀ i, IsMonHom (p.pr i) := p.hom
  let v' : Fin (j * g) → (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR R ⟶ G') := fun m =>
    Fan.IsLimit.lift p.lim (fun i' =>
      if (finProdFinEquiv.symm m).1 = i' then v (finProdFinEquiv.symm m).2 else 1)
  have hv' : ∀ (i i' : Fin j) (k : Fin g),
      v' (finProdFinEquiv (i, k)) ≫ p.pr i' = if i = i' then v k else 1 := by
    intro i i' k
    exact (Fan.IsLimit.fac p.lim _ i').trans (by simp only [Equiv.symm_apply_apply])
  have hpr : ∀ (w : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR R ⟶ G') (i : Fin j), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsTangent w → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsTangent (w ≫ p.pr i) := by
    intro w i hw
    rw [_root_.GlobalTheory.PowLie.isTangent_iff] at hw ⊢
    rw [← Category.assoc, hw, IsMonHom.one_hom]
  have hcomb : ∀ (c : Fin (j * g) → R) (i' : Fin j),
      (∏ m, _root_.GlobalTheory.PowLie.sc (c m) ≫ v' m) ≫ p.pr i' =
        ∏ k, _root_.GlobalTheory.PowLie.sc (c (finProdFinEquiv (i', k))) ≫ v k := by
    intro c i'
    rw [finset_prod_comp_of_isMonHom, ← finProdFinEquiv.prod_comp, Fintype.prod_prod_type]
    have hterm : ∀ (i : Fin j) (k : Fin g),
        (_root_.GlobalTheory.PowLie.sc (c (finProdFinEquiv (i, k))) ≫ v' (finProdFinEquiv (i, k))) ≫
            p.pr i' =
          if i = i' then _root_.GlobalTheory.PowLie.sc (c (finProdFinEquiv (i, k))) ≫ v k else 1 := by
      intro i k
      rw [Category.assoc, hv']
      split_ifs <;> simp [comp_one]
    simp only [hterm]
    rw [Fintype.prod_eq_single i' (fun i hi => by simp [hi])]
    simp
  refine ⟨v', ⟨fun m => ?_, fun w hw => ?_⟩, hv'⟩
  · obtain ⟨⟨i, k⟩, rfl⟩ := finProdFinEquiv.surjective m
    rw [_root_.GlobalTheory.PowLie.isTangent_iff]
    refine Fan.IsLimit.hom_ext p.lim _ _ fun i' => ?_
    change (_root_.GlobalTheory.PowLie.zeroPt R ≫ v' (finProdFinEquiv (i, k))) ≫ p.pr i' =
      η[G'] ≫ p.pr i'
    rw [Category.assoc, hv', IsMonHom.one_hom]
    split_ifs
    · exact (_root_.GlobalTheory.PowLie.isTangent_iff _).1 (htan k)
    · exact zeroPt_comp_one
  · choose cc hcc hcc' using fun i => huniq (w ≫ p.pr i) (hpr w i hw)
    refine ⟨fun m => cc (finProdFinEquiv.symm m).1 (finProdFinEquiv.symm m).2, ?_, ?_⟩
    · beta_reduce
      rw [_root_.GlobalTheory.PowLie.isLieComb_iff_prod]
      refine Fan.IsLimit.hom_ext p.lim _ _ fun i' => ?_
      change w ≫ p.pr i' = (∏ m, _) ≫ p.pr i'
      rw [hcomb, (_root_.GlobalTheory.PowLie.isLieComb_iff_prod _ _ _).1 (hcc i')]
      simp
    · intro c' hc'
      rw [_root_.GlobalTheory.PowLie.isLieComb_iff_prod] at hc'
      funext m
      obtain ⟨⟨i, k⟩, rfl⟩ := finProdFinEquiv.surjective m
      have h := hcc' i (fun k => c' (finProdFinEquiv (i, k))) (by
        beta_reduce
        rw [_root_.GlobalTheory.PowLie.isLieComb_iff_prod, hc', hcomb])
      simpa using congrFun h k

end GlobalTheory.PowLie
end
end
