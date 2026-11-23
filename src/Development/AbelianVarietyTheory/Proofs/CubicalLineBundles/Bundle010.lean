module

public import Mathlib.NumberTheory.NumberField.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsCyclotomicExtensionCyclotomicField28
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle002
public import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.Topology.Sheaves.Presheaf
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionOfIsPushout
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem eigenBC_relation {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K']
    [Algebra K K'] {m : ℕ} (s : Fin m → 𝓞 K') (x : Fin m → K) (φ : 𝓞 K' →ₗ[𝓞 K] 𝓞 K)
    (h : ∑ i, (s i : K') * algebraMap K K' (x i) = 0) :
    ∑ i, ((φ (s i) : 𝓞 K) : K) * x i = 0 := by
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 K)) x
  choose y hy using hd
  have hd0 : ((d : 𝓞 K) : K) ≠ 0 := by
    have := nonZeroDivisors.coe_ne_zero d
    exact_mod_cast this
  have hy' : ∀ i, ((y i : 𝓞 K) : K) = ((d : 𝓞 K) : K) * x i := by
    intro i
    have := hy i
    rw [Algebra.smul_def] at this
    exact this
  have h1 : ∑ i, y i • s i = 0 := by
    apply RingOfIntegers.coe_injective

    rw [map_sum, map_zero]
    have : ∀ i, algebraMap (𝓞 K') K' (y i • s i)
        = algebraMap K K' ((d : 𝓞 K) : K) * ((s i : K') * algebraMap K K' (x i)) := by
      intro i
      rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply (𝓞 K) K K']
      have e : algebraMap (𝓞 K) K (y i) = ((d : 𝓞 K) : K) * x i := hy' i
      rw [e, map_mul]
      show _ * (s i : K') = _
      ring
    simp only [this]
    rw [← Finset.mul_sum, h, mul_zero]
  have h2 : ∑ i, y i * φ (s i) = 0 := by
    have := congrArg φ h1

    simpa [map_sum] using this
  have h3 := congrArg (algebraMap (𝓞 K) K) h2

  rw [map_sum, map_zero] at h3
  apply mul_left_cancel₀ hd0
  rw [mul_zero, Finset.mul_sum, ← h3]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul]
  have e : algebraMap (𝓞 K) K (y i) = ((d : 𝓞 K) : K) * x i := hy' i
  rw [e]
  show _ = _ * ((φ (s i) : 𝓞 K) : K)
  ring

theorem eigenBC_frame (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K']
    [Algebra K K'] : ∃ (m : ℕ) (b : Fin m → 𝓞 K') (φ : Fin m → (𝓞 K' →ₗ[𝓞 K] 𝓞 K)),
      ∀ s, s = ∑ k, φ k s • b k := by
  haveI : Module.FinitePresentation (𝓞 K) (𝓞 K') := Module.finitePresentation_of_finite _ _
  haveI : Module.Projective (𝓞 K) (𝓞 K') := Module.Flat.projective_of_finitePresentation
  obtain ⟨m, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective (𝓞 K) (𝓞 K')
  refine ⟨m, fun k => f (Pi.single k 1), fun k => (LinearMap.proj k).comp g, fun s => ?_⟩
  have := LinearMap.congr_fun hfg s
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
  conv_lhs => rw [← this, LinearMap.pi_apply_eq_sum_univ f (g s)]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [LinearMap.comp_apply, LinearMap.proj_apply]
  congr 2
  funext i
  simp [Pi.single_apply, eq_comm]

theorem eigenLattice_baseChange : ∀ (K K' O : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [CommRing O] (j : K →+* K') (n : ℕ) (Λ : Submodule (𝓞 K) (Fin n → K)) (r : O → Matrix (Fin n) (Fin n) K) (τ : O → K) (c' : Fin n → K'), Λ.FG → (c' ∈ Submodule.span (𝓞 K') ((fun c i => j (c i)) '' {c | c ∈ Λ ∧ ∀ a, (r a).mulVec c = τ a • c}) ↔ c' ∈ Submodule.span (𝓞 K') ((fun c i => j (c i)) '' (Λ : Set (Fin n → K))) ∧ ∀ a, ((r a).map j).mulVec c' = j (τ a) • c') := by
  intro K K' O _ _ _ _ _ j n Λ r τ c' _
  have hmap : ∀ a (c : Fin n → K), ((r a).map j).mulVec (fun i => j (c i))
      = fun i => j ((r a).mulVec c i) := by
    intro a c
    funext i

    simp [Matrix.mulVec, dotProduct, map_sum]
  constructor
  · intro h
    refine ⟨Submodule.span_mono (Set.image_mono (show {c | c ∈ Λ ∧ ∀ a, (r a).mulVec c = τ a • c} ⊆ (Λ : Set (Fin n → K)) from fun c hc => hc.1)) h, fun a => ?_⟩
    induction h using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, ⟨-, hc⟩, rfl⟩ := hx
      rw [hmap, hc a]
      funext i
      simp
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.mulVec_add, hx, hy, smul_add]
    | smul s x _ hx => rw [Matrix.mulVec_smul, hx, smul_comm]
  · rintro ⟨h, he⟩
    letI : Algebra K K' := j.toAlgebra
    obtain ⟨m, s, g, hg⟩ := Submodule.mem_span_set'.1 h
    choose l hl hlg using fun i => (g i).2
    have hc : ∀ t, c' t = ∑ i, (s i : K') * j (l i t) := by
      intro t
      rw [← hg, Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hlg i]
      rfl
    obtain ⟨p, b, φ, hb⟩ := eigenBC_frame K K'
    have hc2 : c' = ∑ k, b k • (fun t => j ((∑ i, φ k (s i) • l i) t)) := by
      funext t
      rw [hc, Finset.sum_apply]
      have e : ∀ i, (s i : K') = ∑ k, j ((φ k (s i) : 𝓞 K) : K) * (b k : K') := by
        intro i
        have := congrArg (algebraMap (𝓞 K') K') (hb (s i))

        rw [map_sum] at this
        refine this.trans (Finset.sum_congr rfl fun k _ => ?_)
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply,
          IsScalarTower.algebraMap_apply (𝓞 K) K K']
        rfl
      rw [Finset.sum_congr rfl fun i _ => by rw [e i, Finset.sum_mul], Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      show _ = (b k : K') * j ((∑ i, φ k (s i) • l i) t)

      rw [Finset.sum_apply, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      show _ = (b k : K') * j (((φ k (s i) : 𝓞 K) : K) * l i t)
      rw [map_mul]; ring
    rw [hc2]
    refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨_, ⟨Λ.sum_mem fun i _ => Λ.smul_mem _ (hl i), fun a => ?_⟩, rfl⟩)
    funext t
    have key := eigenBC_relation s (fun i => (r a).mulVec (l i) t - τ a * l i t) (φ k) (by
      have h1 := congrFun (he a) t
      rw [← hg, Matrix.mulVec_sum, Finset.smul_sum, Finset.sum_apply, Finset.sum_apply,
        ← sub_eq_zero, ← Finset.sum_sub_distrib] at h1
      rw [← h1]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hlg i, Matrix.mulVec_smul, hmap]
      show (s i : K') * j _ = (s i : K') * j _ - j (τ a) * ((s i : K') * j (l i t))
      rw [map_sub, map_mul]; ring)
    rw [Matrix.mulVec_sum, Finset.smul_sum, Finset.sum_apply, Finset.sum_apply,
        ← sub_eq_zero, ← Finset.sum_sub_distrib, ← key]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec_smul]
    show ((φ k (s i) : 𝓞 K) : K) * _ - τ a * (((φ k (s i) : 𝓞 K) : K) * l i t) = _
    ring

end GlobalTheory.CM
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp valAt valAt')

namespace GlobalTheory.SchemeHomsFromPoints

theorem dense_closedPoints {X : Scheme.{0}} (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] :
    Dense (closedPoints X) := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
  rw [dense_iff_closure_eq]
  exact closure_closedPoints

theorem hom_ext_of_points {X Y : Scheme.{0}} (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] [IsReduced X]
    [Y.IsSeparated] (f g : X ⟶ Y) (H : ∀ x : Sp ℂ ⟶ X, x ≫ p = 𝟙 _ → x ≫ f = x ≫ g) : f = g := by
  refine ext_of_fromSpecResidueField_eq f g (terminal.from Y) (closedPoints X)
    (dense_closedPoints p) ?_ (terminal.hom_ext _ _)
  intro x hx
  have h := H (pointOfClosedPoint p x hx) (pointOfClosedPoint_comp p x hx)
  rw [← cancel_epi (Spec.map (residueFieldIsoBase p x hx).hom)]
  simpa only [pointOfClosedPoint, Category.assoc] using h

theorem eq_zero_of_points {X : Scheme.{0}} (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] [IsReduced X]
    (W : X.Opens) (h : Γ(X, W))
    (H : ∀ x : Sp ℂ ⟶ X, x ≫ p = 𝟙 _ → ∀ e : ⊤ ≤ x ⁻¹ᵁ W, valAt x W e h = 0) : h = 0 := by
  rw [← basicOpen_eq_bot_iff]
  by_contra hne
  have hne' : ((X.basicOpen h : X.Opens) : Set X).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h0
    exact hne (TopologicalSpace.Opens.ext h0)
  obtain ⟨x, hx, hxc⟩ := (dense_closedPoints p).inter_open_nonempty _ (X.basicOpen h).isOpen hne'
  have e : ⊤ ≤ (pointOfClosedPoint p x hxc) ⁻¹ᵁ W := by
    intro a _
    change pointOfClosedPoint p x hxc a ∈ W
    exact (pointOfClosedPoint_apply p x hxc a).symm ▸ X.basicOpen_le h hx
  have h1 := H _ (pointOfClosedPoint_comp p x hxc) e
  have h2 : ((pointOfClosedPoint p x hxc).appLE W ⊤ e).hom h = 0 := by
    apply (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv.injective
    rw [map_zero]
    exact h1
  have h3 := Scheme.basicOpen_appLE (pointOfClosedPoint p x hxc) ⊤ W e h
  have h4 : (IsLocalRing.closedPoint ℂ : Spec (CommRingCat.of ℂ)) ∈
      (Spec (CommRingCat.of ℂ)).basicOpen (((pointOfClosedPoint p x hxc).appLE W ⊤ e).hom h) := by
    have h5 : (IsLocalRing.closedPoint ℂ : Spec (CommRingCat.of ℂ)) ∈
        ⊤ ⊓ (pointOfClosedPoint p x hxc) ⁻¹ᵁ X.basicOpen h := by
      refine ⟨trivial, ?_⟩
      change pointOfClosedPoint p x hxc _ ∈ X.basicOpen h
      exact (pointOfClosedPoint_apply p x hxc _).symm ▸ hx
    rw [← h3] at h5
    exact h5
  rw [h2, Scheme.basicOpen_zero] at h4
  exact h4

theorem lift_toSpecΓ {X : Scheme.{0}} {R : CommRingCat.{0}} (W : X.Opens) (x : Spec R ⟶ X)
    (x' : Spec R ⟶ W) (hx : x' ≫ W.ι = x) (e : ⊤ ≤ x ⁻¹ᵁ W) :
    x' ≫ W.toSpecΓ = Spec.map (x.appLE W ⊤ e ≫ (Scheme.ΓSpecIso R).hom) := by
  have h1 : x.resLE W ⊤ e = (⊤ : (Spec R).Opens).ι ≫ x' := by
    rw [← cancel_mono W.ι, Scheme.Hom.resLE_comp_ι, Category.assoc, hx]
  have : IsIso (⊤ : (Spec R).Opens).ι := inferInstanceAs (IsIso (Spec R).topIso.hom)
  rw [← cancel_epi (⊤ : (Spec R).Opens).ι, Spec.map_comp, SpecMap_ΓSpecIso_hom,
    ← Category.assoc, ← h1, ← Category.assoc, ← Scheme.Opens.toSpecΓ_top,
    Scheme.Opens.toSpecΓ_SpecMap_appLE]

theorem range_subset {X T : Scheme.{0}} (W : X.Opens) (x : T ⟶ X) (e : ⊤ ≤ x ⁻¹ᵁ W) :
    Set.range x ⊆ Set.range W.ι := by
  rintro _ ⟨t, rfl⟩
  rw [Scheme.Opens.range_ι]
  exact e trivial

theorem top_le_of_lift {X T : Scheme.{0}} (W : X.Opens) (x : T ⟶ X) (x' : T ⟶ W)
    (hx : x' ≫ W.ι = x) : ⊤ ≤ x ⁻¹ᵁ W := by
  subst hx
  intro t _
  exact (x'.base t).2

noncomputable def ev {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (W : X.Opens) (e : ⊤ ≤ x ⁻¹ᵁ W) :
    Γ(X, W) ⟶ CommRingCat.of ℂ :=
  x.appLE W ⊤ e ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom

theorem valAt'_eq {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (W : X.Opens) (e : ⊤ ≤ x ⁻¹ᵁ W) (h : Γ(X, W)) :
    valAt' x W h = (ev x W e).hom h := by
  rw [valAt', dite_eq_left e]
  rfl

theorem exists_local {X Y : Scheme.{0}} (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] [IsReduced X]
    {Z : Type} (ex : Z → (Sp ℂ ⟶ X)) (ey : Z → (Sp ℂ ⟶ Y))
    (hex : ∀ x : Sp ℂ ⟶ X, x ≫ p = 𝟙 _ → ∃ z, ex z = x)
    (W : X.Opens) (D : Y.Opens) (hD : IsAffineOpen D)
    (hWD : ∀ w, ⊤ ≤ ex w ⁻¹ᵁ W → ⊤ ≤ ey w ⁻¹ᵁ D)
    (hf : ∀ f : Γ(Y, D), ∃ h : Γ(X, W), ∀ w, ⊤ ≤ ex w ⁻¹ᵁ W →
      valAt' (ex w) W h = valAt' (ey w) D f) :
    ∃ g : W.toScheme ⟶ Y, ∀ w (x' : Sp ℂ ⟶ W), x' ≫ W.ι = ex w → x' ≫ g = ey w := by
  choose F hF using hf
  have hF' : ∀ f w (e : ⊤ ≤ ex w ⁻¹ᵁ W),
      (ev (ex w) W e).hom (F f) = (ev (ey w) D (hWD w e)).hom f := by
    intro f w e
    rw [← valAt'_eq, ← valAt'_eq]
    exact hF f w e
  have inj : ∀ a b : Γ(X, W), (∀ w (e : ⊤ ≤ ex w ⁻¹ᵁ W),
      (ev (ex w) W e).hom a = (ev (ex w) W e).hom b) → a = b := by
    intro a b hab
    rw [← sub_eq_zero]
    refine eq_zero_of_points p W _ ?_
    intro x hx e
    obtain ⟨w, rfl⟩ := hex x hx
    change (ev (ex w) W e).hom (a - b) = 0
    rw [map_sub, hab w e, sub_self]
  let φ : Γ(Y, D) →+* Γ(X, W) :=
    { toFun := F
      map_one' := inj _ _ fun w e => by rw [hF', map_one, map_one]
      map_mul' := fun a b => inj _ _ fun w e => by rw [hF', map_mul, map_mul, hF', hF']
      map_zero' := inj _ _ fun w e => by rw [hF', map_zero, map_zero]
      map_add' := fun a b => inj _ _ fun w e => by rw [hF', map_add (f := _), map_add (f := _), hF', hF'] }
  refine ⟨W.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) ≫ hD.fromSpec, ?_⟩
  intro w x' hx'
  have e := top_le_of_lift W (ex w) x' hx'
  have e' := hWD w e
  have hy' := IsOpenImmersion.lift_fac D.ι (ey w) (range_subset D (ey w) e')
  have h1 : x' ≫ W.toSpecΓ = Spec.map (ev (ex w) W e) := lift_toSpecΓ W (ex w) x' hx' e
  have h2 : _ ≫ D.toSpecΓ = Spec.map (ev (ey w) D e') := lift_toSpecΓ D (ey w) _ hy' e'
  have h3 : CommRingCat.ofHom φ ≫ ev (ex w) W e = ev (ey w) D e' := by
    ext f
    exact hF' f w e
  rw [← Category.assoc, h1, ← Category.assoc, ← Spec.map_comp, h3, ← h2, Category.assoc,
    hD.toSpecΓ_fromSpec, hy']

theorem exists_hom {X Y : Scheme.{0}} (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] [IsReduced X]
    {Z : Type} (ex : Z → (Sp ℂ ⟶ X)) (ey : Z → (Sp ℂ ⟶ Y))
    (hex : ∀ x : Sp ℂ ⟶ X, x ≫ p = 𝟙 _ → ∃ z, ex z = x)
    {S : Scheme.{0}} (q : Y ⟶ S) [IsSeparated q] [IsAffine S]
    (H : ∀ z, ∃ (W : X.Opens) (D : Y.Opens), IsAffineOpen D ∧ ⊤ ≤ ex z ⁻¹ᵁ W ∧
      (∀ w, ⊤ ≤ ex w ⁻¹ᵁ W → ⊤ ≤ ey w ⁻¹ᵁ D) ∧
      ∀ f : Γ(Y, D), ∃ h : Γ(X, W), ∀ w, ⊤ ≤ ex w ⁻¹ᵁ W →
        valAt' (ex w) W h = valAt' (ey w) D f) :
    ∃ g : X ⟶ Y, ∀ z, ex z ≫ g = ey z := by
  have hY : Y.IsSeparated := ⟨by rw [← terminal.comp_from q]; infer_instance⟩
  choose W D hD hW hWD hf using H
  choose g hg using fun z => exists_local p ex ey hex (W z) (D z) (hD z) (hWD z) (hf z)
  have hcov : TopologicalSpace.IsOpenCover W := by
    have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    intro x₀ _
    by_contra hx₀
    have hcl : IsClosed ((iSup W : X.Opens) : Set X)ᶜ := (iSup W).isOpen.isClosed_compl
    obtain ⟨x, hx, hxc⟩ := nonempty_inter_closedPoints ⟨x₀, hx₀⟩ hcl.isLocallyClosed
    obtain ⟨z, hz⟩ := hex _ (pointOfClosedPoint_comp p x hxc)
    apply hx
    have h1 : ex z (IsLocalRing.closedPoint ℂ) ∈ W z :=
      hW z (show (IsLocalRing.closedPoint ℂ : Spec (CommRingCat.of ℂ)) ∈ ⊤ from trivial)
    have h2 : ex z (IsLocalRing.closedPoint ℂ) = x := by
      rw [hz]
      exact pointOfClosedPoint_apply p x hxc _
    exact le_iSup W z (h2 ▸ h1)
  have hglue : ∀ i j, pullback.fst (W i).ι (W j).ι ≫ g i = pullback.snd (W i).ι (W j).ι ≫ g j := by
    intro i j
    have : IsReduced (pullback (W i).ι (W j).ι) :=
      isReduced_of_isOpenImmersion (pullback.fst (W i).ι (W j).ι ≫ (W i).ι)
    refine hom_ext_of_points (pullback.fst (W i).ι (W j).ι ≫ (W i).ι ≫ p) _ _ ?_
    intro x hx
    obtain ⟨w, hw⟩ := hex (x ≫ pullback.fst (W i).ι (W j).ι ≫ (W i).ι) (by simpa using hx)
    rw [← Category.assoc, ← Category.assoc, hg i w _ (by rw [hw, Category.assoc]),
      hg j w _ (by rw [hw, Category.assoc, pullback.condition])]
  refine ⟨(X.openCoverOfIsOpenCover W hcov).glueMorphisms g hglue, fun z => ?_⟩
  have h1 := IsOpenImmersion.lift_fac (W z).ι (ex z) (range_subset (W z) (ex z) (hW z))
  have h2 : (W z).ι ≫ (X.openCoverOfIsOpenCover W hcov).glueMorphisms g hglue = g z :=
    Scheme.Cover.ι_glueMorphisms (X.openCoverOfIsOpenCover W hcov) g hglue z
  rw [← hg z z _ h1, ← h2, ← Category.assoc, h1]

end GlobalTheory.SchemeHomsFromPoints
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.RationalTorsion

theorem section_ext {K k : Type} [Field K] [Field k] (t : Sp k ⟶ Sp K) {G : Over (Sp K)}
    {s s' : 𝟙_ (Over (Sp K)) ⟶ G} (h : toUnit (Over.mk t) ≫ s = toUnit (Over.mk t) ≫ s') : s = s' := by
  have h1 : Surjective t := ⟨fun x => ⟨IsLocalRing.closedPoint k, Subsingleton.elim _ _⟩⟩
  have h2 : Flat t := inferInstance
  have h3 : Epi t := Flat.epi_of_flat_of_surjective t
  have h4 : (toUnit (Over.mk t)).left = t := by simp
  have h5 : Epi (toUnit (Over.mk t)).left := by rw [h4]; exact h3
  have h6 : Epi (toUnit (Over.mk t)) := Over.epi_of_epi_left _
  exact (cancel_epi _).1 h

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem ev_add_smul {D : Datum H} {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q}
    {e : ℕ → Q → Q → kˣ → Prop} (I : TateIso D k Q act e) {n : ℕ} (hn : 0 < n) (a c : D.La) :
    I.ev n (a + n • c) = I.ev n a := by
  rw [I.add, (I.ker n hn _).2 ⟨c, rfl⟩, _root_.mul_one]

theorem exists_eq_nsmul (D : Datum H) (l : Level H) {J J' : Ideal (𝓞 E)}
    (hJ : J * J' = Ideal.span {(l.M : 𝓞 E)}) {e : 𝓞 E} (he : e ∈ J) {a : D.La}
    (ha : a ∈ J' • (⊤ : Submodule (𝓞 E) D.La)) : ∃ c, e • a = l.M • c := by
  have h1 : e • a ∈ (J * J') • (⊤ : Submodule (𝓞 E) D.La) := by
    rw [Submodule.mul_smul]; exact Submodule.smul_mem_smul he ha
  rw [hJ, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h1
  obtain ⟨c, -, hc⟩ := h1
  exact ⟨c, by rw [← hc, Nat.cast_smul_eq_nsmul]⟩

end GlobalTheory.CM.RationalTorsion
end
end
