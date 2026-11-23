module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle051
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle080
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle009
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle083
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.GrpDescent

open GrpDense

variable {Z U : Scheme.{0}} {j : U ⟶ Z}

theorem hom_ext_of_points (j : U ⟶ Z) [Flat j] [Surjective j] {X Y : Over Z} {f g : X ⟶ Y}
    (h : ∀ (T : Over U) (t : Over.mk (T.hom ≫ j) ⟶ X), t ≫ f = t ≫ g) : f = g := by
  have : Epi (pullback.fst X.hom j) := Flat.epi_of_flat_of_surjective _
  apply Over.OverMorphism.ext
  rw [← cancel_epi (pullback.fst X.hom j)]
  exact congrArg (fun z => z.left) (h (Over.mk (pullback.snd X.hom j))
    (Over.homMk (pullback.fst X.hom j) (by simpa using pullback.condition)))

variable {G : Over Z} {A : Over U} {φ : A.left ⟶ G.left}

def sq (w : φ ≫ G.hom = A.hom ≫ j) : (A ⊗ A).left ⟶ (G ⊗ G).left :=
  (lift (pushPt w (fst A A)) (pushPt w (snd A A))).left

theorem isSquare_sq (w : φ ≫ G.hom = A.hom ≫ j) : IsSquare φ (sq w) := by
  constructor
  · rw [sq, ← Over.comp_left, lift_fst]; rfl
  · rw [sq, ← Over.comp_left, lift_snd]; rfl

theorem sq_ext {W : Scheme.{0}} {a b : W ⟶ (G ⊗ G).left} (h₁ : a ≫ (fst G G).left = b ≫ (fst G G).left)
    (h₂ : a ≫ (snd G G).left = b ≫ (snd G G).left) : a = b :=
  pullback.hom_ext h₁ h₂

theorem eq_sq (w : φ ≫ G.hom = A.hom ≫ j) {φ₂ : (A ⊗ A).left ⟶ (G ⊗ G).left} (h : IsSquare φ φ₂) :
    φ₂ = sq w :=
  sq_ext (h.1.trans (isSquare_sq w).1.symm) (h.2.trans (isSquare_sq w).2.symm)

theorem isPullback_sq (hA : IsPullback φ A.hom G.hom j) :
    IsPullback (sq hA.w) (A ⊗ A).hom (G ⊗ G).hom j := by
  have w₁ : (fst G G).left ≫ G.hom = (G ⊗ G).hom := Over.w _
  have w₂ : (snd G G).left ≫ G.hom = (G ⊗ G).hom := Over.w _
  have v₁ : (fst A A).left ≫ A.hom = (A ⊗ A).hom := Over.w _
  have v₂ : (snd A A).left ≫ A.hom = (A ⊗ A).hom := Over.w _
  have h₁ := (isSquare_sq hA.w).1
  have h₂ := (isSquare_sq hA.w).2
  refine ⟨⟨by rw [← w₁, reassoc_of% h₁, hA.w, reassoc_of% v₁]⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => pullback.lift
      (hA.lift (s.fst ≫ (fst G G).left) s.snd (by rw [Category.assoc, w₁, s.condition]))
      (hA.lift (s.fst ≫ (snd G G).left) s.snd (by rw [Category.assoc, w₂, s.condition]))
      (by rw [IsPullback.lift_snd, IsPullback.lift_snd])) (fun s => ?_) (fun s => ?_)
    (fun s m h1 h2 => ?_)⟩⟩
  · apply sq_ext
    · rw [Category.assoc, h₁, ← Category.assoc]
      exact (congrArg (· ≫ φ) (pullback.lift_fst _ _ _)).trans (IsPullback.lift_fst _ _ _ _)
    · rw [Category.assoc, h₂, ← Category.assoc]
      exact (congrArg (· ≫ φ) (pullback.lift_snd _ _ _)).trans (IsPullback.lift_fst _ _ _ _)
  · rw [← v₁, ← Category.assoc]
    exact (congrArg (· ≫ A.hom) (pullback.lift_fst _ _ _)).trans (IsPullback.lift_snd _ _ _ _)
  · apply pullback.hom_ext
    · refine Eq.trans ?_ (pullback.lift_fst _ _ _).symm
      change _ ≫ (fst A A).left = _
      apply hA.hom_ext
      · rw [IsPullback.lift_fst, ← h1, Category.assoc, Category.assoc, h₁]
      · rw [IsPullback.lift_snd, ← h2, Category.assoc, v₁]
    · refine Eq.trans ?_ (pullback.lift_snd _ _ _).symm
      change _ ≫ (snd A A).left = _
      apply hA.hom_ext
      · rw [IsPullback.lift_fst, ← h1, Category.assoc, Category.assoc, h₂]
      · rw [IsPullback.lift_snd, ← h2, Category.assoc, v₂]

theorem exists_grpObj (j : U ⟶ Z) [Flat j] [Surjective j] [GrpObj A] (h : IsPullback φ A.hom G.hom j)
    (m : G ⊗ G ⟶ G) (i : G ⟶ G) (e : 𝟙_ (Over Z) ⟶ G)
    (hm : sq h.w ≫ m.left = (μ[A]).left ≫ φ) (hi : φ ≫ i.left = (ι[A]).left ≫ φ)
    (he : j ≫ e.left = (η[A]).left ≫ φ) : ∃ _ : GrpObj G, IsGrpPullback A G j φ := by
  have hM := fun {T : Over U} => pushPt_mul h.w (fun φ₂ h₂ => by rw [eq_sq h.w h₂, hm]) (T := T)
  have hI := fun {T : Over U} => pushPt_inv h.w hi (T := T)
  have hE := pushPt_one h.w he
  letI : MonObj G :=
    { one := e
      mul := m
      one_mul := hom_ext_of_points j fun T t => by
        obtain ⟨x, hx⟩ := pushPt_surjective h T (t ≫ snd _ _)
        obtain rfl : t = lift (toUnit _) (pushPt h.w x) :=
          CartesianMonoidalCategory.hom_ext _ _ (toUnit_unique _ _) (by rw [lift_snd, hx])
        rw [lift_whiskerRight_assoc, hE, hM, _root_.one_mul, lift_leftUnitor_hom]
      mul_one := hom_ext_of_points j fun T t => by
        obtain ⟨x, hx⟩ := pushPt_surjective h T (t ≫ fst _ _)
        obtain rfl : t = lift (pushPt h.w x) (toUnit _) :=
          CartesianMonoidalCategory.hom_ext _ _ (by rw [lift_fst, hx]) (toUnit_unique _ _)
        rw [lift_whiskerLeft_assoc, hE, hM, _root_.mul_one, lift_rightUnitor_hom]
      mul_assoc := hom_ext_of_points j fun T t => by
        obtain ⟨x, hx⟩ := pushPt_surjective h T (t ≫ fst _ _ ≫ fst _ _)
        obtain ⟨y, hy⟩ := pushPt_surjective h T (t ≫ fst _ _ ≫ snd _ _)
        obtain ⟨z, hz⟩ := pushPt_surjective h T (t ≫ snd _ _)
        obtain rfl : t = lift (lift (pushPt h.w x) (pushPt h.w y)) (pushPt h.w z) := by
          ext <;> simp [hx, hy, hz]
        rw [lift_whiskerRight_assoc, lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc, hM, hM, hM, hM,
          _root_.mul_assoc] }
  letI : GrpObj G :=
    { inv := i
      left_inv := hom_ext_of_points j fun T t => by
        obtain ⟨x, rfl⟩ := pushPt_surjective h T t
        change _ ≫ _ ≫ m = _ ≫ _ ≫ e
        rw [comp_lift_assoc, Category.comp_id, hI, hM, inv_mul_cancel, comp_toUnit_assoc, hE]
      right_inv := hom_ext_of_points j fun T t => by
        obtain ⟨x, rfl⟩ := pushPt_surjective h T t
        change _ ≫ _ ≫ m = _ ≫ _ ≫ e
        rw [comp_lift_assoc, Category.comp_id, hI, hM, mul_inv_cancel, comp_toUnit_assoc, hE] }
  refine ⟨inferInstance, h, fun T x y x₀ y₀ hx hy => ?_⟩
  obtain rfl : x₀ = pushPt h.w x := Over.OverMorphism.ext hx
  obtain rfl : y₀ = pushPt h.w y := Over.OverMorphism.ext hy
  exact congrArg (fun z => z.left) (hM x y)

theorem flat_spMap {k K : Type} [Field k] [Field K] (β : k →+* K) : Flat (spMap β) := by
  rw [Flat.SpecMap_iff]
  letI := β.toAlgebra
  exact (inferInstance : Module.Flat k K)

theorem surjective_spMap {k K : Type} [Field k] [Field K] (β : k →+* K) : Surjective (spMap β) :=
  ⟨fun _ => ⟨default, Subsingleton.elim (α := PrimeSpectrum k) _ _⟩⟩

theorem spMap_subtype {K : Type} [Field K] {K₀ K₁ : Subfield K} (h : K₀ ≤ K₁) :
    spMap K₁.subtype ≫ spMap (Subfield.inclusion h) = spMap K₀.subtype := by
  rw [← Spec.map_comp]; rfl

end GlobalTheory.GrpDescent

namespace GlobalTheory

open GrpDescent

theorem grpObj_descends_to_large_subfield :
    ∀ (K : Type) [Field K] (K₀ : Subfield K) (A₀ : Over (Sp K₀)) (A : Over (Sp K)) [GrpObj A] (φ : A.left ⟶ A₀.left) [QuasiCompact A₀.hom] [QuasiSeparated A₀.hom] [LocallyOfFinitePresentation A₀.hom], IsPullback φ A.hom A₀.hom (spMap K₀.subtype) → ∃ s : Finset K, ∀ (K₁ : Subfield K) (h : K₀ ≤ K₁), (s : Set K) ⊆ K₁ → ∀ (A₁ : Over (Sp K₁)) (φ₁ : A₁.left ⟶ A₀.left) (ψ : A.left ⟶ A₁.left), IsPullback φ₁ A₁.hom A₀.hom (spMap (Subfield.inclusion h)) → ψ ≫ φ₁ = φ → ψ ≫ A₁.hom = A.hom ≫ spMap K₁.subtype → ∃ _ : GrpObj A₁, IsGrpPullback A A₁ (spMap K₁.subtype) ψ := by
  intro K _ K₀ A₀ A _ φ _ _ _ hφ
  have hw := hφ.w
  have hq : QuasiCompact (A₀ ⊗ A₀).hom := by
    rw [← Over.w (fst A₀ A₀)]
    exact (inferInstance : QuasiCompact (pullback.fst A₀.hom A₀.hom ≫ A₀.hom))
  have hs : QuasiSeparated (A₀ ⊗ A₀).hom := by
    rw [← Over.w (fst A₀ A₀)]
    exact (inferInstance : QuasiSeparated (pullback.fst A₀.hom A₀.hom ≫ A₀.hom))
  obtain ⟨s₁, H₁⟩ := T.exists_descent_of_morphisms_to_subfield K K₀ _ _ (A₀ ⊗ A₀).hom (A ⊗ A).hom (sq hw) _ A₀.hom Unit
    (fun _ => (μ[A]).left ≫ φ) (isPullback_sq hφ) (fun _ => by
      rw [Category.assoc, hw, ← Category.assoc, Over.w, (isPullback_sq hφ).w])
  obtain ⟨s₂, H₂⟩ := T.exists_descent_of_morphisms_to_subfield K K₀ _ _ A₀.hom A.hom φ _ A₀.hom Unit
    (fun _ => (ι[A]).left ≫ φ) hφ (fun _ => by
      rw [Category.assoc, hw, ← Category.assoc, Over.w])
  obtain ⟨s₃, H₃⟩ := T.exists_descent_of_morphisms_to_subfield K K₀ _ _ (𝟙 _) (𝟙 _) (spMap K₀.subtype) _ A₀.hom Unit
    (fun _ => (η[A]).left ≫ φ) (IsPullback.of_vert_isIso ⟨by simp⟩) (fun _ => by
      rw [Category.assoc, hw, ← Category.assoc, Over.w]; simp)
  classical
  refine ⟨s₁ ∪ s₂ ∪ s₃, fun K₁ h hs A₁ φ₁ ψ hφ₁ hψ hψw => ?_⟩
  simp only [Finset.coe_union, Set.union_subset_iff] at hs
  have hψp : IsPullback ψ A.hom A₁.hom (spMap K₁.subtype) :=
    IsPullback.of_right (by rwa [hψ, spMap_subtype]) hψw hφ₁
  obtain ⟨m, hm⟩ := H₁ K₁ h hs.1.1 _ (A₁ ⊗ A₁).hom (sq hφ₁.w) (sq hψw) (isPullback_sq hφ₁)
    (eq_sq hw ⟨by rw [Category.assoc, (isSquare_sq _).1, reassoc_of% (isSquare_sq hψw).1, hψ],
      by rw [Category.assoc, (isSquare_sq _).2, reassoc_of% (isSquare_sq hψw).2, hψ]⟩) (isPullback_sq hψp).w
  obtain ⟨i, hi⟩ := H₂ K₁ h hs.1.2 _ A₁.hom φ₁ ψ hφ₁ hψ hψw
  obtain ⟨e, he⟩ := H₃ K₁ h hs.2 _ (𝟙 _) (spMap (Subfield.inclusion h)) (spMap K₁.subtype)
    (IsPullback.of_vert_isIso ⟨by simp⟩) (spMap_subtype h) (by simp)
  have := flat_spMap K₁.subtype
  have := surjective_spMap K₁.subtype
  refine exists_grpObj _ hψp
    (Over.homMk (hφ₁.lift (m ()) (A₁ ⊗ A₁).hom ((hm ()).2.trans (isPullback_sq hφ₁).w)) (hφ₁.lift_snd _ _ _))
    (Over.homMk (hφ₁.lift (i ()) A₁.hom ((hi ()).2.trans hφ₁.w)) (hφ₁.lift_snd _ _ _))
    (Over.homMk (hφ₁.lift (e ()) (𝟙 _) ((he ()).2.trans (by simp))) (hφ₁.lift_snd _ _ _)) ?_ ?_ ?_
  · apply hφ₁.hom_ext
    · simp only [Over.homMk_left, Category.assoc, IsPullback.lift_fst, hψ]
      exact (hm ()).1
    · simp only [Over.homMk_left, Category.assoc, IsPullback.lift_snd, hψw]
      rw [(isPullback_sq hψp).w, ← Category.assoc, Over.w]
  · apply hφ₁.hom_ext
    · simp only [Over.homMk_left, Category.assoc, IsPullback.lift_fst, hψ]
      exact (hi ()).1
    · simp only [Over.homMk_left, Category.assoc, IsPullback.lift_snd, hψw]
      rw [← Category.assoc, Over.w]
  · apply hφ₁.hom_ext
    · simp only [Over.homMk_left, Category.assoc, IsPullback.lift_fst, hψ]
      exact (he ()).1
    · simp only [Over.homMk_left, Category.assoc, IsPullback.lift_snd, hψw]
      rw [← Category.assoc, Over.w]; simp

end GlobalTheory
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.HeckePoint

section Pts

variable {k : Type} [Field k] [IsAlgClosed k]

theorem hom_ext_pts {X Y : Over (Sp k)} (hX : Smooth X.hom) [IsSeparated Y.hom] {f g : X ⟶ Y}
    (h : ∀ x : 𝟙_ (Over (Sp k)) ⟶ X, x ≫ f = x ≫ g) : f = g := by
  have := (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field k _ X.hom hX).1
  exact Over.OverMorphism.ext (ComplexPoints.hom_ext_of_points X.hom Y.hom (by rw [Over.w, Over.w]) fun x hx =>
    congrArg (fun q => q.left) (h (Over.homMk x hx)))

theorem exists_lift_pt {S : Scheme.{0}} {A B : Over S} (ψ : A ⟶ B) [LocallyOfFiniteType ψ.left] [Surjective ψ.left]
    (t : Sp k ⟶ S) (y : Over.mk t ⟶ B) : ∃ x : Over.mk t ⟶ A, x ≫ ψ = y := by
  let y' : Sp k ⟶ B.left := y.left
  obtain ⟨z, -⟩ := (pullback.snd ψ.left y').surjective (default : PrimeSpectrum k)
  obtain ⟨x, hx, -⟩ := ComplexPoints.exists_point_mem (pullback.snd ψ.left y') (Z := Set.univ)
    isClosed_univ.isLocallyClosed ⟨z, trivial⟩
  have e : (x ≫ pullback.fst ψ.left y') ≫ ψ.left = y' := by
    rw [Category.assoc, pullback.condition, reassoc_of% hx]
  exact ⟨Over.homMk (x ≫ pullback.fst ψ.left y') (by rw [← Over.w ψ, ← Category.assoc, e]; exact Over.w y),
    Over.OverMorphism.ext e⟩

theorem exists_fac {A B Y : Over (Sp k)} [GrpObj A] [GrpObj B] [GrpObj Y] (hA : Smooth A.hom) [IsSeparated Y.hom]
    (ψ₀ : A ⟶ B) [IsMonHom ψ₀] [Etale ψ₀.left] [Surjective ψ₀.left] [QuasiCompact ψ₀.left] (ψ : A ⟶ Y) [IsMonHom ψ]
    (h : ∀ x : 𝟙_ (Over (Sp k)) ⟶ A, x ≫ ψ₀ = 1 → x ≫ ψ = 1) : ∃ α : B ⟶ Y, ψ₀ ≫ α = ψ := by
  let R : Over (Sp k) := Over.mk (pullback.fst ψ₀.left ψ₀.left ≫ A.hom)
  let p₁ : R ⟶ A := Over.homMk (pullback.fst _ _) rfl
  let p₂ : R ⟶ A := Over.homMk (pullback.snd _ _) (by
    show _ = pullback.fst ψ₀.left ψ₀.left ≫ A.hom
    rw [← Over.w ψ₀, ← pullback.condition_assoc])
  have e₀ : p₁ ≫ ψ₀ = p₂ ≫ ψ₀ := Over.OverMorphism.ext pullback.condition
  have e : p₁ ≫ ψ = p₂ ≫ ψ := hom_ext_pts (inferInstanceAs (Smooth (pullback.fst ψ₀.left ψ₀.left ≫ A.hom))) fun x => by
    have := h ((x ≫ p₁) * (x ≫ p₂)⁻¹) (by
      rw [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, e₀, Category.assoc, mul_inv_cancel])
    rw [MonObj.mul_comp, GrpObj.inv_comp, mul_inv_eq_one, Category.assoc, Category.assoc] at this
    exact this
  have e' : pullback.fst ψ₀.left ψ₀.left ≫ ψ.left = pullback.snd ψ₀.left ψ₀.left ≫ ψ.left :=
    congrArg (fun q => q.left) e
  have hd : ∀ {Z : Scheme.{0}} (g₁ g₂ : Z ⟶ A.left), g₁ ≫ ψ₀.left = g₂ ≫ ψ₀.left → g₁ ≫ ψ.left = g₂ ≫ ψ.left :=
    fun g₁ g₂ hg => by
      rw [← pullback.lift_fst g₁ g₂ hg, Category.assoc, e', pullback.lift_snd_assoc]
  have f := EffectiveEpi.fac ψ₀.left ψ.left hd
  refine ⟨Over.homMk (EffectiveEpi.desc ψ₀.left ψ.left hd) ?_, Over.OverMorphism.ext f⟩
  rw [← cancel_epi ψ₀.left, reassoc_of% f, Over.w, Over.w]

theorem isIso_of_mono {A B : Over (Sp k)} (α : A ⟶ B) [IsProper A.hom] [IsSeparated B.hom] (hB : Smooth B.hom)
    [Mono α.left] (h : ∀ y : 𝟙_ (Over (Sp k)) ⟶ B, ∃ x, x ≫ α = y) : IsIso α := by
  have := (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field k _ B.hom hB).1
  have : IsProper (α.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : IsProper α.left := IsProper.of_comp α.left B.hom
  have : IsClosedImmersion α.left := (IsClosedImmersion.iff_isProper_and_mono _).2 ⟨‹_›, ‹_›⟩
  have : Surjective α.left := ComplexPoints.surjective_of_geomPoints_lift B.hom (𝟙 (Sp k)) α.left
    α.left.isClosedEmbedding.isClosed_range fun y hy => by
      obtain ⟨x, hx⟩ := h (Over.homMk y hy)
      exact ⟨x.left, congrArg (fun q => q.left) hx⟩
  have : IsIso α.left := isIso_of_isClosedImmersion_of_surjective _
  have : IsIso ((Over.forget _).map α) := ‹_›
  exact isIso_of_reflects_iso α (Over.forget _)


omit [IsAlgClosed k] in
theorem toUnit_comp_injective {K : Type} [Field K] (x : Sp K ⟶ Sp k) (A : Over (Sp k)) :
    Function.Injective (fun z : 𝟙_ (Over (Sp k)) ⟶ A => toUnit (Over.mk x) ≫ z) := by
  have : Surjective x := ⟨fun z => ⟨(default : PrimeSpectrum K), Subsingleton.elim (α := PrimeSpectrum k) _ _⟩⟩
  have : Epi x := Flat.epi_of_flat_of_surjective x
  intro a b h
  have e : (toUnit (Over.mk x)).left = x := by simp
  have h' : (toUnit (Over.mk x)).left ≫ a.left = (toUnit (Over.mk x)).left ≫ b.left := congrArg (fun q => q.left) h
  rw [e] at h'
  exact Over.OverMorphism.ext ((cancel_epi x).1 h')

theorem exists_of_torsion (hM : Out.MulNSt) (P : Out.PolAV (Sp k)) {K : Type} [Field K] [IsAlgClosed K]
    (x : Sp K ⟶ Sp k) {n : ℕ} (hk : (n : k) ≠ 0) (hK : (n : K) ≠ 0) (z : Over.mk x ⟶ P.A) (hz : z ^ n = 1) :
    ∃ z₀ : 𝟙_ (Over (Sp k)) ⟶ P.A, toUnit (Over.mk x) ≫ z₀ = z := by
  have hn : 1 ≤ n := Nat.pos_of_ne_zero (by rintro rfl; exact hk Nat.cast_zero)
  have c₁ : Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ P.A // x ^ n = 1} = n ^ (2 * P.g) := (hM _ P n hn).2.2.2.2 k (𝟙 _) hk
  have c₂ := (hM _ P n hn).2.2.2.2 K x hK
  have : Finite {y : Over.mk x ⟶ P.A // y ^ n = 1} := Nat.finite_of_card_ne_zero (by rw [c₂]; positivity)
  let F : {x : 𝟙_ (Over (Sp k)) ⟶ P.A // x ^ n = 1} → {y : Over.mk x ⟶ P.A // y ^ n = 1} := fun a =>
    ⟨toUnit _ ≫ a.1, by rw [← MonObj.comp_pow, a.2, MonObj.comp_one]⟩
  have hF : Function.Bijective F := (Nat.bijective_iff_injective_and_card F).2
    ⟨fun a b h => Subtype.ext (toUnit_comp_injective x _ (congrArg Subtype.val h)), c₁.trans c₂.symm⟩
  obtain ⟨a, ha⟩ := hF.2 ⟨z, hz⟩
  exact ⟨a.1, congrArg Subtype.val ha⟩

end Pts

theorem exists_ptsEquiv {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') (y : T.left ⟶ S) (e : T.hom ≫ f = y) :
    ∃ ρ : (T ⟶ G') ≃* (Over.mk y ⟶ G), ∀ x, (ρ x).left = x.left ≫ φ := by
  subst e
  refine ⟨MulEquiv.ofBijective (pushHom h T) ⟨fun a b e => Over.OverMorphism.ext
    (h.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w])), fun z => ?_⟩, fun _ => rfl⟩
  exact ⟨Over.homMk (h.1.lift z.left T.hom (Over.w z)) (h.1.lift_snd _ _ _), Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩

theorem unitOn_bijective (R : Type) [CommRing R] : Function.Bijective (unitOn (R := R)) :=
  (Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.toMulEquiv).bijective

theorem unitOn_pow {R : Type} [CommRing R] (c : Rˣ) (n : ℕ) : unitOn (c ^ n) = unitOn c ^ n := map_pow _ _ _

theorem unitOn_one {R : Type} [CommRing R] : unitOn (1 : Rˣ) = 1 := map_one _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem isAbelianScheme_of_proper {S : Scheme.{0}} (t : SAB H S) (hp : IsProper t.G.hom) : IsAbelianScheme t.G :=
  ⟨inferInstance, t.semi.smooth, hp, t.semi.geomConnected⟩

theorem exists_dim {k : Type} [Field k] (t : SAB H (Sp k)) : ∃ g, SmoothOfRelativeDimension g t.G.hom := by
  have := t.semi.smooth
  have := t.semi.geomConnected
  have : ConnectedSpace t.G.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := t.G.hom) (𝟙 _) (𝟙 _) t.G.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  exact exists_dim_of_preconnected t.G.hom (eSec t.G (default : PrimeSpectrum k))

abbrev polOf {S : Scheme.{0}} (t : SAB H S) (hp : IsProper t.G.hom) (ha : Out.RelAmple t.G t.PP.L)
    (hk : Out.KTriv t.G t.PP.L) {g : ℕ} (hg : SmoothOfRelativeDimension g t.G.hom) : Out.PolAV S where
  A := t.G
  isAb := isAbelianScheme_of_proper t hp
  g := g
  smoothDim := hg
  L := t.PP.L
  isLB := t.PP.isLB
  rigid := ⟨t.PP.rig, t.PP.rigGen⟩
  sym := fun _ => ⟨⊤, trivial, by
    obtain ⟨-, ws, gs', -⟩ := t.sym
    exact gen_of_iso ((isGen_iff ws).1 gs') _⟩
  ample := ha
  ktriv := hk

end GlobalTheory.HeckePoint
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory

theorem eq_one_of_surjective_appTop_of_section {X S : Scheme.{0}} (p : X ⟶ S) (o : S ⟶ X) (ho : o ≫ p = 𝟙 S)
    (hs : Function.Surjective p.appTop.hom) (a : Γ(X, ⊤)) (ha : o.appTop.hom a = 1) : a = 1 := by
  obtain ⟨b, rfl⟩ := hs a
  have e : o.appTop.hom (p.appTop.hom b) = b := by
    rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop, ho, Scheme.Hom.id_appTop]
    rfl
  rw [e.symm.trans ha, map_one]

theorem exists_sabMap_of_isProper_of_lbIso : Out.GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (t : SAB H S) (t' : SAB H S') (f : S' ⟶ S) (φ : t'.G.left ⟶ t.G.left), IsProper t.G.hom → IsGrpPullback t'.G t.G f φ → LBIso t'.PP.L (t.PP.L.pull φ) → (∀ a, (t'.act.act a).left ≫ φ = φ ≫ (t.act.act a).left) → ∃ m : SABMap t' t f, m.φ = φ := by
  intro hG E _ _ _ H S S' t t' f φ hp gp ⟨w, hw⟩ hact
  obtain ⟨w', hw', Hr⟩ := TripleMap.exists_rigidified t.PP.isLB t'.PP.isLB w ((isGen_iff w).1 hw) (eSec t.G)
    (eSec t'.G) t'.G.hom (Over.w _) f (cubeMapOf gp).e_comm t.PP.rig t.PP.rigGen t'.PP.rig t'.PP.rigGen
  have hp' : IsProper t'.G.hom := MorphismProperty.of_isPullback gp.1 hp
  have hA := AbelianSchemeGerms.isAbelianScheme_of_proper t'.G t'.semi
  have hA₃ := AbelianSchemeGerms.isAbelianScheme_tensor _ _ hA (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hA hA)
  refine ⟨⟨cubeMapOf gp, gp, rfl, hact, (isPullCubical_iff _ _ _).2 ⟨w', hw', Hr,
    TripleMap.pmaps_cubical gp t.cub t'.cub hw' fun a ha => ?_⟩⟩, rfl⟩
  let o := lift (1 : 𝟙_ (Over S') ⟶ t'.G) (lift (1 : 𝟙_ (Over S') ⟶ t'.G) (1 : 𝟙_ (Over S') ⟶ t'.G))
  have h₁ : pullU o.left ⊤ a = 1 := unit_ext fun y _ =>
    (gm_pull (𝟙 _) o.left y ⊤ trivial a).trans ((congrArg (fun q => gm q y ⊤ a) (Category.id_comp _)).trans
      ((ha y).trans (map_one _).symm))
  exact Units.ext (eq_one_of_surjective_appTop_of_section (G3 t'.G).hom o.left (Over.w o) (hG _ _ hA₃).2 a.val
    (congrArg Units.val h₁))

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.exists_gen_of_rigidified_faithfullyFlat_descent : Out.GlobalFnsSt → ∀ (S S' : Scheme.{0}) (π : S' ⟶ S) (A : Over S) [GrpObj A] (N : LB A.left), IsAbelianScheme A → N.IsLB → Flat π → Surjective π → QuasiCompact π → (∃ t : (N.pull (eSec A)).Gen, t.IsGen) → (∃ t : (N.pull (pullback.fst A.hom π)).Gen, t.IsGen) → ∃ t : N.Gen, t.IsGen := by
  first | exact @GlobalTheory.exists_gen_of_rigidified_of_flat_baseChange | exact GlobalTheory.exists_gen_of_rigidified_of_flat_baseChange | (intros; apply GlobalTheory.exists_gen_of_rigidified_of_flat_baseChange <;> assumption)
end
