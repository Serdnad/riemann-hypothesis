module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import ReciprocityTheory.ThetaQuasiPeriods.PeriodLattice
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory

namespace PointwiseRegular

theorem hom_ext {X Y : Scheme.{0}} (p : Y ⟶ Sp ℂ) [LocallyOfFiniteType p] [IsReduced Y] {f g : Y ⟶ X}
    (h : ∀ y : Sp ℂ ⟶ Y, y ≫ p = 𝟙 _ → y ≫ f = y ≫ g) : f = g := by
  refine Scheme.hom_ext_of_forall _ _ fun z => ?_
  obtain ⟨_, ⟨D, hD, rfl⟩, hz, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f z)) isOpen_univ
  have hle : f ⁻¹ᵁ D ≤ g ⁻¹ᵁ D := ComplexPoints.opens_le_of_complexPoints p _ _ fun y hy hyD => by
    rw [← top_le_preimage_comp] at hyD ⊢
    rwa [← h y hy]
  refine ⟨f ⁻¹ᵁ D, hz, ?_⟩
  have : IsAffine (Scheme.Opens.toScheme (X := X) D) := hD
  have key : f.resLE D (f ⁻¹ᵁ D) le_rfl = g.resLE D (f ⁻¹ᵁ D) hle := by
    refine ComplexPoints.hom_ext_of_points ((f ⁻¹ᵁ D).ι ≫ p) (terminal.from _) (terminal.hom_ext _ _) fun x hx => ?_
    rw [← cancel_mono (Scheme.Opens.ι (X := X) D), Category.assoc, Category.assoc, Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι,
      ← Category.assoc, ← Category.assoc]
    exact h _ (by rw [Category.assoc]; exact hx)
  rw [← Scheme.Hom.resLE_comp_ι f le_rfl, key, Scheme.Hom.resLE_comp_ι]

def ofRingHom {X Y : Scheme.{0}} (U : Y.Opens) {D : X.Opens} (hD : IsAffineOpen D) (r : Γ(X, D) →+* Γ(Y, U)) :
    U.toScheme ⟶ X :=
  U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom r) ≫ hD.fromSpec

theorem top_le_preimage_ι {Y : Scheme.{0}} (U : Y.Opens) (y : Sp ℂ ⟶ U.toScheme) : ⊤ ≤ (y ≫ U.ι) ⁻¹ᵁ U := by
  rw [top_le_preimage_comp]
  simp

theorem comp_ofRingHom {X Y : Scheme.{0}} (U : Y.Opens) {D : X.Opens} (hD : IsAffineOpen D)
    (r : Γ(X, D) →+* Γ(Y, U)) (y : Sp ℂ ⟶ U.toScheme) (x : Sp ℂ ⟶ X) (hx : ⊤ ≤ x ⁻¹ᵁ D)
    (h : ∀ φ, valAt' (y ≫ U.ι) U (r φ) = valAt' x D φ) : y ≫ ofRingHom U hD r = x := by
  have hy := top_le_preimage_ι U y
  have e1 : CommRingCat.ofHom r ≫ (y ≫ U.ι).appLE U ⊤ hy = x.appLE D ⊤ hx := by
    rw [← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom]
    ext φ
    have := h φ
    rw [valAt'_eq_valAt _ hy, valAt'_eq_valAt _ hx] at this
    exact this
  have e2 : (isAffineOpen_top (Sp ℂ)).fromSpec ≫ y ≫ U.toSpecΓ = Spec.map ((y ≫ U.ι).appLE U ⊤ hy) := by
    rw [IsAffineOpen.fromSpec_top, Iso.inv_comp_eq, Scheme.Opens.toSpecΓ, Scheme.toSpecΓ_naturality_assoc,
      ← Spec.map_comp]
    congr 2
    rw [← Scheme.Hom.appLE_comp_appLE y U.ι U ⊤ ⊤ (by simp) le_top, Scheme.Opens.ι_appLE, Scheme.Hom.appTop,
      Scheme.Hom.app_eq_appLE]
    rfl
  have : IsIso (isAffineOpen_top (Sp ℂ)).fromSpec := by
    rw [IsAffineOpen.fromSpec_top]; infer_instance
  rw [← cancel_epi (isAffineOpen_top (Sp ℂ)).fromSpec, ← hD.SpecMap_appLE_fromSpec x _ hx, ← e1, ofRingHom,
    reassoc_of% e2, Spec.map_comp_assoc]

theorem exists_ringHom {X Y : Over (Sp ℂ)} [IsReduced Y.left] [LocallyOfFiniteType Y.hom]
    (F : (𝟙_ (Over (Sp ℂ)) ⟶ Y) → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (U : Y.left.Opens) (D : X.left.Opens)
    (hF : ∀ y : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ⊤ ≤ y.left ⁻¹ᵁ U → ⊤ ≤ (F y).left ⁻¹ᵁ D)
    (h : ∀ φ : Γ(X.left, D), ∃ ρ : Γ(Y.left, U), ∀ y : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ⊤ ≤ y.left ⁻¹ᵁ U →
      valAt' y.left U ρ = valAt' (F y).left D φ) :
    ∃ r : Γ(X.left, D) →+* Γ(Y.left, U), ∀ φ, ∀ y : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ⊤ ≤ y.left ⁻¹ᵁ U →
      valAt' y.left U (r φ) = valAt' (F y).left D φ := by
  choose r hr using h
  have ext : ∀ a b : Γ(Y.left, U), (∀ y : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ⊤ ≤ y.left ⁻¹ᵁ U →
      valAt' y.left U a = valAt' y.left U b) → a = b := fun a b hab =>
    ComplexPoints.eq_of_valAt'_eq Y.hom U a b fun x hx hU => hab (Over.homMk x hx) hU
  refine ⟨⟨⟨⟨r, ?_⟩, ?_⟩, ?_, ?_⟩, hr⟩
  · exact ext _ _ fun y hy => by
      rw [hr _ y hy]; exact (valAt'_one _ (hF y hy)).trans (valAt'_one _ hy).symm
  · exact fun a b => ext _ _ fun y hy => by
      refine (hr _ y hy).trans (((valAt'_mul _ _ _ _).trans ?_).trans (valAt'_mul _ _ _ _).symm)
      rw [hr _ y hy, hr _ y hy]
  · exact ext _ _ fun y hy => (hr _ y hy).trans ((valAt'_zero _ _).trans (valAt'_zero _ _).symm)
  · exact fun a b => ext _ _ fun y hy => by
      refine (hr _ y hy).trans (((valAt'_add _ _ _ _).trans ?_).trans (valAt'_add _ _ _ _).symm)
      exact congrArg₂ (· + ·) (hr _ y hy).symm (hr _ y hy).symm

theorem existsUnique_hom {X Y : Over (Sp ℂ)} [IsReduced Y.left] [LocallyOfFiniteType Y.hom]
    (F : (𝟙_ (Over (Sp ℂ)) ⟶ Y) → (𝟙_ (Over (Sp ℂ)) ⟶ X))
    (h : ∀ y : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ∃ (U : Y.left.Opens) (D : X.left.Opens), ⊤ ≤ y.left ⁻¹ᵁ U ∧ IsAffineOpen D ∧
      (∀ y' : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ⊤ ≤ y'.left ⁻¹ᵁ U → ⊤ ≤ (F y').left ⁻¹ᵁ D) ∧
      ∀ φ : Γ(X.left, D), ∃ ρ : Γ(Y.left, U), ∀ y' : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ⊤ ≤ y'.left ⁻¹ᵁ U →
        valAt' y'.left U ρ = valAt' (F y').left D φ) :
    ∃! m : Y ⟶ X, ∀ y, y ≫ m = F y := by
  choose U D hU hD hF hρ using h
  have loc : ∀ i, ∃ m : (U i).toScheme ⟶ X.left, ∀ (z : Sp ℂ ⟶ (U i).toScheme) (y : 𝟙_ (Over (Sp ℂ)) ⟶ Y),
      y.left = z ≫ (U i).ι → z ≫ m = (F y).left := fun i => by
    obtain ⟨r, hr⟩ := exists_ringHom F (U i) (D i) (hF i) (hρ i)
    refine ⟨ofRingHom (U i) (hD i) r, fun z y hy => ?_⟩
    have hyU : ⊤ ≤ y.left ⁻¹ᵁ U i := by rw [hy]; exact top_le_preimage_ι _ z
    refine comp_ofRingHom _ _ r z _ (hF i y hyU) fun φ => ?_
    rw [← hr φ y hyU, hy]
  choose m hm using loc
  have hcov : TopologicalSpace.IsOpenCover U :=
    ComplexPoints.iSup_eq_top_of_complexPoints Y.hom U fun x hx => ⟨Over.homMk x hx, hU _⟩
  let 𝒰 := Y.left.openCoverOfIsOpenCover U hcov
  have hc : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ m i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ m j := fun i j => by
    have : IsReduced (pullback (𝒰.f i) (𝒰.f j)) :=
      isReduced_of_isOpenImmersion (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i)
    refine hom_ext ((pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i) ≫ Y.hom) fun z hz => ?_
    let y : 𝟙_ (Over (Sp ℂ)) ⟶ Y := Over.homMk (z ≫ pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i)
      ((Category.assoc _ _ _).trans hz)
    refine (Category.assoc _ _ _).symm.trans (Eq.trans ?_ (Category.assoc _ _ _))
    refine (hm i _ y (Category.assoc _ _ _).symm).trans (hm j _ y ?_).symm
    change z ≫ pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i = (z ≫ pullback.snd (𝒰.f i) (𝒰.f j)) ≫ 𝒰.f j
    rw [pullback.condition, Category.assoc]
  have hg : ∀ y : 𝟙_ (Over (Sp ℂ)) ⟶ Y, y.left ≫ 𝒰.glueMorphisms m hc = (F y).left := fun y => by
    have hr : Set.range y.left ⊆ Set.range (U y).ι := by
      rintro _ ⟨a, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hU y (Set.mem_univ a)
    have e := IsOpenImmersion.lift_fac (U y).ι y.left hr
    have e2 : (U y).ι ≫ 𝒰.glueMorphisms m hc = m y := 𝒰.ι_glueMorphisms m hc y
    refine Eq.trans ?_ (hm y _ y e.symm)
    rw [← e2, ← Category.assoc, e]
  have hw : 𝒰.glueMorphisms m hc ≫ X.hom = Y.hom := by
    refine hom_ext Y.hom fun z hz => ?_
    have := hg (Over.homMk z hz)
    rw [hz, ← Category.assoc]
    exact (congrArg (· ≫ X.hom) this).trans (Over.w (F _))
  refine ⟨Over.homMk _ hw, fun y => Over.OverMorphism.ext (hg y), fun m' hm' => Over.OverMorphism.ext ?_⟩
  refine hom_ext Y.hom fun z hz => ?_
  exact (congrArg (fun φ => φ.left) (hm' (Over.homMk z hz))).trans (hg (Over.homMk z hz)).symm

end PointwiseRegular

theorem existsUnique_hom_of_locally_regular : (∀ (X : Over (Sp ℂ)) (U : X.left.Opens), IsAffineOpen U → ∀ e : Γ(X.left, U) →+* ℂ, (∀ a, e (constFn X.hom U a) = a) → ∃! x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ (x).left ⁻¹ᵁ U ∧ ∀ f, valAt' x.left U f = e f) → (∀ (X : Over (Sp ℂ)), IsReduced X.left → LocallyOfFiniteType X.hom → ∀ (U : X.left.Opens) (f f' : Γ(X.left, U)), (∀ x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ (x).left ⁻¹ᵁ U → valAt' x.left U f = valAt' x.left U f') → f = f') → (∀ (X Y : Over (Sp ℂ)), IsReduced Y.left → LocallyOfFiniteType Y.hom → ∀ F : (𝟙_ (Over (Sp ℂ)) ⟶ Y) → (𝟙_ (Over (Sp ℂ)) ⟶ X), (∀ y : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ∃ (U : Y.left.Opens) (D : X.left.Opens), ⊤ ≤ (y).left ⁻¹ᵁ U ∧ IsAffineOpen D ∧ (∀ y' : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ⊤ ≤ (y').left ⁻¹ᵁ U → ⊤ ≤ (F y').left ⁻¹ᵁ D) ∧ ∀ φ : Γ(X.left, D), ∃ ρ : Γ(Y.left, U), ∀ y' : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ⊤ ≤ (y').left ⁻¹ᵁ U → valAt' y'.left U ρ = valAt' (F y').left D φ) → ∃! m : Y ⟶ X, ∀ y, y ≫ m = F y) :=
  fun _ _ _ _ _ _ F h => PointwiseRegular.existsUnique_hom F h

end GlobalTheory
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory

def thetaZeroSec {X : Scheme.{0}} (L : LB X) : L.Sec where
  f _ := 0
  compat := by intros; simp

theorem valAt'_zero_fn {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (U : X.Opens) : valAt' x U 0 = 0 := by
  unfold valAt'
  split_ifs with h
  · simp [valAt]
  · rfl

theorem isAH_of_polarisation :
    (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)) → (∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ) (Ef : LinearMap.BilinForm ℤ Λ) (θ : (Fin g → ℂ) → ℂ), Hm.IsHermitian → (∀ l, ‖χ l‖ = 1) → (∀ l m : Λ, (Ef l m : ℝ) = ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im) → Function.Injective Ef → Differentiable ℂ θ → θ ≠ 0 → (∀ (l : Λ) z, θ (z + l) = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) + Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))) * θ z) → ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) → (∀ (P : Out.PolAV (Sp ℂ)) (n : ℕ), 1 ≤ n → ∃ s : Fin (n ^ P.g) → (lbPow P.L n).Sec, ∀ a : Fin (n ^ P.g) → ℂ, (∀ j, ∑ i, constFn P.A.hom _ (a i) * (s i).f j = 0) → a = 0) → (∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ), (Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : u.Λ, (Ef l m : ℝ) = ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin P.g → ℂ))).im) ∧ ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))) + Real.pi / 2 * ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))))) * u.fr i (z + l)) → ∀ n : ℕ, (∀ s, ∃! θ, u.IsThetaFn Hm χ n θ ∧ u.IsFnPow n s θ) ∧ ∀ θ s s', u.IsFnPow n s θ → u.IsFnPow n s' θ → s = s') → (∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ), (Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : u.Λ, (Ef l m : ℝ) = ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin P.g → ℂ))).im) ∧ ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))) + Real.pi / 2 * ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))))) * u.fr i (z + l)) → Function.Bijective Ef → u.IsAH Hm χ) := by
  intro _ hpos hsec hthe P u Hm χ Ef hAH hbij
  obtain ⟨hH, hχ, hE, hfr⟩ := hAH
  refine ⟨hH, ?_, hχ, hfr⟩

  obtain ⟨s, hs⟩ := hsec P 1 le_rfl
  have hone : ∀ i j : Fin (1 ^ P.g), i = j := fun i j =>
    Fin.ext (by
      have hi : (i : ℕ) < 1 := lt_of_lt_of_eq i.isLt (one_pow _)
      have hj : (j : ℕ) < 1 := lt_of_lt_of_eq j.isLt (one_pow _)
      omega)
  let i0 : Fin (1 ^ P.g) := ⟨0, by rw [one_pow]; exact Nat.one_pos⟩
  have hcorr := hthe P u Hm χ Ef ⟨hH, hχ, hE, hfr⟩ 1
  obtain ⟨θ, ⟨hθ, hfn⟩, -⟩ := hcorr.1 (s i0)

  have hθne : θ ≠ 0 := by
    rintro rfl
    have hz : u.IsFnPow 1 (thetaZeroSec (lbPow P.L 1)) 0 := by
      intro j z _
      rw [Pi.zero_apply, zero_mul]
      exact valAt'_zero_fn _ _
    have hs0 : s i0 = thetaZeroSec (lbPow P.L 1) := hcorr.2 0 _ _ hfn hz
    have hall : ∀ i, s i = thetaZeroSec (lbPow P.L 1) := fun i => by rw [hone i i0, hs0]
    have h1 := hs (fun _ => 1) (fun j => Finset.sum_eq_zero (fun i _ => by rw [hall i]; exact mul_zero _))
    exact absurd (congrFun h1 i0) (by simp)

  exact hpos P.g u.Λ u.discrete u.full Hm χ Ef θ hH hχ hE hbij.1 hθ.1 hθne
    (fun l z => by have h := hθ.2 l z; rw [pow_one] at h; exact h)

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory

section
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem holUnif_ex_zero_eq_one : u.ex 0 = 1 :=
  (u.ker 0).2 (zero_mem _)

theorem holUnif_ex_nsmul_eq_pow (z : Fin g → ℂ) (k : ℕ) : u.ex (k • z) = u.ex z ^ k := by
  induction k with
  | zero => rw [zero_smul, pow_zero]; exact (u.ker 0).2 (zero_mem _)
  | succ n ih => rw [succ_nsmul, u.ex_add, ih, pow_succ]

theorem holUnif_isZLattice : haveI := u.discrete; IsZLattice ℝ u.Λ := by
  have := u.discrete
  exact ⟨u.full⟩

end

theorem riemannForm_bijective_of_weilNondeg :
    Out.WeilNondegSt → (∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (E : LinearMap.BilinForm ℤ X), (∀ (k : ℕ) (a : X), 0 < k → (∀ b, (k : ℤ) ∣ E a b) → ∃ a', a = (k : ℤ) • a') → Function.Bijective E) → (∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ), (Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : u.Λ, (Ef l m : ℝ) = ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin P.g → ℂ))).im) ∧ ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))) + Real.pi / 2 * ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))))) * u.fr i (z + l)) → ∀ (k : ℕ) (a b : u.Λ) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (Ef a b : ℂ) / k) → Out.WeilIs P.A P.L k (u.ex ((k : ℂ)⁻¹ • (a : Fin P.g → ℂ))) (u.ex ((k : ℂ)⁻¹ • (b : Fin P.g → ℂ))) (unitOn c)) → (∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ), (Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : u.Λ, (Ef l m : ℝ) = ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin P.g → ℂ))).im) ∧ ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))) + Real.pi / 2 * ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))))) * u.fr i (z + l)) → Function.Bijective Ef) := by
  intro hW hB hE P u Hm χ Ef hc
  have := u.discrete
  have := holUnif_isZLattice u
  apply hB u.Λ Ef
  intro k a hk hdiv
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'

  have hpow : ∀ w : Fin P.g → ℂ, u.ex w ^ k = u.ex ((k : ℂ) • w) := by
    intro w
    rw [← holUnif_ex_nsmul_eq_pow, Nat.cast_smul_eq_nsmul]
  have hx : u.ex ((k : ℂ)⁻¹ • (a : Fin P.g → ℂ)) = 1 := by
    refine hW ℂ P k hk0 _ ?_ ?_
    · rw [hpow, smul_smul, mul_inv_cancel₀ hk0, one_smul]
      exact (u.ker _).2 a.2
    · intro y hy
      obtain ⟨w, rfl⟩ := u.ex_onto y
      have hw : (k : ℂ) • w ∈ u.Λ := (u.ker _).1 (by rw [← hpow]; exact hy)
      set b : u.Λ := ⟨(k : ℂ) • w, hw⟩
      have hwb : w = (k : ℂ)⁻¹ • (b : Fin P.g → ℂ) := by
        simp only [b, smul_smul, inv_mul_cancel₀ hk0, one_smul]
      obtain ⟨m, hm⟩ := hdiv b
      have h1 := hE P u Hm χ Ef hc k a b 1 hk (by
        rw [hm, Units.val_one]
        push_cast
        rw [show -(2 * (Real.pi : ℂ) * Complex.I) * ((k : ℂ) * (m : ℂ)) / (k : ℂ)
            = (-m : ℤ) * (2 * Real.pi * Complex.I) by push_cast; field_simp]
        exact (Complex.exp_int_mul_two_pi_mul_I (-m)).symm)
      have hu : unitOn (1 : ℂˣ) = 1 := map_one _
      rw [hu, ← hwb] at h1
      exact h1
  refine ⟨⟨(k : ℂ)⁻¹ • (a : Fin P.g → ℂ), (u.ker _).1 hx⟩, ?_⟩
  ext1
  simp only [Submodule.coe_smul, ← Int.cast_smul_eq_zsmul ℂ, Int.cast_natCast, smul_smul,
    mul_inv_cancel₀ hk0, one_smul]

end GlobalTheory
end
