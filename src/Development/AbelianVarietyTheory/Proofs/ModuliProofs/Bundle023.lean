module

public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle010
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle009
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.DedekindDomain.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
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
import Mathlib.Tactic.Lemma
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.TUniq
variable {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k} {S S' : Scheme.{0}} {s : S ⟶ Sp o} {s' : S' ⟶ Sp o}

def MapBy (t' : TObj g k J b s') (t : TObj g k J b s) (f : S' ⟶ S) (φ : t'.A.left ⟶ t.A.left) : Prop :=
  IsGrpPullback t'.A t.A f φ ∧ LBIso t'.L (t.L.pull φ) ∧
    (∀ i, (t'.pt i).left ≫ φ = f ≫ (t.pt i).left) ∧ ∀ j, (t'.act j).left ≫ φ = φ ≫ (t.act j).left

theorem tMap_iff (t' : TObj g k J b s') (t : TObj g k J b s) (f : S' ⟶ S) : TMap t' t f ↔ ∃ φ, MapBy t' t f φ := Iff.rfl

def GeoGood (t t' : TObj g k J b s) (Sg : Set S) : Prop :=
  ∀ (K : Type) [Field K] (x : Sp K ⟶ S), Set.range x ⊆ Sg →
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (i : K →+* Ω) (su : Sp Ω ⟶ Sp o) (u : TObj g k J b su)
      (ψ : u.A.left ⟶ t.A.left) (ψ' : u.A.left ⟶ t'.A.left),
      MapBy u t (spMap i ≫ x) ψ ∧ MapBy u t' (spMap i ≫ x) ψ'

theorem GeoGood.symm {t t' : TObj g k J b s} {Sg : Set S} (h : GeoGood t t' Sg) : GeoGood t' t Sg := fun K _ x hx => by
  obtain ⟨Ω, _, _, i, su, u, ψ, ψ', h₁, h₂⟩ := h K x hx
  exact ⟨Ω, inferInstance, inferInstance, i, su, u, ψ', ψ, h₂, h₁⟩

def Compat (t t' : TObj g k J b s) {X : Scheme.{0}} (c₀ : X ⟶ t.A.left) (f : X ⟶ t'.A.left) : Prop :=
  f ≫ t'.A.hom = c₀ ≫ t.A.hom ∧
    ∀ (K : Type) [Field K] [IsAlgClosed K] (su : Sp K ⟶ Sp o) (u : TObj g k J b su) (x : Sp K ⟶ S)
      (ψ : u.A.left ⟶ t.A.left) (ψ' : u.A.left ⟶ t'.A.left), MapBy u t x ψ → MapBy u t' x ψ' →
      ∀ (B : Type) [Field B] (z : Sp B ⟶ u.A.left) (y : Sp B ⟶ X), y ≫ c₀ = z ≫ ψ → y ≫ f = z ≫ ψ'

theorem epi_spMap {K Ω : Type} [Field K] [Field Ω] (i : K →+* Ω) : Epi (spMap i) := by
  have : Flat (spMap i) := by
    refine (HasRingHomProperty.Spec_iff (P := @Flat)).2 ?_
    letI := i.toAlgebra
    exact (inferInstance : Module.Flat K Ω)
  have : Surjective (spMap i) := ⟨fun p => ⟨(default : PrimeSpectrum Ω), Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem ext_of_geoGood {t t' : TObj g k J b s} {Sg : Set S} (hd : Dense Sg) (hg : GeoGood t t' Sg) {X Y : Scheme.{0}}
    [IsReduced X] (p : X ⟶ S) [Flat p] [LocallyOfFinitePresentation p] (q : Y ⟶ S) [IsSeparated q] {f f' : X ⟶ Y}
    (hf : f ≫ q = p) (hf' : f' ≫ q = p)
    (H : ∀ (K : Type) [Field K] [IsAlgClosed K] (su : Sp K ⟶ Sp o) (u : TObj g k J b su) (x : Sp K ⟶ S)
      (ψ : u.A.left ⟶ t.A.left) (ψ' : u.A.left ⟶ t'.A.left), MapBy u t x ψ → MapBy u t' x ψ' →
      ∀ y : Sp K ⟶ X, y ≫ p = x → y ≫ f = y ≫ f') : f = f' := by
  refine (GlobalTheory.dense_fibres_ext X S p Sg hd).2.1 Y q f f' hf hf' fun K _ _ y hy => ?_
  obtain ⟨Ω, _, _, i, su, u, ψ, ψ', h₁, h₂⟩ := hg K (y ≫ p) hy
  have := epi_spMap i
  rw [← cancel_epi (spMap i), ← Category.assoc, ← Category.assoc]
  exact H Ω su u _ ψ ψ' h₁ h₂ _ (Category.assoc _ _ _)

theorem Compat.unique {t t' : TObj g k J b s} {Sg : Set S} (hd : Dense Sg) (hg : GeoGood t t' Sg) {X : Scheme.{0}}
    [IsReduced X] {c₀ : X ⟶ t.A.left} [Flat (c₀ ≫ t.A.hom)] [LocallyOfFinitePresentation (c₀ ≫ t.A.hom)]
    {f f' : X ⟶ t'.A.left} (h : Compat t t' c₀ f) (h' : Compat t t' c₀ f') : f = f' := by
  have := t'.ab.proper
  refine ext_of_geoGood hd hg (c₀ ≫ t.A.hom) t'.A.hom h.1 h'.1 fun K _ _ su u x ψ ψ' h₁ h₂ y hy => ?_
  have w : (y ≫ c₀) ≫ t.A.hom = 𝟙 _ ≫ x := by rw [Category.assoc, hy, Category.id_comp]
  have e := (h₁.1.1.lift_fst _ _ w).symm
  exact (h.2 K su u x ψ ψ' h₁ h₂ K _ y e).trans (h'.2 K su u x ψ ψ' h₁ h₂ K _ y e).symm

theorem Compat.comp {t t' : TObj g k J b s} {X Y : Scheme.{0}} {c₀ : X ⟶ t.A.left} {f : X ⟶ t'.A.left}
    (h : Compat t t' c₀ f) (j : Y ⟶ X) : Compat t t' (j ≫ c₀) (j ≫ f) :=
  ⟨by rw [Category.assoc, Category.assoc, h.1], fun K _ _ su u x ψ ψ' h₁ h₂ B _ z y e => by
    rw [← Category.assoc] at e ⊢
    exact h.2 K su u x ψ ψ' h₁ h₂ B z _ e⟩

theorem Compat.fibre {t t' : TObj g k J b s} {φ : t.A.left ⟶ t'.A.left} (h : Compat t t' (𝟙 _) φ)
    {K : Type} [Field K] [IsAlgClosed K] {su : Sp K ⟶ Sp o} {u : TObj g k J b su} {x : Sp K ⟶ S}
    {ψ : u.A.left ⟶ t.A.left} {ψ' : u.A.left ⟶ t'.A.left} (h₁ : MapBy u t x ψ) (h₂ : MapBy u t' x ψ') :
    ψ ≫ φ = ψ' := by
  have := u.ab.proper
  have := u.ab.smooth
  have := GlobalTheory.isReduced_of_smooth_of_isReduced u.A.hom
  have w : (ψ ≫ φ) ≫ t'.A.hom = u.A.hom ≫ x := by rw [Category.assoc, h.1, Category.id_comp, h₁.1.1.w]
  have e : h₂.1.1.lift _ _ w = 𝟙 _ :=
    (GlobalTheory.dense_fibres_ext _ _ u.A.hom Set.univ dense_univ).2.1 _ u.A.hom _ _ (h₂.1.1.lift_snd _ _ _)
      (Category.id_comp _) fun B _ _ z _ => by
        apply h₂.1.1.hom_ext
        · rw [Category.assoc, h₂.1.1.lift_fst, Category.comp_id, ← Category.assoc]
          exact h.2 K su u x ψ ψ' h₁ h₂ B z _ (Category.comp_id _)
        · rw [Category.assoc, h₂.1.1.lift_snd, Category.comp_id]
  rw [← h₂.1.1.lift_fst _ _ w, e, Category.id_comp]

theorem exists_compat_of_local [IsReduced S] {t t' : TObj g k J b s} {Sg : Set S} (hd : Dense Sg) (hg : GeoGood t t' Sg)
    (H : ∀ p : t.A.left, ∃ (X : Scheme.{0}) (c₀ : X ⟶ t.A.left) (f : X ⟶ t'.A.left), IsOpenImmersion c₀ ∧
      p ∈ Set.range c₀ ∧ Compat t t' c₀ f) : ∃ φ, Compat t t' (𝟙 _) φ := by
  choose X c₀ f hc₀ hp hf using H
  have := t.ab.smooth
  have := GlobalTheory.isReduced_of_smooth_of_isReduced t.A.hom
  let 𝒰 : t.A.left.OpenCover := Scheme.Cover.mkOfCovers _ X c₀ (fun p => ⟨p, hp p⟩) hc₀
  have hc : ∀ p q, pullback.fst (𝒰.f p) (𝒰.f q) ≫ f p = pullback.snd _ _ ≫ f q := fun p q => by
    have := hc₀ p
    have := hc₀ q
    have : IsReduced (pullback (c₀ p) (c₀ q)) := isReduced_of_isOpenImmersion (pullback.fst (c₀ p) (c₀ q) ≫ c₀ p)
    exact ((hf p).comp (pullback.fst (c₀ p) (c₀ q))).unique hd hg
      (by rw [pullback.condition]; exact (hf q).comp (pullback.snd (c₀ p) (c₀ q)))
  have e : ∀ p, c₀ p ≫ 𝒰.glueMorphisms f hc = f p := fun p => 𝒰.ι_glueMorphisms f hc p
  refine ⟨𝒰.glueMorphisms f hc, 𝒰.hom_ext _ _ fun p => ?_, fun K _ _ su u x ψ ψ' h₁ h₂ B _ z y hy => ?_⟩
  · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (e p)).trans ((hf p).1.trans
      (congrArg _ (Category.id_comp _).symm)))
  · let p := y (default : PrimeSpectrum B)
    have := hc₀ p
    have hr : Set.range y ⊆ Set.range (c₀ p) := by
      rintro _ ⟨q, rfl⟩
      obtain rfl : q = (default : PrimeSpectrum B) := Subsingleton.elim (α := PrimeSpectrum B) _ _
      exact hp _
    have l := IsOpenImmersion.lift_fac (c₀ p) y hr
    rw [← l, Category.assoc, e]
    exact (hf p).2 K su u x ψ ψ' h₁ h₂ B z _ (l.trans ((Category.comp_id _).symm.trans hy))

end GlobalTheory.TUniq
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.UnifTransport

theorem hermForm_smul_left {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) (c : ℂ) (z w : Fin g → ℂ) :
    hermForm H (c • z) w = c * hermForm H z w := by
  simp only [hermForm, smul_dotProduct, smul_eq_mul]

theorem hermForm_add_left {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) (z z' w : Fin g → ℂ) :
    hermForm H (z + z') w = hermForm H z w + hermForm H z' w := by
  simp only [hermForm, add_dotProduct]

theorem hermForm_add_right {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) (z w w' : Fin g → ℂ) :
    hermForm H z (w + w') = hermForm H z w + hermForm H z w' := by
  simp only [hermForm, star_add, Matrix.mulVec_add, dotProduct_add]

theorem hermForm_smul_right {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) (c : ℂ) (z w : Fin g → ℂ) :
    hermForm H z (c • w) = star c * hermForm H z w := by
  simp only [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem hermForm_eq_of_im {g : ℕ} (H H' : Matrix (Fin g) (Fin g) ℂ)
    (h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (S : Set (Fin g → ℂ)) (hS : Submodule.span ℝ S = ⊤)
    (him : ∀ x ∈ S, ∀ y ∈ S, (hermForm H' (h x) (h y)).im = (hermForm H x y).im) (z w : Fin g → ℂ) :
    hermForm H' (h z) (h w) = hermForm H z w := by
  have first : ∀ y ∈ S, ∀ x, (hermForm H' (h x) (h y)).im = (hermForm H x y).im := by
    intro y hy
    let f₁ : (Fin g → ℂ) →ₗ[ℝ] ℝ :=
      { toFun := fun x => (hermForm H' (h x) (h y)).im
        map_add' := fun a c => by simp only [map_add (f := _), hermForm_add_left, Complex.add_im]
        map_smul' := fun r a => by
          simp only [RingHom.id_apply, smul_eq_mul]
          rw [← Complex.coe_smul, map_smul, hermForm_smul_left, Complex.im_ofReal_mul] }
    let f₂ : (Fin g → ℂ) →ₗ[ℝ] ℝ :=
      { toFun := fun x => (hermForm H x y).im
        map_add' := fun a c => by simp only [hermForm_add_left, Complex.add_im]
        map_smul' := fun r a => by
          simp only [RingHom.id_apply, smul_eq_mul]
          rw [← Complex.coe_smul, hermForm_smul_left, Complex.im_ofReal_mul] }
    have hf : f₁ = f₂ := LinearMap.ext_on hS (fun x hx => him x hx y hy)
    exact fun x => LinearMap.congr_fun hf x
  have both : ∀ x y, (hermForm H' (h x) (h y)).im = (hermForm H x y).im := by
    intro x
    let f₁ : (Fin g → ℂ) →ₗ[ℝ] ℝ :=
      { toFun := fun y => (hermForm H' (h x) (h y)).im
        map_add' := fun a c => by simp only [map_add (f := _), hermForm_add_right, Complex.add_im]
        map_smul' := fun r a => by
          simp only [RingHom.id_apply, smul_eq_mul]
          rw [← Complex.coe_smul, map_smul, hermForm_smul_right, Complex.star_def, Complex.conj_ofReal,
            Complex.im_ofReal_mul] }
    let f₂ : (Fin g → ℂ) →ₗ[ℝ] ℝ :=
      { toFun := fun y => (hermForm H x y).im
        map_add' := fun a c => by simp only [hermForm_add_right, Complex.add_im]
        map_smul' := fun r a => by
          simp only [RingHom.id_apply, smul_eq_mul]
          rw [← Complex.coe_smul, hermForm_smul_right, Complex.star_def, Complex.conj_ofReal,
            Complex.im_ofReal_mul] }
    have hf : f₁ = f₂ := LinearMap.ext_on hS (fun y hy => first y hy x)
    exact fun y => LinearMap.congr_fun hf y
  apply Complex.ext
  ·
    have hI := both (Complex.I • z) w
    rw [map_smul, hermForm_smul_left, hermForm_smul_left, Complex.I_mul_im, Complex.I_mul_im] at hI
    exact hI
  · exact both z w

theorem transport_uniformisation :
    ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (t : TObj g k J b (spMap em)) (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (lam : Fin (2 * g) → La) (ac : J → La → La) (Q : La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (La' : Type) [AddCommGroup La'] (EF' : LinearMap.BilinForm ℤ La') (lam' : Fin (2 * g) → La') (ac' : J → La' → La') (Q' : La' →+ (Fin g → ℂ)) (Hm' : Matrix (Fin g) (Fin g) ℂ) (e : La ≃+ La') (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = EF x y) → (Function.Injective Q' ∧ DiscreteTopology (Q').range ∧ Submodule.span ℝ (Set.range Q') = ⊤ ∧ (Hm').IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm' z z).re) ∧ ∀ x y, (hermForm Hm' (Q' x) (Q' y)).im = EF' x y) → (∀ x, Q' (e x) = h (Q x)) → (∀ x y, EF' (e x) (e y) = EF x y) → (∀ j x, e (ac j x) = ac' j (e x)) → (∀ i, ∃ y, e (lam i) = lam' i + k • y) → (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH Hm χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q x → χ' l = (-1) ^ EF x (ac w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q (lam i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q (ac j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) → (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH Hm' χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q').range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q' x → χ' l = (-1) ^ EF' x (ac' w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q' (lam' i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q' x) = Q' (ac' j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) := by
  intro o _ g k J b em w w' t La _ EF lam ac Q Hm La' _ EF' lam' ac' Q' Hm' e h hA hA' hQ hE hac hlam hU
  obtain ⟨u, χ', hAH, hΛ, hχ, hpt, hact⟩ := hU

  have hsym : ∀ x, h.symm (Q' x) = Q (e.symm x) := by
    intro x
    have hx := hQ (e.symm x)
    rw [e.apply_symm_apply] at hx
    rw [hx, LinearEquiv.symm_apply_apply]

  have him : ∀ x ∈ Set.range Q, ∀ y ∈ Set.range Q,
      (hermForm Hm' ((h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) x)
        ((h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) y)).im = (hermForm Hm x y).im := by
    rintro _ ⟨a, rfl⟩ _ ⟨c, rfl⟩
    simp only [LinearEquiv.coe_coe]
    rw [← hQ, ← hQ, hA'.2.2.2.2.2, hA.2.2.2.2.2, hE]
  have hH : ∀ a c, a ⬝ᵥ Hm'.mulVec (star c) = (h.symm a) ⬝ᵥ Hm.mulVec (star (h.symm c)) := by
    intro a c
    have hac' := hermForm_eq_of_im Hm Hm' (h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (Set.range Q) hA.2.2.1 him
      (h.symm a) (h.symm c)
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at hac'
    exact hac'

  have hper : ∀ a v, v ∈ u.Λ → u.ex (a - v) = u.ex a := by
    intro a v hv
    have hsplit := u.ex_add (a - v) v
    rw [sub_add_cancel, (u.ker v).2 hv, _root_.mul_one] at hsplit
    exact hsplit.symm
  refine ⟨holUnifReparam u h.symm (fun _ => 1) (differentiable_const 1) (fun _ => one_ne_zero),
    fun l => χ' ⟨h.symm l, l.2⟩, ?_, ?_, ?_, ?_, ?_⟩
  · unfold HolUnif.IsAH
    refine ⟨hA'.2.2.2.1, hA'.2.2.2.2.1, fun l => hAH.2.2.1 _, ?_⟩
    intro l i z hz
    simp only [holUnifReparam, div_one, map_add (f := _)]
    rw [hH z l, hH l l]
    exact hAH.2.2.2 ⟨h.symm l, l.2⟩ i (h.symm z) hz
  · intro z
    show h.symm z ∈ u.Λ ↔ z ∈ Q'.range
    rw [hΛ]
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨e a, ?_⟩
      rw [hQ, ha, LinearEquiv.apply_symm_apply]
    · rintro ⟨c, rfl⟩
      exact ⟨e.symm c, (hsym c).symm⟩
  · intro x l hl
    have hpos : h.symm (l : Fin g → ℂ) = Q (e.symm x) := by rw [hl, hsym]
    have hform := hE (e.symm x) (ac w (e.symm x))
    rw [hac, e.apply_symm_apply] at hform
    rw [hform]
    exact hχ (e.symm x) ⟨h.symm l, l.2⟩ hpos
  · intro i
    obtain ⟨y, hy⟩ := hlam i
    have hl : lam' i = e (lam i) - k • y := eq_sub_of_add_eq hy.symm
    have hmem : (((k : ℕ) : ℂ)⁻¹ * (k : ℂ)) • Q (e.symm y) ∈ u.Λ := by
      by_cases hk : ((k : ℕ) : ℂ) = 0
      · rw [hk, mul_zero, zero_smul]
        exact zero_mem _
      · rw [inv_mul_cancel₀ hk, one_smul]
        exact (hΛ _).2 ⟨e.symm y, rfl⟩
    have hpt' : h.symm (((k : ℕ) : ℂ)⁻¹ • Q' (lam' i))
        = ((k : ℕ) : ℂ)⁻¹ • Q (lam i) - (((k : ℕ) : ℂ)⁻¹ * (k : ℂ)) • Q (e.symm y) := by
      rw [hl, map_sub, map_nsmul, map_smul, map_sub, map_nsmul, hsym, hsym, e.symm_apply_apply, smul_sub,
        mul_smul, Nat.cast_smul_eq_nsmul]
    show (t.pt i).left = (u.ex (h.symm (((k : ℕ) : ℂ)⁻¹ • Q' (lam' i)))).left
    rw [hpt', hper _ _ hmem, hpt]
  · intro j
    obtain ⟨F, hF1, hF2⟩ := hact j
    refine ⟨(h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) ∘ₗ F ∘ₗ (h.symm : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), ?_, ?_⟩
    · intro x
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [hsym, hF1, ← hQ, hac, e.apply_symm_apply]
    · intro z
      show u.ex (h.symm (h (F (h.symm z)))) = u.ex (h.symm z) ≫ t.act j
      rw [LinearEquiv.symm_apply_apply, hF2]

end GlobalTheory.UnifTransport
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct Pointwise in
private lemma comap_algebraMap_fractionRing_specializes (O F : Type) [CommRing O] [IsDomain O] [Field F]
    [Algebra O F] [IsFractionRing O F] (x : PrimeSpectrum F) (y : PrimeSpectrum O) :
    PrimeSpectrum.comap (algebraMap O F) x ⤳ y := by
  rw [← PrimeSpectrum.le_iff_specializes]
  intro a ha
  have h0 : x.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
  rw [PrimeSpectrum.comap_asIdeal, h0, ← RingHom.ker_eq_comap_bot,
    (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective O F)] at ha
  rw [Ideal.mem_bot.mp ha]
  exact zero_mem _


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct Pointwise in
theorem _root_.GlobalTheory.genericPart_dense_proOpen : ∀ (O F : Type) [CommRing O] [IsDedekindDomain O] [Field F] [Algebra O F] [IsFractionRing O F] (X U : Scheme.{0}) (s : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O) (jQ : U ⟶ pullback s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F))), Flat s → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver s → IsOpenImmersion jQ → Dense (Set.range jQ) → IsLocallyNoetherian X ∧ CompactSpace X ∧ X.IsSeparated ∧ IsPreimmersion (jQ ≫ pullback.fst _ _) ∧ Flat (jQ ≫ pullback.fst _ _) ∧ IsDominant (jQ ≫ pullback.fst _ _) ∧ QuasiCompact (jQ ≫ pullback.fst _ _) := by
  intro O F _ _ _ _ _ X U s jQ hflat hproj hopen hdense
  obtain ⟨N, i, hi, hsi⟩ := hproj
  have := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str O N
  have hprop : IsProper s := by rw [← hsi]; infer_instance
  have hnO : IsLocallyNoetherian (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O) := by unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp; infer_instance
  have hnF : IsLocallyNoetherian (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp F) := by unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp; infer_instance
  have hcF : CompactSpace (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp F) := by unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp; infer_instance
  have hcO : CompactSpace (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O) := by unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp; infer_instance
  have hsepO : IsSeparated (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O).toSpecΓ := by unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp; infer_instance
  have hpre : IsPreimmersion (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F)) := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap
    exact IsPreimmersion.of_isLocalization (nonZeroDivisors O)
  have hflg : Flat (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F)) := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap
    rw [HasRingHomProperty.Spec_iff (P := @Flat), CommRingCat.hom_ofHom, RingHom.flat_algebraMap_iff]
    exact IsLocalization.flat F (nonZeroDivisors O)
  have hnP : IsLocallyNoetherian (pullback s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F))) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F)))
  have hcP : CompactSpace ↥(pullback s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F))) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F)))
  have : IsNoetherian (pullback s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F))) := ⟨⟩
  have : TopologicalSpace.NoetherianSpace U := jQ.isOpenEmbedding.isInducing.noetherianSpace
  have hdomj : IsDominant jQ := ⟨hdense⟩
  have hdomf : IsDominant (pullback.fst s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F))) := by
    constructor
    intro x
    obtain ⟨p⟩ : Nonempty (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp F) := by unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp; infer_instance
    have hp : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F) p ⤳ s x := comap_algebraMap_fractionRing_specializes O F p (s x)
    obtain ⟨x', hx', hsx'⟩ := Flat.generalizingMap s hp
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := s) (g := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F)) x' p hsx'
    exact closure_mono (show {x'} ⊆ Set.range _ from Set.singleton_subset_iff.mpr ⟨z, hz⟩)
      (specializes_iff_mem_closure.mp hx')
  refine ⟨LocallyOfFiniteType.isLocallyNoetherian s, QuasiCompact.compactSpace_of_compactSpace s,
    ?_, inferInstance, inferInstance, inferInstance, inferInstance⟩
  constructor
  rw [← terminal.comp_from s]
  infer_instance

end GlobalTheory
end

section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.TQCompare
open GlobalTheory.UU

section Clauses
variable {S S' : Scheme.{0}} {X : Type} [AddCommGroup X]

theorem isGrpPullback_id_iff {B B' : Over S} [GrpObj B] [GrpObj B'] (β : B.left ⟶ B'.left) :
    IsGrpPullback B B' (𝟙 S) β ↔ ∃ e : B ≅ B', IsMonHom e.hom ∧ e.hom.left = β := by
  constructor
  · rintro ⟨hpb, hmul⟩
    have : IsIso β := hpb.isIso_fst_of_isIso
    have hw : β ≫ B'.hom = B.hom := by simpa using hpb.w
    obtain ⟨e, he⟩ : ∃ e : B ≅ B', e.hom.left = β := ⟨Over.isoMk (asIso β) hw, rfl⟩
    have key : ∀ (T : Over S) (x y : T ⟶ B), (x * y) ≫ e.hom = (x ≫ e.hom) * (y ≫ e.hom) := by
      intro T x y
      have h1 := hmul T x y (Over.homMk (x.left ≫ β) (by simp [hw])) (Over.homMk (y.left ≫ β) (by simp [hw]))
        rfl rfl
      apply Over.OverMorphism.ext
      simp only [Hom.mul_def, Over.comp_left, Over.lift_left, Over.homMk_left, Category.assoc, he] at h1 ⊢
      exact h1.symm
    have hone : ∀ {M : Over S} [GrpObj M], (1 : 𝟙_ (Over S) ⟶ M) = η[M] := by
      intro M _
      rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    refine ⟨e, ⟨?_, ?_⟩, he⟩
    · have h2 := key (𝟙_ (Over S)) 1 1
      rw [_root_.one_mul] at h2
      have h3 : (1 : 𝟙_ (Over S) ⟶ B) ≫ e.hom = 1 := _root_.mul_left_cancel (h2.symm.trans (_root_.mul_one _).symm)
      rw [hone, hone] at h3
      exact h3
    · have h3 := key _ (fst B B) (snd B B)
      rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at h3
      rw [h3]
      congr 1
  · rintro ⟨e, he, rfl⟩
    have : IsIso e.hom.left := (Over.forget S).map_isIso e.hom
    refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, ?_⟩
    intro T x y x₀ y₀ hx hy
    have hm := (IsMonHom.monoidHom e.hom T).map_mul x y
    simp only [IsMonHom.monoidHom_apply] at hm
    have h4 := congrArg Over.Hom.left hm
    simp only [Hom.mul_def, Over.comp_left, Over.lift_left, Category.assoc] at h4 ⊢
    simp only [hx, hy]
    exact h4.symm

end Clauses

section At
variable (X : Type) [AddCommGroup X]

end At

end GlobalTheory.TQCompare
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem levelMaps_of_parts : (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo : Moduli D l) (Xo₂ : Moduli D l₂), 1 ≤ D.p + D.q → l.Dvd l₂ → ∃ (r : Xo₂.X ⟶ Xo.X) (jK : KA l →+* KA l₂) (m : SABMap Xo₂.univ.t Xo.univ.t r), (∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ)) ∧ r ≫ Xo.s = Xo₂.s ≫ spMap jK ∧ (∀ a, (Xo₂.univ.eta a ^ (l₂.M / l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left) ∧ (∀ a, (Xo₂.univ.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA a).left)) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo : Moduli D l) (Xo₂ : Moduli D l₂), 1 ≤ D.p + D.q → l.Dvd l₂ → ∀ (r : Xo₂.X ⟶ Xo.X) (jK : KA l →+* KA l₂) (m : SABMap Xo₂.univ.t Xo.univ.t r), (∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ)) ∧ r ≫ Xo.s = Xo₂.s ≫ spMap jK ∧ (∀ a, (Xo₂.univ.eta a ^ (l₂.M / l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left) ∧ (∀ a, (Xo₂.univ.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA a).left) → ∀ g : Sim D, g.InGam l l₂ → ∃ ρ : Xo₂.X ≅ Xo₂.X, Xo₂.LevAut g ρ ∧ ρ.hom ≫ r = r) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo : Moduli D l) (Xo₂ : Moduli D l₂), 1 ≤ D.p + D.q → l.Dvd l₂ → ∀ (r : Xo₂.X ⟶ Xo.X) (jK : KA l →+* KA l₂) (m : SABMap Xo₂.univ.t Xo.univ.t r), (∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ)) ∧ r ≫ Xo.s = Xo₂.s ≫ spMap jK ∧ (∀ a, (Xo₂.univ.eta a ^ (l₂.M / l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left) ∧ (∀ a, (Xo₂.univ.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA a).left) → ∀ (c : Coeff l) (c₂ : Coeff l₂) (hc : c.F = c₂.F) (rF : Xo₂.XF c₂ ⟶ Xo.XF c), rF ≫ pullback.fst _ _ = pullback.fst _ _ ≫ r → rF ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hc.le).toRingHom → IsFinite rF ∧ Etale rF ∧ Surjective rF) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo : Moduli D l) (Xo₂ : Moduli D l₂), 1 ≤ D.p + D.q → l.Dvd l₂ → ∀ (r : Xo₂.X ⟶ Xo.X) (jK : KA l →+* KA l₂) (m : SABMap Xo₂.univ.t Xo.univ.t r), (∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ)) ∧ r ≫ Xo.s = Xo₂.s ≫ spMap jK ∧ (∀ a, (Xo₂.univ.eta a ^ (l₂.M / l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left) ∧ (∀ a, (Xo₂.univ.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA a).left) → ∀ (c : Coeff l) (c₂ : Coeff l₂) (hc : c.F = c₂.F) (rF : Xo₂.XF c₂ ⟶ Xo.XF c), rF ≫ pullback.fst _ _ = pullback.fst _ _ ≫ r → rF ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hc.le).toRingHom → ∀ (k : Type) [Field k] [IsAlgClosed k] (y y' : Sp k ⟶ Xo₂.XF c₂), y ≫ rF = y' ≫ rF → (∃ (g : Sim D) (ρ : Xo₂.X ≅ Xo₂.X), g.InGam l l₂ ∧ Xo₂.LevAut g ρ ∧ ρ.hom ≫ r = r ∧ y' ≫ pullback.fst _ _ = y ≫ pullback.fst _ _ ≫ ρ.hom) ∧ ∀ (g : Sim D) (ρ : Xo₂.X ≅ Xo₂.X), g.InGam l l₂ → Xo₂.LevAut g ρ → y ≫ pullback.fst _ _ ≫ ρ.hom = y ≫ pullback.fst _ _ → g.TrivAt l₂) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), 1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) := by
  intro h₁ h₂ h₃ h₄ E _ _ _ H D hpq l l₂ Xo Xo₂ hd
  obtain ⟨r, jK, m, hh⟩ := h₁ E H D l l₂ Xo Xo₂ hpq hd
  refine ⟨r, jK, m, hh.1, hh.2.1, hh.2.2.1, hh.2.2.2, h₂ E H D l l₂ Xo Xo₂ hpq hd r jK m hh, ?_⟩
  intro c c₂ hc
  have hring : (IntermediateField.inclusion c₂.le).toRingHom.comp jK =
      (IntermediateField.inclusion hc.le).toRingHom.comp (IntermediateField.inclusion c.le).toRingHom := by
    ext x
    exact hh.1 x
  have w : (pullback.fst Xo₂.s (spMap (IntermediateField.inclusion c₂.le).toRingHom) ≫ r) ≫ Xo.s =
      (pullback.snd Xo₂.s (spMap (IntermediateField.inclusion c₂.le).toRingHom) ≫
        spMap (IntermediateField.inclusion hc.le).toRingHom) ≫
        spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [Category.assoc, hh.2.1, pullback.condition_assoc, Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hring]
  have e₁ := pullback.lift_fst _ _ w
  have e₂ := pullback.lift_snd _ _ w
  have k₃ := h₃ E H D l l₂ Xo Xo₂ hpq hd r jK m hh c c₂ hc _ e₁ e₂
  exact ⟨pullback.lift _ _ w, e₁, e₂, k₃.1, k₃.2.1, k₃.2.2,
    h₄ E H D l l₂ Xo Xo₂ hpq hd r jK m hh c c₂ hc _ e₁ e₂⟩

end GlobalTheory
end
