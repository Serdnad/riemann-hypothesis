module

public import Mathlib.FieldTheory.IntermediateField.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle025
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle009
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.exists_field_of_definition_of_point : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (x : Sp Ω ⟶ X), ∃ E : Subfield Ω, (∀ τ τ' : Ω →+* Ω, spMap τ ≫ x = spMap τ' ≫ x ↔ ∀ c ∈ E, τ c = τ' c) ∧ (∀ (K' : Type) [Field K'] (j : K' →+* Ω), E ≤ j.fieldRange ↔ ∃ y : Sp K' ⟶ X, spMap j ≫ y = x) ∧ ∀ (K : Type) [Field K] [Algebra K Ω] (s : X ⟶ Sp K), LocallyOfFiniteType s → x ≫ s = spMap (algebraMap K Ω) → Algebra.IsAlgebraic K Ω → ∃ L : IntermediateField K Ω, FiniteDimensional K L ∧ L.toSubfield = E := by
  first | exact @GlobalTheory.SS.exists_fieldOfValues | exact GlobalTheory.SS.exists_fieldOfValues | (intros; apply GlobalTheory.SS.exists_fieldOfValues <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf
namespace GlobalTheory.SS.ArcInf

theorem exists_factor_of_range_subset {k : Type} [CommRing k] {G : Over (Sp k)} {A B : Type} [CommRing A]
    [Algebra k A] [CommRing B] [Algebra k B] (j : algOver k A ⟶ G) (hj : IsOpenImmersion j.left)
    (a : algOver k B ⟶ G) (hr : Set.range a.left ⊆ Set.range j.left) :
    ∃ χ : A →ₐ[k] B, algOverHom χ ≫ j = a := by
  have hf := IsOpenImmersion.lift_fac j.left a.left hr
  let l : algOver k B ⟶ algOver k A := Over.homMk (IsOpenImmersion.lift j.left a.left hr) (by
    rw [← Over.w j, ← Category.assoc, hf, Over.w a])
  obtain ⟨χ, hχ⟩ := algOverHom_surjective l
  refine ⟨χ, ?_⟩
  rw [hχ]
  ext1
  exact hf

theorem exists_extend_of_localSubring : ∀ (k : Type) [CommRing k] (G : Over (Sp k)) (O K F : Type) [CommRing O] [Algebra k O] [Field K] [Algebra k K] [Field F] [Algebra k F] (em : O →ₐ[k] K) (σ : K →ₐ[k] F) (L : Subalgebra k F), IsLocalRing L → Function.Injective em → (∀ x, σ x ∈ L → x ∈ Set.range em) → ∀ (a : algOver k K ⟶ G) (b' : algOver k L ⟶ G), algOverHom σ ≫ a = algOverHom L.val ≫ b' → ∃ b : algOver k O ⟶ G, algOverHom em ≫ b = a := by
  intro k _ G O K F _ _ _ _ _ _ em σ L hL hem hsub a b' hab
  let x0 : (Sp L) := IsLocalRing.closedPoint L
  obtain ⟨R, i, hi, hx, -⟩ := Scheme.exists_affine_mem_range_and_range_subset (X := G.left)
    (x := b'.left x0) (U := ⊤) trivial
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (i ≫ G.hom : Spec R ⟶ Spec (CommRingCat.of k))
  letI : Algebra k R := φ.hom.toAlgebra
  let j : algOver k R ⟶ G := Over.homMk i hφ.symm
  have hj : IsOpenImmersion j.left := hi
  have hrb : Set.range b'.left ⊆ Set.range j.left := by
    rintro _ ⟨y, rfl⟩
    have hs : y ⤳ x0 := IsLocalRing.specializes_closedPoint (R := L) y
    have hs' := hs.map b'.left.continuous
    exact hs'.mem_open j.left.isOpenEmbedding.isOpen_range hx
  have hra : Set.range a.left ⊆ Set.range j.left := by
    rintro _ ⟨y, rfl⟩
    let p : (Sp F) := IsLocalRing.closedPoint F
    have hy : y = (algOverHom σ).left p := Subsingleton.elim (α := PrimeSpectrum K) _ _
    have hl : (algOverHom σ).left ≫ a.left = (algOverHom L.val).left ≫ b'.left := by
      rw [← Over.comp_left, ← Over.comp_left, hab]
    apply hrb
    refine ⟨(algOverHom L.val).left p, ?_⟩
    rw [hy, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hl]
  obtain ⟨χL, hχL⟩ := exists_factor_of_range_subset j hj b' hrb
  obtain ⟨χK, hχK⟩ := exists_factor_of_range_subset j hj a hra
  have hc : σ.comp χK = L.val.comp χL := by
    apply eq_of_comp_eq hj
    rw [algOverHom_comp, algOverHom_comp, Category.assoc, Category.assoc, hχK, hχL, hab]
  have hmem : ∀ x, χK x ∈ em.range := fun x => by
    apply hsub
    have : σ (χK x) = (χL x : F) := DFunLike.congr_fun hc x
    rw [this]
    exact (χL x).2
  let χO : R →ₐ[k] O :=
    ((AlgEquiv.ofInjective em hem).symm : em.range →ₐ[k] O).comp (χK.codRestrict em.range hmem)
  have hO : em.comp χO = χK := by
    ext x
    have := AlgEquiv.ofInjective_apply em hem ((AlgEquiv.ofInjective em hem).symm ⟨χK x, hmem x⟩)
    rw [AlgEquiv.apply_symm_apply] at this
    exact this.symm
  refine ⟨algOverHom χO ≫ j, ?_⟩
  rw [← Category.assoc, ← algOverHom_comp, hO, hχK]

end GlobalTheory.SS.ArcInf
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf
noncomputable section
namespace GlobalTheory.SS.ArcInf

theorem exists_basicOpen_factor : ∀ (k : Type) [CommRing k] (G : Over (Sp k)) (A B F : Type) [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] [Field F] [Algebra k F] (j : algOver k A ⟶ G) (φ : algOver k B ⟶ G) (δ : B →ₐ[k] F) (χ₀ : A →ₐ[k] F), IsOpenImmersion j.left → algOverHom δ ≫ φ = algOverHom χ₀ ≫ j → ∃ e : B, δ e ≠ 0 ∧ ∀ (B' : Type) [CommRing B'] [Algebra k B'] (ρ : B →ₐ[k] B'), IsUnit (ρ e) → ∃ χ : A →ₐ[k] B', algOverHom χ ≫ j = algOverHom ρ ≫ φ := by
  intro k _ G A B F _ _ _ _ _ _ j φ δ χ₀ hj h
  let U : (Spec (CommRingCat.of B)).Opens := φ.left ⁻¹ᵁ j.left.opensRange
  let p₀ : PrimeSpectrum F := ⟨⊥, Ideal.isPrime_bot⟩
  let p : PrimeSpectrum B := PrimeSpectrum.comap (δ : B →+* F) p₀
  have hl : (algOverHom δ).left ≫ φ.left = (algOverHom χ₀).left ≫ j.left := by
    have := congrArg (fun x => x.left) h
    simpa only [Over.comp_left] using this
  have hp : p ∈ (U : Set (Spec (CommRingCat.of B))) := by
    refine ⟨(algOverHom χ₀).left p₀, ?_⟩
    have := congrArg (fun x => x p₀) hl
    simp only [Scheme.Hom.comp_apply] at this
    exact this.symm
  obtain ⟨_, ⟨e, rfl⟩, he, heU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hp U.isOpen
  refine ⟨e, fun h0 => he (show δ e ∈ (⊥ : Ideal F) from h0), ?_⟩
  intro B' _ _ ρ hρ
  have hr : Set.range ((algOverHom ρ).left ≫ φ.left) ⊆ Set.range j.left := by
    rintro _ ⟨q, rfl⟩
    have hq : PrimeSpectrum.comap (ρ : B →+* B') q ∈ PrimeSpectrum.basicOpen e := by
      intro hm
      exact q.2.ne_top (Ideal.eq_top_of_isUnit_mem _ (show ρ e ∈ q.asIdeal from hm) hρ)
    rw [Scheme.Hom.comp_apply]
    exact heU hq
  have hf := IsOpenImmersion.lift_fac j.left ((algOverHom ρ).left ≫ φ.left) hr
  let ψ : algOver k B' ⟶ algOver k A :=
    Over.homMk (IsOpenImmersion.lift j.left ((algOverHom ρ).left ≫ φ.left) hr) (by
      rw [← Over.w j, ← Category.assoc, hf, Category.assoc, Over.w φ, Over.w (algOverHom ρ)])
  obtain ⟨χ, hχ⟩ := algOverHom_surjective ψ
  refine ⟨χ, ?_⟩
  rw [hχ]
  ext1
  exact hf

end GlobalTheory.SS.ArcInf
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.TorsionDivisible

theorem hom_ext_of_rationalPoints {K : Type} [Field K] [IsAlgClosed K] {X Y : Over (Sp K)}
    [IsReduced X.left] [LocallyOfFiniteType X.hom] [IsProper Y.hom] (f g : X ⟶ Y)
    (h : ∀ x : 𝟙_ (Over (Sp K)) ⟶ X, x ≫ f = x ≫ g) : f = g := by
  have : LocallyOfFiniteType (f.left ≫ Y.hom) := by rw [Over.w]; infer_instance
  refine Over.OverMorphism.ext (ext_of_apply_eq (K := K) Y.hom Set.univ
    isOpen_univ.isLocallyClosed dense_univ (fun x _ hx => ?_) (by rw [Over.w, Over.w]))
  let p : 𝟙_ (Over (Sp K)) ⟶ X :=
    Over.homMk (pointOfClosedPoint (K := K) X.hom x hx) (pointOfClosedPoint_comp (K := K) X.hom x hx)
  have h1 : pointOfClosedPoint (K := K) X.hom x hx ≫ f.left =
      pointOfClosedPoint (K := K) X.hom x hx ≫ g.left := congrArg CommaMorphism.left (h p)
  have h2 : f.left (pointOfClosedPoint (K := K) X.hom x hx (IsLocalRing.closedPoint K)) =
      g.left (pointOfClosedPoint (K := K) X.hom x hx (IsLocalRing.closedPoint K)) :=
    congrArg (fun φ => φ (IsLocalRing.closedPoint K)) h1
  have h3 := pointOfClosedPoint_apply (K := K) X.hom x hx (IsLocalRing.closedPoint K)
  exact (congrArg f.left h3).symm.trans (h2.trans (congrArg g.left h3))

theorem finite_fibre_points {K : Type} [Field K] [IsAlgClosed K]
    {X Y : Over (Sp K)} [LocallyOfFiniteType X.hom] (f : X ⟶ Y)
    [IsFinite f.left] (y : 𝟙_ (Over (Sp K)) ⟶ Y) :
    Finite {x : 𝟙_ (Over (Sp K)) ⟶ X // x ≫ f = y} := by
  have hfin : (f.left ⁻¹' {y.left (IsLocalRing.closedPoint K)}).Finite :=
    f.left.finite_preimage_singleton _
  have := hfin.to_subtype
  refine Finite.of_injective
    (fun x => (⟨x.1.left (IsLocalRing.closedPoint K), by
      have h := congrArg (fun u => u.left (IsLocalRing.closedPoint K)) x.2
      exact h⟩ : (f.left ⁻¹' {y.left (IsLocalRing.closedPoint K)}))) ?_
  intro a b hab
  refine Subtype.ext (Over.OverMorphism.ext ?_)
  exact ext_of_apply_closedPoint_eq (K := K) X.hom (Over.w a.1) (Over.w b.1)
    (congrArg Subtype.val hab)

theorem finite_torsion_and_divisible :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B], IsAbelianScheme B → ∀ n : ℕ, (n : k) ≠ 0 → Finite {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} ∧ ∀ f : B ⟶ B, IsMonHom f → (∀ x : (𝟙_ (Over (Sp k)) ⟶ B), x ^ n = 1 → x ≫ f = 1) → ∃ g : B ⟶ B, IsMonHom g ∧ f = g ^ n := by
  intro k _ _ B _ hB n hn
  have := hB.comm
  have := hB.smooth
  have := hB.proper
  have := hB.geomConnected
  have hu : IsUnit (n : Γ(Sp k, ⊤)) := by
    simpa using (isUnit_iff_ne_zero.2 hn).map (Scheme.ΓSpecIso (.of k)).inv.hom
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := GrpTangent.finiteEtale_mulN_torsion B hu
  refine ⟨?_, fun f hf hker => ?_⟩
  · have := finite_fibre_points (mulN B n) 1
    exact Finite.of_equiv _ (Equiv.subtypeEquivRight (p := fun x => x ≫ mulN B n = 1) fun x => by
      rw [GrpTangent.comp_mulN])
  · have : ConnectedSpace B.left := GeometricallyConnected.connectedSpace_of_subsingleton B.hom
    have hc : IsClopen (Set.range (mulN B n).left) :=
      ⟨(mulN B n).left.isClosedMap.isClosed_range, (mulN B n).left.isOpenMap.isOpen_range⟩
    have h5 : Surjective (mulN B n).left :=
      ⟨Set.range_eq_univ.mp (hc.eq_univ (Set.range_nonempty _))⟩
    have : IsReduced (torsion B n).left := isReduced_of_smooth_of_isReduced (torsion B n).hom
    have hι : torsion.ι B n ≫ mulN B n = 1 := by
      rw [Hom.one_def]
      exact pullback.condition.trans (congrArg (· ≫ η[B]) (toUnit_unique _ _))
    have h6 : torsion.ι B n ≫ f = 1 := hom_ext_of_rationalPoints _ _ fun x => by
      rw [← Category.assoc, MonObj.comp_one]
      refine hker _ ?_
      rw [← GrpTangent.comp_mulN, Category.assoc, hι, MonObj.comp_one]
    have h7 : ∀ (T : Over (Sp k)) (x : T ⟶ B), x ^ n = 1 → x ≫ f = 1 := fun T x hx => by
      have e : x ≫ mulN B n = toUnit T ≫ η[B] := by rw [GrpTangent.comp_mulN, hx, Hom.one_def]
      obtain ⟨y, e'⟩ : ∃ y : T ⟶ torsion B n, y ≫ torsion.ι B n = x :=
        ⟨pullback.lift x (toUnit T) e, pullback.lift_fst _ _ _⟩
      rw [← e', Category.assoc, h6, MonObj.comp_one]
    have hm : Out.mulA B n = mulN B n := (GrpTangent.mulN_eq_pow B n).symm
    have : Etale (Out.mulA B n).left := hm ▸ h2
    have : IsFinite (Out.mulA B n).left := hm ▸ h1
    have : Surjective (Out.mulA B n).left := hm ▸ h5
    obtain ⟨φ, hφ⟩ := DivisibleHom.exists_factor n f h7
    have : IsMonHom (Out.mulA B n ≫ φ) := hφ ▸ hf
    have : IsMonHom φ := DivisibleHom.isMonHom_of_factor n φ
    exact ⟨φ, this, by rw [← hφ, DivisibleHom.mulA_comp]⟩

end GlobalTheory.TorsionDivisible
end
