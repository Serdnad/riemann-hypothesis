module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsNeZeroIsStandardSmoothOfRelativeDimension
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle013
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem injective_of_quasiFinite_of_isStandardSmoothOfRelativeDimension {R B : Type} [CommRing R]
    [IsDomain R] [CommRing B] [IsDomain B] [Algebra R B] {g : ℕ}
    [Algebra.IsStandardSmoothOfRelativeDimension g R B] (ψ : MvPolynomial (Fin g) R →ₐ[R] B)
    (hψ : ψ.toRingHom.QuasiFinite) : Function.Injective ψ := by
  have key : FaithfulSMul R B ∧ Algebra.trdeg R B = g := by
    obtain ⟨e, he⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial g R B
    letI : Algebra (MvPolynomial (Fin g) R) B := e.toRingHom.toAlgebra
    haveI : Algebra.Etale (MvPolynomial (Fin g) R) B := he
    haveI : IsScalarTower R (MvPolynomial (Fin g) R) B :=
      IsScalarTower.of_algebraMap_eq fun x => (e.commutes x).symm
    obtain ⟨_, _⟩ :=
      AffinePoints.faithfulSMul_and_isAlgebraic_of_etale (MvPolynomial (Fin g) R) B
    refine ⟨FaithfulSMul.trans R (MvPolynomial (Fin g) R) B, ?_⟩
    rw [trdeg_eq_of_isAlgebraic_top R (MvPolynomial (Fin g) R) B, MvPolynomial.trdeg_of_isDomain]
    simp
  obtain ⟨_, htr⟩ := key
  let x : Fin g → B := fun i => ψ (MvPolynomial.X i)
  have hx : ψ = MvPolynomial.aeval x := MvPolynomial.aeval_unique ψ
  have hr : ψ.range = Algebra.adjoin R (Set.range x) := by
    rw [Algebra.adjoin_range_eq_range_aeval, ← hx]
  have h1 : (algebraMap ψ.range B).QuasiFinite :=
    RingHom.QuasiFinite.of_comp (f := algebraMap ψ.range B) (g := ψ.rangeRestrict.toRingHom) hψ
  rw [RingHom.quasiFinite_algebraMap] at h1
  have h2 : Algebra.IsAlgebraic ψ.range B := isAlgebraic_of_quasiFiniteAt ψ.range B ⊥
  rw [hr] at h2
  have h3 := Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite R x (by simp [htr])
  rw [hx]
  exact h3.1

theorem isDominant_of_locallyQuasiFinite_affineSpace {Z : Scheme.{0}} [IsIntegral Z]
    {R B : CommRingCat.{0}} [IsDomain R] [IsDomain B] {g : ℕ} (φ : R ⟶ B)
    (hφ : φ.hom.IsStandardSmoothOfRelativeDimension g) (i : Spec R ⟶ Z) [IsOpenImmersion i]
    (f : Spec B ⟶ 𝔸(Fin g; Z)) [LocallyQuasiFinite f]
    (hf : f ≫ 𝔸(Fin g; Z) ↘ Z = Spec.map φ ≫ i) : IsDominant f := by
  have hp := AffineSpace.isPullback_map (n := Fin g) i
  have : IsOpenImmersion (AffineSpace.map (Fin g) i) :=
    MorphismProperty.of_isPullback hp.flip ‹_›
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective
    (hp.lift f (Spec.map φ) hf ≫ (AffineSpace.SpecIso (Fin g) R).hom)
  have e : f = Spec.map ψ ≫ (AffineSpace.SpecIso (Fin g) R).inv ≫ AffineSpace.map (Fin g) i := by
    rw [hψ]; simp
  have e2 : CommRingCat.ofHom MvPolynomial.C ≫ ψ = φ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ, ← AffineSpace.SpecIso_inv_over, Category.assoc, Iso.hom_inv_id_assoc,
      IsPullback.lift_snd]
  have hq : LocallyQuasiFinite (Spec.map ψ) := by
    rw [e] at ‹LocallyQuasiFinite f›
    exact .of_comp _ ((AffineSpace.SpecIso (Fin g) R).inv ≫ AffineSpace.map (Fin g) i)
  rw [HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite)] at hq
  letI : Algebra R B := φ.hom.toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension g R B := hφ
  have hinj := injective_of_quasiFinite_of_isStandardSmoothOfRelativeDimension
    (R := R) (B := B) (g := g) { ψ.hom with commutes' := fun r => congr($e2 r) } hq
  have : IsDominant (Spec.map ψ) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
      (by rw [(RingHom.injective_iff_ker_eq_bot ψ.hom).1 hinj]; exact bot_le)⟩
  have : IsDominant (AffineSpace.map (Fin g) i) :=
    ⟨(AffineSpace.map (Fin g) i).isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩
  rw [e]
  infer_instance

theorem isDominant_homOfVector_of_quasiFiniteAt :
    ∀ (X Z : Scheme.{0}) [IsIntegral X] [IsIntegral Z] (t : X ⟶ Z) [LocallyOfFiniteType t] (g : ℕ) (U : X.Opens), (U : Set X).Nonempty → SmoothOfRelativeDimension g (U.ι ≫ t) → ∀ (u : Fin g → Γ(X, ⊤)) (w : X), (AffineSpace.homOfVector t u).QuasiFiniteAt w → IsDominant (AffineSpace.homOfVector t u) := by
  intro X Z _ _ t _ g U hU hs u w hw
  have hf := AffineSpace.homOfVector_over t u
  generalize AffineSpace.homOfVector t u = f at hf hw
  have : LocallyOfFiniteType f := by
    have : LocallyOfFiniteType (f ≫ 𝔸(Fin g; Z) ↘ Z) := by rw [hf]; infer_instance
    exact locallyOfFiniteType_of_comp f (𝔸(Fin g; Z) ↘ Z)
  obtain ⟨x, hxU, hxV⟩ := nonempty_preirreducible_inter U.isOpen f.quasiFiniteLocus.isOpen hU
    ⟨w, hw⟩
  let W : X.Opens := U ⊓ f.quasiFiniteLocus
  have h1 : SmoothOfRelativeDimension (0 + g) (X.homOfLE (inf_le_left : W ≤ U) ≫ U.ι ≫ t) :=
    inferInstance
  have h2 : LocallyQuasiFinite (X.homOfLE (inf_le_right : W ≤ f.quasiFiniteLocus) ≫
    f.quasiFiniteLocus.ι ≫ f) := inferInstance
  rw [Scheme.homOfLE_ι_assoc] at h1 h2
  rw [zero_add] at h1
  obtain ⟨Z', hZ', V, hV, hx, e, hsm⟩ := h1.exists_isStandardSmoothOfRelativeDimension ⟨x, hxU, hxV⟩
  have : Nonempty W := ⟨⟨x, hxU, hxV⟩⟩
  have : Nonempty V := ⟨⟨_, hx⟩⟩
  have : Nonempty Z' := ⟨⟨_, e hx⟩⟩
  have : IsDominant (hV.fromSpec ≫ W.ι ≫ f) :=
    isDominant_of_locallyQuasiFinite_affineSpace _ hsm hZ'.fromSpec _ (by
      rw [IsAffineOpen.SpecMap_appLE_fromSpec _ hZ' hV e]; simp [hf, W])
  have : IsDominant (W.ι ≫ f) := .of_comp hV.fromSpec _
  exact .of_comp W.ι _

end GlobalTheory
end

section

open scoped BigOperators TensorProduct

theorem _root_.GlobalTheory.T.exists_complete_discreteValuationRing_of_mem_closure_cones_alt : ∀ (F K J ι : Type) [Field F] [Field K] [Algebra F K] [Fintype J] [Finite ι] (A : ι → Type) [∀ i, CommRing (A i)] [∀ i, Algebra F (A i)], (∀ i, Algebra.FiniteType F (A i)) → ∀ (w : ∀ i, J → A i) (v : J → K), v ≠ 0 → (∀ (G : MvPolynomial J F) (d : ℕ), G.IsHomogeneous d → (∀ i, MvPolynomial.aeval (w i) G = 0) → MvPolynomial.aeval v G = 0) → ∃ (i : ι) (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : Algebra K W) (f : A i →+* FractionRing W) (s : FractionRing W) (w' : J → W), IsAdicComplete (IsLocalRing.maximalIdeal W) W ∧ s ≠ 0 ∧ (∀ x : F, f (algebraMap F (A i) x) = algebraMap W (FractionRing W) (algebraMap K W (algebraMap F K x))) ∧ ∀ j, algebraMap W (FractionRing W) (w' j) = s * f (w i j) ∧ w' j - algebraMap K W (v j) ∈ IsLocalRing.maximalIdeal W := by
  first | exact @GlobalTheory.exists_complete_discreteValuationRing_of_mem_closure_cones | exact GlobalTheory.exists_complete_discreteValuationRing_of_mem_closure_cones | (intros; apply GlobalTheory.exists_complete_discreteValuationRing_of_mem_closure_cones <;> assumption)
end

section

namespace GlobalTheory

namespace IntegralOverComplete

open IsLocalRing Polynomial

theorem isLocalHom_val {W R : Type} [CommRing W] [CommRing R] [Algebra W R]
    [Algebra.IsIntegral W R] (W' : Subalgebra W R) : IsLocalHom W'.val.toRingHom := by
  have : Algebra.IsIntegral W' R := Algebra.IsIntegral.tower_top W
  have : FaithfulSMul W' R := (faithfulSMul_iff_algebraMap_injective _ _).2 Subtype.val_injective
  exact inferInstanceAs (IsLocalHom (algebraMap W' R))

theorem exists_subalgebra (W R : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (maximalIdeal W) W] [CharZero W] [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Algebra W R] [FaithfulSMul W R] [Algebra.IsIntegral W R]
    (s : Finset R) :
    ∃ (W' : Subalgebra W R) (_ : IsDiscreteValuationRing W'), (↑s : Set R) ⊆ W' ∧
      IsAdicComplete (maximalIdeal W') W' ∧ Module.Finite W W' ∧
      IsLocalHom W'.val.toRingHom := by
  classical
  let F := FractionRing R
  let j : R →ₐ[W] F := IsScalarTower.toAlgHom W R F
  have hj : Function.Injective j := IsFractionRing.injective R F
  have : FaithfulSMul W F := (faithfulSMul_iff_algebraMap_injective _ _).2 (by
    rw [IsScalarTower.algebraMap_eq W R F]
    exact hj.comp (FaithfulSMul.algebraMap_injective W R))
  have : Algebra.IsAlgebraic R F := IsLocalization.isAlgebraic F (nonZeroDivisors R)
  have : Algebra.IsAlgebraic W F := Algebra.IsAlgebraic.trans W R F
  obtain ⟨V, hV, -, -, hfin, -, -, -, hs⟩ :=
    exists_complete_dvr_finite_subalgebra W F (s.image j)
  have hle : V ≤ j.range := fun x hx => by
    have h1 : IsIntegral W x :=
      (Algebra.IsIntegral.isIntegral (R := W) (⟨x, hx⟩ : V)).map V.val
    exact IsIntegrallyClosed.isIntegral_iff.1 (h1.tower_top (A := R))
  let W' : Subalgebra W R := V.comap j
  have hmap : W'.map j = V := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hx
    · intro x hx
      obtain ⟨y, rfl⟩ := hle hx
      exact ⟨y, hx, rfl⟩
  let e : V ≃ₐ[W] W' :=
    ((Subalgebra.equivMapOfInjective W' j hj).trans (Subalgebra.equivOfEq _ _ hmap)).symm
  have hd : IsDiscreteValuationRing W' :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e
  have hf : Module.Finite W W' := Module.Finite.equiv e.toLinearEquiv
  refine ⟨W', hd, fun x hx => ?_,
    CompleteFiniteExtension.isAdicComplete_of_finite_local W W', hf, isLocalHom_val W'⟩
  exact hs _ (Finset.mem_image_of_mem j hx) ((Algebra.IsIntegral.isIntegral x).map j)

theorem henselian_of_union (W R : Type) [CommRing W] [CommRing R] [IsLocalRing R] [Algebra W R]
    (h : ∀ s : Finset R, ∃ (W' : Subalgebra W R) (_ : IsLocalRing W'), (↑s : Set R) ⊆ W' ∧
      IsAdicComplete (maximalIdeal W') W' ∧ IsLocalHom W'.val.toRingHom) :
    HenselianLocalRing R := by
  classical
  refine ⟨fun f hf a₀ h0 hu => ?_⟩
  obtain ⟨V, _, hs, hc, hl⟩ := h (insert a₀ f.coeffs ∪ {0})
  let i : V →+* R := V.val.toRingHom
  have hlift : f ∈ lifts i := by
    rw [lifts_iff_coeff_lifts]
    intro n
    by_cases hn : f.coeff n = 0
    · exact ⟨0, by simp [hn]⟩
    · exact ⟨⟨f.coeff n, hs (by simp [coeff_mem_coeffs hn])⟩, rfl⟩
  obtain ⟨g, hg, -, hgm⟩ := lifts_and_natDegree_eq_and_monic hlift hf
  obtain ⟨b, rfl⟩ : ∃ b : V, i b = a₀ := ⟨⟨a₀, hs (by simp)⟩, rfl⟩
  subst hg
  rw [eval_map, eval₂_at_apply] at h0
  rw [derivative_map, eval_map, eval₂_at_apply] at hu
  have h0' : g.eval b ∈ maximalIdeal V := fun hu' => h0 (hu'.map i)
  have hu' : IsUnit (g.derivative.eval b) := IsLocalHom.map_nonunit _ hu
  obtain ⟨a, ha, hab⟩ := HenselianRing.is_henselian (I := maximalIdeal V) g hgm b h0' (hu'.map _)
  refine ⟨i a, ?_, ?_⟩
  · rw [IsRoot, eval_map, eval₂_at_apply, ha.eq_zero, map_zero]
  · rw [← map_sub]
    exact fun hh => hab (IsLocalHom.map_nonunit _ hh)

end IntegralOverComplete

theorem henselian_and_union_of_isIntegral_complete :
    ∀ (W R : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
      [IsAdicComplete (IsLocalRing.maximalIdeal W) W] [CharZero W] [CommRing R] [IsDomain R]
      [IsDiscreteValuationRing R] [Algebra W R], Function.Injective (algebraMap W R) →
      Algebra.IsIntegral W R → IsLocalHom (algebraMap W R) ∧ HenselianLocalRing R ∧
      ∀ s : Finset R, ∃ (W' : Subalgebra W R) (_ : IsDiscreteValuationRing W'),
        (↑s : Set R) ⊆ W' ∧ IsAdicComplete (IsLocalRing.maximalIdeal W') W' ∧
        Module.Finite W W' ∧ IsLocalHom W'.val.toRingHom := by
  intro W R _ _ _ _ _ _ _ _ _ hinj hint
  have : FaithfulSMul W R := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  refine ⟨inferInstance, IntegralOverComplete.henselian_of_union W R fun s => ?_,
    IntegralOverComplete.exists_subalgebra W R⟩
  obtain ⟨V, hV, h1, h2, -, h3⟩ := IntegralOverComplete.exists_subalgebra W R s
  exact ⟨V, inferInstance, h1, h2, h3⟩

end GlobalTheory
end
