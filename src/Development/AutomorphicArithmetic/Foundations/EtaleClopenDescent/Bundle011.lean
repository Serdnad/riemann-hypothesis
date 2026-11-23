module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OmegaPullOmegaTraceOfSecTraceOne
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Module.StablyFree.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Proper
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001

@[expose] public section

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR KaehlerDifferential GlobalTheory.W1

theorem UpperTheory.Cb.existsUnique_complexPoint_lift_clopen_cover :
    ∀ (Y : Scheme.{0}) (s' : Y ⟶ Sp ℂ) (M : Type) [Fintype M] (W : M → Y.Opens), (∀ i j, i ≠ j → W i ⊓ W j = ⊥) → iSup W = ⊤ → ∀ y : CxPts s' (RingHom.id ℂ), ∃! m : M, ∃! y' : CxPts ((W m).ι ≫ s') (RingHom.id ℂ), y'.1 ≫ (W m).ι = y.1 := by
  intro Y s' M _ W hd hc y
  let x0 : (Sp ℂ : Scheme.{0}) := IsLocalRing.closedPoint ℂ
  have hone : ∀ a : (Sp ℂ : Scheme.{0}), a = x0 := fun a => Subsingleton.elim a x0
  obtain ⟨m, hm⟩ : ∃ m, y.1 x0 ∈ W m := by
    have h : y.1 x0 ∈ iSup W := by
      rw [hc]
      trivial
    exact TopologicalSpace.Opens.mem_iSup.mp h
  have hr : Set.range y.1 ⊆ Set.range (W m).ι := by
    rintro _ ⟨a, rfl⟩
    rw [hone a, Scheme.Opens.range_ι]
    exact hm
  refine ⟨m, ?_, ?_⟩
  · refine ⟨⟨IsOpenImmersion.lift (W m).ι y.1 hr, ?_⟩, ?_, ?_⟩
    · rw [← Category.assoc, IsOpenImmersion.lift_fac]
      exact y.2
    · exact IsOpenImmersion.lift_fac _ _ _
    · intro z hz
      apply Subtype.ext
      rw [← cancel_mono (W m).ι, hz]
      exact (IsOpenImmersion.lift_fac _ _ _).symm
  · rintro m' ⟨z, hz, -⟩
    by_contra hne
    have h1 : y.1 x0 ∈ W m' := by
      have hz' : z.1 ≫ (W m').ι = y.1 := hz
      rw [← hz', Scheme.Hom.comp_apply]
      exact (z.1 x0).2
    have h2 : y.1 x0 ∈ W m' ⊓ W m := ⟨h1, hm⟩
    rw [hd m' m hne] at h2
    exact h2
end

section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry GlobalTheory.HodgeCoh GlobalTheory.CechDR ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section
namespace UpperTheory.Cb

section Alg

variable {B B' K L : Type} [CommRing B] [CommRing B'] [IsDomain B] [IsDomain B'] [Field K] [Field L]
  [Algebra B B'] [Algebra B K] [Algebra K L] [Algebra B' L] [Algebra B L]
  [IsScalarTower B K L] [IsScalarTower B B' L] [IsFractionRing B K] [IsFractionRing B' L]

include K L in
private theorem injective_algebraMap : Function.Injective (algebraMap B B') := by
  have h : Function.Injective (algebraMap B L) := by
    rw [IsScalarTower.algebraMap_eq B K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective B K)
  rw [IsScalarTower.algebraMap_eq B B' L] at h
  exact Function.Injective.of_comp (f := algebraMap B' L) h

include K L in
private theorem isLocalization_of_integral [Algebra.IsIntegral B B'] :
    IsLocalization (Algebra.algebraMapSubmonoid B' (nonZeroDivisors B)) L := by
  have hinj : Function.Injective (algebraMap B B') := injective_algebraMap (K := K) (L := L)
  have hL : Function.Injective (algebraMap B' L) := IsFractionRing.injective B' L
  refine { map_units := ?_, surj := ?_, exists_of_eq := ?_ }
  · rintro ⟨_, r, hr, rfl⟩
    refine IsUnit.mk0 _ ?_
    exact (map_ne_zero_iff _ hL).2 ((map_ne_zero_iff _ hinj).2 (nonZeroDivisors.ne_zero hr))
  · intro z
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := B') z
    obtain ⟨r, hr, t, ht⟩ := (Algebra.IsIntegral.isIntegral (R := B) b).isAlgebraic.exists_nonzero_dvd hb
    refine ⟨⟨a * t, ⟨algebraMap B B' r, r, mem_nonZeroDivisors_of_ne_zero hr, rfl⟩⟩, ?_⟩
    have hb0 : algebraMap B' L b ≠ 0 := (map_ne_zero_iff _ hL).2 (nonZeroDivisors.ne_zero hb)
    have e : algebraMap B' L (algebraMap B B' r) = algebraMap B' L b * algebraMap B' L t := by
      rw [ht, map_mul]
    change algebraMap B' L a / algebraMap B' L b * algebraMap B' L (algebraMap B B' r) =
      algebraMap B' L (a * t)
    rw [e, map_mul]
    field_simp
  · intro x y h
    exact ⟨1, by rw [hL h]⟩

include K L in
private theorem isPushout_of_integral [Algebra.IsIntegral B B'] : Algebra.IsPushout B K B' L := by
  have h1 := isLocalization_of_integral (B := B) (B' := B') (K := K) (L := L)
  have h2 := (isLocalizedModule_iff_isLocalization (S := nonZeroDivisors B) (A := B') (Aₛ := L)).2 h1
  exact ⟨(isLocalizedModule_iff_isBaseChange (nonZeroDivisors B) K _).1 h2⟩

private theorem algebraMap_etTrace [Module.Finite B B'] [Algebra.Etale B B'] (b : B') :
    algebraMap B K (etTrace B B' b) = Algebra.trace K L (algebraMap B' L b) := by
  haveI := projective_of_etale B B'
  haveI hp := isPushout_of_integral (B := B) (B' := B') (K := K) (L := L)
  haveI : Module.Finite K L := Module.Finite.equiv hp.out.equiv
  rw [← algTrace_eq_trace, algTrace_of_isPushout (B := B) (B' := B') b]
  rfl

end Alg

theorem germ_comap_eq_algebraMap_germ_of_finite_etale : ∀ (Z Y : Scheme.{0}) [IsIntegral Z] [IsIntegral Y] (p : Z ⟶ Sp ℂ) (p' : Y ⟶ Sp ℂ)
    (c : Y ⟶ Z) (hc : c ≫ p = p') [IsFinite c] [Etale c] [Algebra Z.functionField Y.functionField],
    (∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c ⁻¹ᵁ V) (g : Γ(Z, V)),
      (Y.presheaf.germ (c ⁻¹ᵁ V) (genericPoint Y) hV').hom ((c.app V).hom g) =
        algebraMap Z.functionField Y.functionField ((Z.presheaf.germ V (genericPoint Z) hV).hom g)) →
    ∀ (V : Z.Opens) (hV : IsAffineOpen V) (hg : genericPoint Z ∈ V)
      (hg' : genericPoint Y ∈ c ⁻¹ᵁ V) (b' : Γ(Y, c ⁻¹ᵁ V)),
      (Z.presheaf.germ V (genericPoint Z) hg).hom (secTrace (f := c) p p' hV b') =
        Algebra.trace Z.functionField Y.functionField
          ((Y.presheaf.germ (c ⁻¹ᵁ V) (genericPoint Y) hg').hom b') := by
  intro Z Y _ _ p p' c _ _ _ _ hg V hVa hV hV' b'
  haveI : Nonempty V := ⟨⟨_, hV⟩⟩
  haveI : Nonempty (c ⁻¹ᵁ V : Y.Opens) := ⟨⟨_, hV'⟩⟩
  letI := secAlg p p' c V
  haveI := sec_finite (s := p) (s' := p') (f := c) hVa
  haveI := sec_etale (s := p) (s' := p') (f := c) hVa
  letI : Algebra (Sec p V) Z.functionField := (Z.germToFunctionField V).hom.toAlgebra
  letI : Algebra (Sec p' (c ⁻¹ᵁ V)) Y.functionField := (Y.germToFunctionField (c ⁻¹ᵁ V)).hom.toAlgebra
  letI : Algebra (Sec p V) Y.functionField :=
    ((algebraMap Z.functionField Y.functionField).comp (algebraMap (Sec p V) Z.functionField)).toAlgebra
  haveI : IsScalarTower (Sec p V) Z.functionField Y.functionField := .of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower (Sec p V) (Sec p' (c ⁻¹ᵁ V)) Y.functionField :=
    .of_algebraMap_eq fun g ↦ (hg V hV hV' g).symm
  haveI : IsDomain (Sec p V) := inferInstanceAs (IsDomain Γ(Z, V))
  haveI : IsDomain (Sec p' (c ⁻¹ᵁ V)) := inferInstanceAs (IsDomain Γ(Y, c ⁻¹ᵁ V))
  haveI : IsFractionRing (Sec p V) Z.functionField :=
    functionField_isFractionRing_of_isAffineOpen Z V hVa
  haveI : IsFractionRing (Sec p' (c ⁻¹ᵁ V)) Y.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y (c ⁻¹ᵁ V) (hVa.preimage c)
  exact algebraMap_etTrace (B := Sec p V) (B' := Sec p' (c ⁻¹ᵁ V)) (K := Z.functionField)
    (L := Y.functionField) b'

end UpperTheory.Cb
end
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR KaehlerDifferential GlobalTheory.W1

theorem UpperTheory.Cb.smoothOfRelativeDimension_comp_etale :
    ∀ (Z Y : Scheme.{0}) (s : Z ⟶ Sp ℂ) (s' : Y ⟶ Sp ℂ) (c : Y ⟶ Z), c ≫ s = s' → ∀ (d : ℕ) [SmoothOfRelativeDimension d s], Etale c → SmoothOfRelativeDimension d s' := by
  intro Z Y s s' c h d _ hc
  subst h
  have h0 : SmoothOfRelativeDimension 0 c := (Etale.iff_smoothOfRelativeDimension_zero c).1 hc
  have h1 : SmoothOfRelativeDimension (0 + d) (c ≫ s) := smoothOfRelativeDimension_comp 0 d c s
  rwa [Nat.zero_add] at h1
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR KaehlerDifferential GlobalTheory.W1

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem UpperTheory.Cb.adjoin_degree_zero_variables_eq_top (N : ℕ) :
    Algebra.adjoin (↥(MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ 0))
      (Set.range (MvPolynomial.X : Fin (N + 1) → MvPolynomial (Fin (N + 1)) ℂ)) = ⊤ := by
  rw [eq_top_iff]
  intro p _
  induction p using MvPolynomial.induction_on with
  | C a =>
    have hC : MvPolynomial.C a ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ 0 :=
      MvPolynomial.isHomogeneous_C _ a
    exact Subalgebra.algebraMap_mem _ (⟨_, hC⟩ : ↥(MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ 0))
  | add p q hp hq => exact Subalgebra.add_mem _ (hp trivial) (hq trivial)
  | mul_X p i hp =>
    exact Subalgebra.mul_mem _ (hp trivial) (Algebra.subset_adjoin ⟨i, rfl⟩)

private theorem UpperTheory.Cb.compactSpace_projective_space (N : ℕ) : CompactSpace (PSpace ℂ N) := by
  have hX : ∀ i : Fin (N + 1), (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) ℂ) ∈
      MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ 1 :=
    fun i => MvPolynomial.isHomogeneous_X ℂ i
  have hcov := Proj.iSup_basicOpen_eq_top' (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ)
    (MvPolynomial.X : Fin (N + 1) → MvPolynomial (Fin (N + 1)) ℂ) (fun i => ⟨1, hX i⟩)
    (UpperTheory.Cb.adjoin_degree_zero_variables_eq_top N)
  refine ⟨?_⟩
  have huniv : (Set.univ : Set (PSpace ℂ N)) =
      ⋃ i, ((Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ)
        (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) ℂ) : (PSpace ℂ N).Opens) : Set (PSpace ℂ N)) := by
    have := congrArg (fun U : (PSpace ℂ N).Opens => (U : Set (PSpace ℂ N))) hcov
    simpa using this.symm
  rw [huniv]
  exact isCompact_iUnion fun i =>
    (Proj.isAffineOpen_basicOpen _ _ (hX i) Nat.one_pos).isCompact

theorem UpperTheory.Cb.compactSpace_of_projective_and_of_finite :
    (∀ (Z : Scheme.{0}) (s : Z ⟶ Sp ℂ), IsProjOver s → CompactSpace Z) ∧ ∀ (Y Z : Scheme.{0}) (c : Y ⟶ Z), IsFinite c → CompactSpace Z → CompactSpace Y := by
  refine ⟨?_, ?_⟩
  · rintro Z s ⟨N, i, hi, -⟩
    haveI := UpperTheory.Cb.compactSpace_projective_space N
    exact QuasiCompact.compactSpace_of_compactSpace i
  · intro Y Z c hc hZ
    exact QuasiCompact.compactSpace_of_compactSpace c
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR KaehlerDifferential GlobalTheory.W1

theorem UpperTheory.Cb.isProjOver_restrict_clopen :
    ∀ (Z : Scheme.{0}) (s : Z ⟶ Sp ℂ) (V : Z.Opens), IsClosed (V : Set Z) → IsProjOver s → IsProjOver (V.ι ≫ s) := by
  rintro Z s V hV ⟨N, i, hi, rfl⟩
  have hc : IsClosedImmersion V.ι := by
    apply IsClosedImmersion.of_isPreimmersion
    simpa using hV
  exact ⟨N, V.ι ≫ i, inferInstance, by simp⟩
end
