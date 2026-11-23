module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianTorsionFiniteAndMulNSurjective
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle057
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle992
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteOfIsClosedTorusZariskiOfPowEqOne
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2134
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.DimEqZero
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.descentLocInj : ∀ (k : Type) [Field k] (P : Polynomial k), P ≠ 0 → ∀ (R : Subring k) (P₁ : Polynomial R) (h : IsUnit (((algebraMap (Polynomial k) (Localization.Away P)).comp (Polynomial.mapRingHom R.subtype)) P₁)), P₁.map R.subtype = P → Function.Injective (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ h) := by
  intro k _ P hP R P₁ h _
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨⟨f, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers P₁) z
  simp only at hz ⊢
  unfold IsLocalization.Away.lift at hz
  rw [IsLocalization.lift_mk'_spec, mul_zero] at hz
  have h2 := hz
  have hinj : Function.Injective (algebraMap (Polynomial k) (Localization.Away P)) :=
    IsLocalization.injective (Localization.Away P) (powers_le_nonZeroDivisors_of_noZeroDivisors hP)
  have h3 : f.map R.subtype = 0 := by
    apply hinj
    simpa using h2
  have h4 : f = 0 := by
    have := Polynomial.map_injective R.subtype Subtype.val_injective
    exact this (by simpa using h3)
  subst h4
  simp
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem localization_away_descent_range :
 ∀ (k : Type) [Field k] (P : Polynomial k) (T : Finset (Localization.Away P)), ∃ F : Finset k, ∀ (R : Subring k), (F : Set k) ⊆ R → ∀ (P₁ : Polynomial R) (h : IsUnit (((algebraMap (Polynomial k) (Localization.Away P)).comp (Polynomial.mapRingHom R.subtype)) P₁)), P₁.map R.subtype = P → ∀ t ∈ T, t ∈ (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ h).range := by
  classical
  intro k _ P T
  have hs : ∀ t : Localization.Away P, ∃ (f : Polynomial k) (n : ℕ),
      IsLocalization.mk' (Localization.Away P) f
        (⟨P ^ n, n, rfl⟩ : Submonoid.powers P) = t := by
    intro t
    obtain ⟨⟨f, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers P) t
    obtain ⟨n, hn⟩ := s.2
    exact ⟨f, n, by congr 1; exact Subtype.ext hn⟩
  choose f n hfn using hs
  refine ⟨T.biUnion (fun t => (f t).coeffs), ?_⟩
  intro R hF P₁ h hP t ht
  have hlift : f t ∈ Polynomial.lifts R.subtype := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro m
    by_cases hm : (f t).coeff m = 0
    · exact ⟨0, by simp [hm]⟩
    · have : (f t).coeff m ∈ (T.biUnion (fun t => (f t).coeffs) : Set k) := by
        simp only [Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe]
        exact ⟨t, ht, Polynomial.coeff_mem_coeffs hm⟩
      exact ⟨⟨_, hF this⟩, rfl⟩
  obtain ⟨f₁, hf₁⟩ := (Polynomial.mem_lifts _).mp hlift
  refine ⟨IsLocalization.mk' (Localization.Away P₁) f₁
    (⟨P₁ ^ n t, n t, rfl⟩ : Submonoid.powers P₁), ?_⟩
  rw [IsLocalization.Away.lift, IsLocalization.lift_mk'_spec]
  simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_mapRingHom, hf₁,
    Polynomial.map_pow, hP]
  have key := IsLocalization.mk'_spec' (Localization.Away P) (f t)
    (⟨P ^ n t, n t, rfl⟩ : Submonoid.powers P)
  rw [hfn t] at key
  exact key.symm

end GlobalTheory
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SpreadConn

variable {S : Scheme.{0}}

theorem unit_comp (G : Over S) [GrpObj G] : (η[G]).left ≫ G.hom = 𝟙 S := by
  have h := Over.w (η[G])
  have h2 : (𝟙_ (Over S)).hom = 𝟙 S := rfl
  rwa [h2] at h

theorem hom_unit (G : Over S) [GrpObj G] (s : S) : G.hom ((η[G]).left s) = s := by
  rw [← Scheme.Hom.comp_apply, unit_comp]
  rfl

theorem isConnected_fibre (G : Over S) [GrpObj G] (U : Set G.left)
    (hU : ∀ x : G.left, x ∈ U ↔ x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x)))
    (s : S) (h : G.hom ⁻¹' {s} ⊆ U) : _root_.IsConnected (G.hom ⁻¹' {s}) := by
  have hu : (η[G]).left s ∈ G.hom ⁻¹' {s} := hom_unit G s
  have he : connectedComponentIn (G.hom ⁻¹' {s}) ((η[G]).left s) = G.hom ⁻¹' {s} := by
    refine (connectedComponentIn_subset _ _).antisymm fun x hx => ?_
    have h1 := (hU x).1 (h hx)
    have hx' : G.hom x = s := hx
    rwa [hx'] at h1
  rw [← he]
  exact isConnected_connectedComponentIn_iff.2 hu

theorem subset_of_isPreconnected (G : Over S) [GrpObj G] (U : Set G.left)
    (hU : ∀ x : G.left, x ∈ U ↔ x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x)))
    (s : S) (h : _root_.IsPreconnected (G.hom ⁻¹' {s})) : G.hom ⁻¹' {s} ⊆ U := by
  intro x hx
  have hx' : G.hom x = s := hx
  refine (hU x).2 ?_
  rw [hx']
  exact h.subset_connectedComponentIn (hom_unit G s) subset_rfl hx

theorem geometricallyConnected_fibre (G : Over S) [GrpObj G] [LocallyOfFiniteType G.hom]
    [QuasiCompact G.hom] (s : S) (h : _root_.IsConnected (G.hom ⁻¹' {s})) :
    GeometricallyConnected (G.hom.fiberToSpecResidueField s) := by
  have hc : ConnectedSpace (G.hom.fiber s) :=
    (G.hom.fiberHomeo s).connectedSpace_iff.2 (isConnected_iff_connectedSpace.1 h)
  exact GlobalTheory.RatPointConn.geometricallyConnected_of_ratPoint (S.residueField s)
    (Over.mk (G.hom.fiberToSpecResidueField s))
    (inferInstanceAs (LocallyOfFiniteType (pullback.snd G.hom (S.fromSpecResidueField s))))
    (inferInstanceAs (QuasiCompact (pullback.snd G.hom (S.fromSpecResidueField s)))) hc
    ⟨Over.homMk (pullback.lift (S.fromSpecResidueField s ≫ (η[G]).left) (𝟙 _)
      (by rw [Category.assoc, unit_comp, Category.comp_id, Category.id_comp]))
      (pullback.lift_snd _ _ _)⟩

theorem isConnected_of_geometricallyConnected_fibre {X : Scheme.{0}} (f : X ⟶ S) (s : S)
    (h : GeometricallyConnected (f.fiberToSpecResidueField s)) : _root_.IsConnected (f ⁻¹' {s}) := by
  have hc : ConnectedSpace (f.fiber s) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f.fiberToSpecResidueField s)
  exact isConnected_iff_connectedSpace.2 ((f.fiberHomeo s).connectedSpace_iff.1 hc)

end GlobalTheory.SpreadConn

namespace GlobalTheory.SpreadConn

theorem geometricallyConnected_of_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G], Smooth G.hom → QuasiCompact G.hom → ∀ (K : Type) [Field K] (e : R →+* K), Function.Injective e → GeometricallyConnected (pullback.snd G.hom (spMap e)) → ∃ f : R, e f ≠ 0 ∧ ∀ (F : Type) [Field F] (ψ : R →+* F), IsUnit (ψ f) → GeometricallyConnected (pullback.snd G.hom (spMap ψ)) := by
  intro R _ _ _ G _ hs hq K _ e he hgc
  obtain ⟨G₀, _, j, -, hjo, hj⟩ := GlobalTheory.identityComponentOpen (Sp R) G hs
  let U : Set G.left := Set.range j.left
  let η₀ : Sp R := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)
  have hη : η₀ ∈ Set.range (spMap e) := ⟨(default : PrimeSpectrum K), by
    apply PrimeSpectrum.ext
    change Ideal.comap e (default : PrimeSpectrum K).asIdeal = ⊥
    have h0 : (default : PrimeSpectrum K).asIdeal = ⊥ := Ideal.eq_bot_of_prime _
    rw [h0]
    exact Ideal.comap_bot_of_injective _ he⟩
  have hgen : GeometricallyConnected (G.hom.fiberToSpecResidueField η₀) :=
    GlobalTheory.GenericSplit.geometricallyConnected_snd_of_range_subset G.hom (spMap e)
      ((Sp R).fromSpecResidueField η₀)
      (by rw [Scheme.range_fromSpecResidueField]; exact Set.singleton_subset_iff.2 hη) hgc
  have hsub0 : G.hom ⁻¹' {η₀} ⊆ U := subset_of_isPreconnected G U hj η₀
    (isConnected_of_geometricallyConnected_fibre G.hom η₀ hgen).isPreconnected
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have : IsNoetherian G.left := {}
  have hUo : IsOpen U := j.left.isOpenEmbedding.isOpen_range
  have hZ : Topology.IsConstructible Uᶜ :=
    (IsRetrocompact.isConstructible hUo fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _).compl
  have hC : Topology.IsConstructible (G.hom '' Uᶜ) := G.hom.isConstructible_image hZ
  obtain ⟨V, hV, h1, h2⟩ := GlobalTheory.exists_isOpen_inter_closure_subset_of_isConstructible continuous_id hC.compl
  rw [Set.preimage_id] at h1 h2
  have hηC : η₀ ∈ (G.hom '' Uᶜ)ᶜ := by
    rintro ⟨x, hx, hxη⟩
    exact hx (hsub0 hxη)
  have hgenz : ∀ p : Sp R, η₀ ⤳ p := fun p =>
    (PrimeSpectrum.le_iff_specializes (η₀ : PrimeSpectrum R) (p : PrimeSpectrum R)).1
      (show (⊥ : Ideal R) ≤ (p : PrimeSpectrum R).asIdeal from bot_le)
  have hcl : closure (G.hom '' Uᶜ)ᶜ = Set.univ := by
    refine Set.eq_univ_of_forall fun p => ?_
    exact closure_mono (Set.singleton_subset_iff.2 hηC) (specializes_iff_mem_closure.1 (hgenz p))
  rw [hcl, Set.inter_univ] at h1 h2
  have hVne : V.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, closure_empty] at h2
    exact Set.empty_ne_univ h2
  obtain ⟨p₀, hp₀⟩ := hVne
  have hηV : η₀ ∈ V := (hgenz p₀).mem_open hV hp₀
  obtain ⟨_, ⟨f, rfl⟩, hf, hfV⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hηV hV
  refine ⟨f, fun h0 => (PrimeSpectrum.mem_basicOpen _ _).1 hf ?_, fun F _ ψ hψ => ?_⟩
  · rw [he (h0.trans (map_zero e).symm)]
    exact zero_mem _
  · let p : Sp R := spMap ψ (default : PrimeSpectrum F)
    have hpf : p ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := by
      refine (PrimeSpectrum.mem_basicOpen f (p : PrimeSpectrum R)).2 fun hfp => ?_
      change ψ f ∈ (default : PrimeSpectrum F).asIdeal at hfp
      exact (default : PrimeSpectrum F).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hfp hψ)
    have hpC : p ∉ G.hom '' Uᶜ := h1 (hfV hpf)
    have hsub : G.hom ⁻¹' {p} ⊆ U := fun x hx => by
      by_contra hxU
      exact hpC ⟨x, hxU, hx⟩
    have hfib := geometricallyConnected_fibre G p (isConnected_fibre G U hj p hsub)
    refine GlobalTheory.GenericSplit.geometricallyConnected_snd_of_range_subset G.hom
      ((Sp R).fromSpecResidueField p) (spMap ψ) ?_ hfib
    rw [Scheme.range_fromSpecResidueField]
    rintro _ ⟨y, rfl⟩
    show spMap ψ y = p
    rw [Subsingleton.elim (α := PrimeSpectrum F) y default]

end GlobalTheory.SpreadConn
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SepClosedDiv

theorem exists_section_of_etale {Ω : Type} [Field Ω] [IsSepClosed Ω] {X : Scheme.{0}} (f : X ⟶ Sp Ω)
    [Etale f] (x : X) : ∃ s : Sp Ω ⟶ X, s ≫ f = 𝟙 _ := by
  let i := X.affineCover.idx x
  obtain ⟨y, -⟩ := X.affineCover.covers x
  obtain ⟨R, e⟩ : ∃ R : CommRingCat, X.affineCover.X i = Spec R := ⟨_, rfl⟩
  let φ : CommRingCat.of Ω ⟶ R := Spec.preimage (eqToHom e.symm ≫ X.affineCover.f i ≫ f)
  have hφ : Spec.map φ = eqToHom e.symm ≫ X.affineCover.f i ≫ f := Spec.map_preimage _
  have hg : Etale (Spec.map φ) := by rw [hφ]; infer_instance
  have hr : φ.hom.Etale := (HasRingHomProperty.Spec_iff (P := @Etale)).1 hg
  letI := φ.hom.toAlgebra
  have : Algebra.Etale Ω R := hr
  let q : PrimeSpectrum R := (eqToHom e).base y
  obtain ⟨ψ⟩ := GlobalTheory.nonempty_algHom_of_etale_of_isSepClosed (R := Ω) (A := R) (K := Ω) q.asIdeal
    (by
      rw [(Ideal.comap (algebraMap Ω R) q.asIdeal).eq_bot_of_prime]
      exact ((RingHom.injective_iff_ker_eq_bot _).1 (algebraMap Ω Ω).injective).symm)
  refine ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ eqToHom e.symm ≫ X.affineCover.f i, ?_⟩
  simp only [Category.assoc]
  rw [← hφ, ← Spec.map_comp]
  rw [← Spec.map_id]
  congr 1
  ext a
  exact ψ.commutes a

theorem exists_pow_eq : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosed Ω] (A : Over (Sp K)) [GrpObj A]
    [IsCommMonObj A], IsAbelianScheme A → ∀ n : ℕ, (n : K) ≠ 0 → ∀ x : ptOver K Ω ⟶ A, ∃ y, y ^ n = x := by
  intro K Ω _ _ _ _ A _ _ hA n hn x
  have := hA.smooth
  have hu : IsUnit (n : Γ(Sp K, ⊤)) := by
    simpa using (isUnit_iff_ne_zero.2 hn).map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  have he : Etale (mulN A n).left := GlobalTheory.GrpTangent.etale_mulN A hu
  have hs : Surjective (mulN A n).left := GlobalTheory.surjective_mulN_of_isAbelianScheme K A hA n hn
  let m := (mulN A n).left
  have he' : Etale (pullback.snd m x.left) := inferInstance
  obtain ⟨z, -⟩ := (pullback.snd m x.left).surjective (IsLocalRing.closedPoint Ω)
  obtain ⟨s, hs'⟩ := exists_section_of_etale (pullback.snd m x.left) z
  have h : (s ≫ pullback.fst m x.left) ≫ m = x.left := by
    rw [Category.assoc, pullback.condition, reassoc_of% hs']
  refine ⟨Over.homMk (s ≫ pullback.fst m x.left) ?_, ?_⟩
  · change (s ≫ pullback.fst m x.left) ≫ A.hom = _
    rw [← Over.w (mulN A n), ← Category.assoc, h]
    exact Over.w x
  · rw [← GlobalTheory.GrpTangent.comp_mulN]
    exact Over.OverMorphism.ext h

end GlobalTheory.SepClosedDiv
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem flat_surjective_spMap_of_dvr : ∀ (R K W K' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] [Algebra R W] [Algebra K K'] [Algebra R K'] [IsScalarTower R W K'] [IsScalarTower R K K'], (maximalIdeal R).map (algebraMap R W) = maximalIdeal W → Flat (spMap (algebraMap R W)) ∧ Surjective (spMap (algebraMap R W)) := by
  intro R K W K' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h
  have hinj : Function.Injective (algebraMap R W) := by
    have h1 : (algebraMap W K').comp (algebraMap R W) = (algebraMap K K').comp (algebraMap R K) := by
      rw [← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
    have h2 : Function.Injective ((algebraMap K K').comp (algebraMap R K)) :=
      (algebraMap K K').injective.comp (IsFractionRing.injective R K)
    rw [← h1] at h2
    exact Function.Injective.of_comp h2
  have hfl : Module.Flat R W := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    intro x hx
    obtain ⟨⟨a, ha⟩, hax⟩ := (Submodule.mem_torsion_iff x).1 hx
    have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
    change a • x = 0 at hax
    rw [Algebra.smul_def] at hax
    rcases mul_eq_zero.1 hax with h0 | h0
    · exact absurd (hinj (h0.trans (map_zero _).symm)) ha0
    · simp [h0]
  have hloc : IsLocalHom (algebraMap R W) := by
    refine ((IsLocalRing.local_hom_tfae (algebraMap R W)).out 1 3).2 ?_
    rw [h]
  have hff : Module.FaithfullyFlat R W := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hrf : (algebraMap R W).FaithfullyFlat := RingHom.faithfullyFlat_algebraMap_iff.2 hff
  obtain ⟨h1, h2⟩ := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap R W))).2 hrf
  exact ⟨h1, h2⟩

end GlobalTheory
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem relDim_le_of_formallyUnramified (R B C : Type) [CommRing R] [CommRing B] [CommRing C]
    [Algebra R B] [Algebra R C] [Algebra B C] [IsScalarTower R B C] [Nontrivial C]
    [Algebra.FormallyUnramified B C] (g g' : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension g R B]
    [Algebra.IsStandardSmoothOfRelativeDimension g' R C] : g' ≤ g := by
  have : Nontrivial B := (algebraMap B C).domain_nontrivial
  have : Algebra.IsStandardSmooth R B := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth g
  have : Module.Free B Ω[B⁄R] := Algebra.IsStandardSmooth.free_kaehlerDifferential
  have hs : Function.Surjective (KaehlerDifferential.mapBaseChange R B C) := fun x =>
    (KaehlerDifferential.exact_mapBaseChange_map R B C x).mp (Subsingleton.elim _ _)
  have h1 := LinearMap.rank_le_of_surjective _ hs
  rw [Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential g', Module.rank_baseChange,
    Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential g] at h1
  simpa using h1

end GlobalTheory

namespace GlobalTheory

theorem relDim_le_of_surjective_away {R B A L : Type} [CommRing R] [CommRing B] [CommRing A] [CommRing L]
    [Algebra A L] (t : A) [IsLocalization.Away t L] [Nontrivial L] (φ : R →+* B) (ψ : B →+* A)
    (hψ : Function.Surjective ψ) (g g' : ℕ) (hφ : RingHom.IsStandardSmoothOfRelativeDimension g φ)
    (hL : RingHom.IsStandardSmoothOfRelativeDimension g' ((algebraMap A L).comp (ψ.comp φ))) :
    g' ≤ g := by
  letI : Algebra R B := φ.toAlgebra
  letI : Algebra B A := ψ.toAlgebra
  letI : Algebra B L := ((algebraMap A L).comp ψ).toAlgebra
  letI : Algebra R L := ((algebraMap A L).comp (ψ.comp φ)).toAlgebra
  haveI : IsScalarTower R B L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower B A L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.FormallyUnramified B A := Algebra.FormallyUnramified.of_surjective (Algebra.ofId B A) hψ
  haveI : Algebra.FormallyUnramified A L := Algebra.FormallyUnramified.of_isLocalization (Submonoid.powers t)
  haveI : Algebra.FormallyUnramified B L := Algebra.FormallyUnramified.comp B A L
  haveI : Algebra.IsStandardSmoothOfRelativeDimension g R B := hφ
  haveI : Algebra.IsStandardSmoothOfRelativeDimension g' R L := hL
  exact relDim_le_of_formallyUnramified R B L g g'

end GlobalTheory

namespace GlobalTheory

theorem relDim_le_of_isClosedImmersion : ∀ (k : Type) [Field k] (N G : Over (Sp k)) (ν : N ⟶ G),
    IsClosedImmersion ν.left → Nonempty N.left → ∀ g g' : ℕ, SmoothOfRelativeDimension g G.hom →
    SmoothOfRelativeDimension g' N.hom → g' ≤ g := by
  intro k _ N G ν hν ⟨x⟩ g g' hG hN
  obtain ⟨U, hU, V, hV, hx, e, h⟩ := hG.exists_isStandardSmoothOfRelativeDimension (ν.left x)
  let V' : N.left.Opens := ν.left ⁻¹ᵁ V
  have hV' : IsAffineOpen V' := hV.preimage ν.left
  have hN' : SmoothOfRelativeDimension g' (ν.left ≫ G.hom) := by rw [Over.w ν]; exact hN
  have e' : V' ≤ (ν.left ≫ G.hom) ⁻¹ᵁ U := fun y hy => e hy
  obtain ⟨s, hs, h'⟩ := HasRingHomProperty.appLE (@SmoothOfRelativeDimension g') _ hN' ⟨U, hU⟩ ⟨V', hV'⟩ e'
  have : Nonempty V' := ⟨⟨x, hx⟩⟩
  obtain ⟨p, hp⟩ := Ideal.exists_maximal Γ(N.left, V')
  obtain ⟨t, ht, htp⟩ : ∃ t ∈ s, t ∉ p := by
    by_contra hc
    exact hp.ne_top (top_le_iff.1 (hs ▸ Ideal.span_le.2 fun t ht => by_contra fun h => hc ⟨t, ht, h⟩))
  have : Nontrivial (Localization.Away t) := by
    by_contra hc
    obtain ⟨k, hk⟩ := (IsLocalization.subsingleton_iff (M := Submonoid.powers t)).1
      (not_nontrivial_iff_subsingleton.1 hc)
    exact htp (hp.isPrime.mem_of_pow_mem k (by rw [show t ^ k = 0 from hk]; exact p.zero_mem))
  have h₁ := h' t ht
  have hψ : Function.Surjective (ν.left.appLE V V' le_rfl).hom := by
    have := ν.left.app_surjective V hV
    rw [Scheme.Hom.app_eq_appLE] at this
    exact this
  refine relDim_le_of_surjective_away (L := Localization.Away t) t (G.hom.appLE U V e).hom
    (ν.left.appLE V V' le_rfl).hom hψ g g' h ?_
  rw [← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE ν.left G.hom U V V' e le_rfl]
  exact h₁

end GlobalTheory
end

section

open MeasureTheory Filter Topology GlobalTheory.ResLine
open scoped ENNReal

theorem _root_.GlobalTheory.T.mul_lintegral_rpow_le_of_shell_bound' : ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (h : X → ℝ) (d : ℝ) (B : ℝ≥0∞), Measurable h → (∀ x, 0 < h x) → 0 < d → (∀ j : ℕ, μ {x | Real.exp (-(j + 1 : ℝ)) < h x ∧ h x ≤ Real.exp (-(j : ℝ))} ≤ B * ENNReal.ofReal (Real.exp (d * j))) → ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ENNReal.ofReal ε * ∫⁻ x, (if h x ≤ 1 then ENNReal.ofReal (h x ^ (d + ε)) else 0) ∂μ ≤ 2 * B := by
  first | exact @GlobalTheory.ResLine.mul_lintegral_rpow_le_of_shell_bound | exact GlobalTheory.ResLine.mul_lintegral_rpow_le_of_shell_bound | (intros; apply GlobalTheory.ResLine.mul_lintegral_rpow_le_of_shell_bound <;> assumption)
end
