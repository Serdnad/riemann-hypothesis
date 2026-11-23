module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle213
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle188
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSchemeOfThickenings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle373
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle190
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle377
public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryPQContinuousCharacterEqDetPowProd
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle374
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConcaveTwistEtaInequalities
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle370
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle376
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Finite
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle003
import ReciprocityTheory.L2DbarEstimates.SkodaWeights.Bundle001

@[expose] public section

section

noncomputable section

open TensorProduct

namespace GlobalTheory

section AdicAux

variable {S : Type*} [CommRing S] (a : S)

theorem mem_span_singleton_pow_smul_top_iff_exists {N : Type*} [AddCommGroup N] [Module S N] (n : ℕ)
    (x : N) : x ∈ (Ideal.span {a} ^ n • ⊤ : Submodule S N) ↔ ∃ y : N, x = a ^ n • y := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  exact exists_congr fun v => by simp [eq_comm]

theorem isAdicComplete_fin_pi [IsAdicComplete (Ideal.span {a}) S] (k : ℕ) :
    IsAdicComplete (Ideal.span {a}) (Fin k → S) := by
  refine { haus' := ?_, toIsPrecomplete := ⟨?_⟩ }
  · intro x hx
    funext i
    refine IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {a}) S) (x i) fun n => ?_
    have h := hx n
    rw [SModEq.sub_mem, mem_span_singleton_pow_smul_top_iff_exists] at h ⊢
    obtain ⟨y, hy⟩ := h
    exact ⟨y i, by simpa using congrFun hy i⟩
  · intro f hf
    have key : ∀ i, ∃ L : S, ∀ n,
        f n i ≡ L [SMOD (Ideal.span {a} ^ n • ⊤ : Submodule S S)] := fun i =>
      IsPrecomplete.prec (inferInstance : IsPrecomplete (Ideal.span {a}) S) fun {m n} hmn => by
        have h := hf hmn
        rw [SModEq.sub_mem, mem_span_singleton_pow_smul_top_iff_exists] at h ⊢
        obtain ⟨y, hy⟩ := h
        exact ⟨y i, by simpa using congrFun hy i⟩
    choose L hL using key
    refine ⟨L, fun n => ?_⟩
    rw [SModEq.sub_mem, mem_span_singleton_pow_smul_top_iff_exists]
    have h := fun i => (mem_span_singleton_pow_smul_top_iff_exists a n _).1 (SModEq.sub_mem.1 (hL i n))
    choose y hy using h
    exact ⟨y, funext fun i => by simpa using hy i⟩

theorem isAdicComplete_of_retraction {N F : Type*} [AddCommGroup N] [Module S N]
    [AddCommGroup F] [Module S F] [IsAdicComplete (Ideal.span {a}) F] (i : N →ₗ[S] F)
    (r : F →ₗ[S] N) (h : r ∘ₗ i = LinearMap.id) : IsAdicComplete (Ideal.span {a}) N := by
  refine { haus' := ?_, toIsPrecomplete := ⟨?_⟩ }
  · intro x hx
    have h1 : i x = 0 := IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {a}) F) (i x) fun n => by
      have h2 := hx n
      rw [SModEq.sub_mem, mem_span_singleton_pow_smul_top_iff_exists] at h2 ⊢
      obtain ⟨y, hy⟩ := h2
      rw [sub_zero] at hy ⊢
      exact ⟨i y, by rw [hy, map_smul]⟩
    have h3 := LinearMap.congr_fun h x
    rw [LinearMap.comp_apply, h1, map_zero, LinearMap.id_apply] at h3
    exact h3.symm
  · intro f hf
    obtain ⟨L, hL⟩ := IsPrecomplete.prec (f := fun n => i (f n))
      (inferInstance : IsPrecomplete (Ideal.span {a}) F) fun {m n} hmn => by
        have h2 := hf hmn
        rw [SModEq.sub_mem, mem_span_singleton_pow_smul_top_iff_exists] at h2 ⊢
        obtain ⟨y, hy⟩ := h2
        exact ⟨i y, by rw [← map_sub, hy, map_smul]⟩
    refine ⟨r L, fun n => ?_⟩
    have h2 := hL n
    rw [SModEq.sub_mem, mem_span_singleton_pow_smul_top_iff_exists] at h2 ⊢
    obtain ⟨y, hy⟩ := h2
    refine ⟨r y, ?_⟩
    have h3 := LinearMap.congr_fun h (f n)
    rw [LinearMap.comp_apply, LinearMap.id_apply] at h3
    rw [← map_smul, ← hy, map_sub, h3]

theorem isAdicComplete_of_finite_projective [IsAdicComplete (Ideal.span {a}) S] (N : Type*)
    [AddCommGroup N] [Module S N] [Module.Finite S N] [Module.Projective S N] :
    IsAdicComplete (Ideal.span {a}) N := by
  obtain ⟨k, f, hf⟩ := Module.Finite.exists_fin' S N
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  haveI := isAdicComplete_fin_pi a k
  exact isAdicComplete_of_retraction a s f hs

end AdicAux

namespace PDivGroup

open PDiv Coalgebra Bialgebra

variable {p : ℕ} {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (G : PDivGroup p R)

variable {M : Type} [AddCommGroup M] [Module R M] (c : M →ₗ[R] G.omega)

end PDivGroup

end GlobalTheory

namespace GlobalTheory

namespace PDivGroup

open PDiv

end PDivGroup

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem hypersurface_part_preirreducible_spreads : ∀ (A : Type) [CommRing A] (σ : Type) [Finite σ] (f g : MvPolynomial σ A) (i : σ), (∀ (k : Type) [Field k] (ψ : A →+* k), MvPolynomial.map ψ f ≠ 0) → (∀ (k : Type) [Field k] (ψ : A →+* k) (Q : σ → k), MvPolynomial.eval Q (MvPolynomial.map ψ f) = 0 → MvPolynomial.eval Q (MvPolynomial.map ψ g) ≠ 0 → MvPolynomial.eval Q (MvPolynomial.pderiv i (MvPolynomial.map ψ f)) ≠ 0) → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (φ : A →+* Ω), IsPreirreducible (PrimeSpectrum.zeroLocus {MvPolynomial.map φ f} \ PrimeSpectrum.zeroLocus {MvPolynomial.map φ g}) → ∃ (a : A) (I : Finset A), φ a ≠ 0 ∧ (∀ c ∈ I, φ c = 0) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (ψ : A →+* k), ψ a ≠ 0 → (∀ c ∈ I, ψ c = 0) → IsPreirreducible (PrimeSpectrum.zeroLocus {MvPolynomial.map ψ f} \ PrimeSpectrum.zeroLocus {MvPolynomial.map ψ g}) := by
  intro A _ σ _ f g i h0 hd Ω _ _ φ hirr
  have h3 := GlobalTheory.T.no_splitting_factorisation_of_pderiv_ne_zero Ω σ (MvPolynomial.map φ f) (MvPolynomial.map φ g) i f.totalDegree
    (hd Ω φ) hirr
  obtain ⟨a, I, ha, hI, h⟩ := GlobalTheory.T.splitting_absence_spreads_alt A σ f g f.totalDegree Ω φ h3
  refine ⟨a, I, ha, hI, fun k _ _ ψ hψa hψI => ?_⟩
  refine GlobalTheory.T.hypersurface_diff_isPreirreducible_of_no_splitting k σ (MvPolynomial.map ψ f) (MvPolynomial.map ψ g) f.totalDegree
    (h0 k ψ) ?_ (h k ψ hψa hψI)
  exact Finset.sup_mono (MvPolynomial.support_map_subset ψ f)

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace GlobalTheory.ThickGlue


set_option backward.isDefEq.respectTransparency false in
theorem isOpenImmersion_specMap_of_thickening : ∀ (B₀ : Scheme.{0}) (𝒰 : Set B₀.Opens), (∀ U ∈ 𝒰, IsAffineOpen U) → ∀ (𝒜 : B₀.Opensᵒᵖ ⥤ CommRingCat.{0}) (π : 𝒜 ⟶ B₀.presheaf), (∀ U ∈ 𝒰, Function.Surjective (π.app (op U)).hom ∧ IsNilpotent (RingHom.ker (π.app (op U)).hom)) → (∀ U ∈ 𝒰, ∀ a : 𝒜.obj (op U), letI := (𝒜.map (homOfLE (B₀.basicOpen_le ((π.app (op U)).hom a))).op).hom.toAlgebra; IsLocalization.Away a (𝒜.obj (op (B₀.basicOpen ((π.app (op U)).hom a))))) → ∀ U ∈ 𝒰, ∀ V ∈ 𝒰, ∀ h : U ≤ V, IsOpenImmersion (Spec.map (𝒜.map (homOfLE h).op)) := by
  intro B₀ 𝒰 haff 𝒜 p hp hloc
  have hloc' : ∀ U ∈ 𝒰, ∀ (a : 𝒜.obj (Opposite.op U)) (W : B₀.Opens)
      (_ : W = B₀.basicOpen ((p.app (Opposite.op U)).hom a)) (h : W ≤ U),
      IsOpenImmersion (Spec.map (𝒜.map (homOfLE h).op)) := by
    rintro U hU a W rfl h
    letI := (𝒜.map (homOfLE h).op).hom.toAlgebra
    haveI := hloc U hU a
    exact IsOpenImmersion.of_isLocalization
      (S := 𝒜.obj (Opposite.op (B₀.basicOpen ((p.app (Opposite.op U)).hom a)))) a
  have hci : ∀ U ∈ 𝒰, IsClosedImmersion (toSpec p U) := fun U hU ↦
    isClosedImmersion_toSpec p (haff U hU) (hp U hU).1
  have hsu : ∀ U ∈ 𝒰, Surjective (toSpec p U) := fun U hU ↦
    surjective_toSpec p (haff U hU) (hp U hU).1 (hp U hU).2
  have hnat : ∀ {U V : B₀.Opens} (h : U ≤ V) (x : U.toScheme),
      Spec.map (𝒜.map (homOfLE h).op) (toSpec p U x) = toSpec p V (B₀.homOfLE h x) :=
    fun h x ↦ congr($(toSpec_naturality p h) x).symm
  intro U hU V hV h
  have := hci V hV
  have := hsu U hU
  apply IsOpenImmersion.of_forall_source_exists
  · intro x y hxy
    obtain ⟨x, rfl⟩ := (toSpec p U).surjective x
    obtain ⟨y, rfl⟩ := (toSpec p U).surjective y
    rw [hnat, hnat] at hxy
    rw [(B₀.homOfLE h).isOpenEmbedding.injective
      ((toSpec p V).isClosedEmbedding.injective hxy)]
  · intro x
    obtain ⟨x, rfl⟩ := (toSpec p U).surjective x
    obtain ⟨f, hf, hxf⟩ := (haff V hV).exists_basicOpen_le (V := U) ⟨x.1, x.2⟩ (h x.2)
    obtain ⟨a, rfl⟩ := (hp V hV).1 f
    have h1 := hloc' U hU ((𝒜.map (homOfLE h).op).hom a) _ (by
      have := congr($(p.naturality (homOfLE h).op).hom a)
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
      rw [this, Scheme.basicOpen_res]
      exact (inf_eq_right.mpr hf).symm) hf
    refine ⟨_, _, h1, ⟨toSpec p _ ⟨x.1, hxf⟩, ?_⟩, ?_⟩
    · rw [hnat]
      congr 1
      exact Subtype.ext (Scheme.homOfLE_apply _ _)
    · rw [← Spec.map_comp, ← 𝒜.map_comp]
      exact hloc' V hV a _ rfl (hf.trans h)

end GlobalTheory.ThickGlue
end

section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory

theorem irreducibleSpace_of_smooth_of_geometricallyConnected_domain :
    ∀ (R : Type) [CommRing R] [IsDomain R] (G : Over (Spec (CommRingCat.of R))), Smooth G.hom →
      GeometricallyConnected G.hom → Nonempty G.left → IrreducibleSpace G.left := by
  intro R _ _ G hs hc _
  let K := FractionRing R
  let g : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R K))
  let F : Scheme := pullback G.hom g
  have hsnd : Smooth (pullback.snd G.hom g) :=
    MorphismProperty.of_isPullback (P := @Smooth) (IsPullback.of_hasPullback G.hom g) hs
  have hcon : ConnectedSpace F :=
    GeometricallyConnected.geometrically_connectedSpace (f := G.hom) g (pullback.fst _ _)
      (pullback.snd _ _) (IsPullback.of_hasPullback _ _)
  have hirr : IrreducibleSpace F :=
    irreducibleSpace_of_smooth_field_of_connectedSpace K _ (pullback.snd G.hom g) hsnd hcon
  have hgf : Flat g := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat K (nonZeroDivisors R))
  have hG : Flat G.hom := inferInstance

  have hη : genericPoint (Spec (CommRingCat.of R)) ∈ Set.range g :=
    (Flat.generalizingMap g).stableUnderGeneralization_range
      (genericPoint_specializes (g (closedPoint K))) ⟨closedPoint K, rfl⟩
  let ξ : G.left := pullback.fst G.hom g (genericPoint F)
  have hspec : ∀ z : G.left, ξ ⤳ z := by
    intro z
    obtain ⟨z', hz', e⟩ := Flat.generalizingMap G.hom (genericPoint_specializes (G.hom z))
    have hr : z' ∈ Set.range (pullback.fst G.hom g) := by
      rw [Scheme.Pullback.range_fst, Set.mem_preimage, e]; exact hη
    obtain ⟨w, rfl⟩ := hr
    exact ((genericPoint_specializes w).map (pullback.fst G.hom g).continuous).trans hz'
  have hcl : closure ({ξ} : Set G.left) = Set.univ :=
    Set.eq_univ_of_forall fun z => specializes_iff_mem_closure.mp (hspec z)
  rw [irreducibleSpace_def]
  have := (isIrreducible_singleton (x := ξ)).closure
  rw [hcl] at this
  exact this

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace GlobalTheory.SchlessingerAffine

theorem nilKer {A B C D : CommRingCat.{0}} (e : A ≅ B) (g : B ⟶ C) (e' : C ≅ D)
    (h : IsNilpotent (RingHom.ker g.hom)) : IsNilpotent (RingHom.ker (e.hom ≫ g ≫ e'.hom).hom) := by
  have hk : RingHom.ker (e.hom ≫ g ≫ e'.hom).hom = Ideal.map e.inv.hom (RingHom.ker g.hom) := by
    ext x
    have hinj : Function.Injective e'.hom.hom := e'.commRingCatIsoToRingEquiv.injective
    constructor
    · intro hx
      rw [RingHom.mem_ker] at hx
      have hx' : g.hom (e.hom.hom x) = 0 := by
        apply hinj; simpa using hx
      have : x = e.inv.hom (e.hom.hom x) := by
        change x = (e.hom ≫ e.inv).hom x; simp
      rw [this]; exact Ideal.mem_map_of_mem _ hx'
    · intro hx
      rw [RingHom.mem_ker]
      have hle : Ideal.map e.inv.hom (RingHom.ker g.hom) ≤ RingHom.ker (e.hom ≫ g ≫ e'.hom).hom := by
        rw [Ideal.map_le_iff_le_comap]
        intro z hz
        simp only [Ideal.mem_comap, RingHom.mem_ker] at hz ⊢
        change (e'.hom.hom (g.hom ((e.inv ≫ e.hom).hom z))) = 0
        simp [hz]
      exact hle hx
  rw [hk]
  exact h.map (Ideal.mapHom e.inv.hom)

theorem appTop_eq (R S : CommRingCat.{0}) (f : R ⟶ S) :
    (Spec.map f).appTop = (Scheme.ΓSpecIso R).hom ≫ f ≫ (Scheme.ΓSpecIso S).inv := by
  rw [← Category.assoc, ← Scheme.ΓSpecIso_naturality]; simp

theorem inv_comp_appTop (R S : CommRingCat.{0}) (f : R ⟶ S) :
    (Scheme.ΓSpecIso R).inv ≫ (Spec.map f).appTop = f ≫ (Scheme.ΓSpecIso S).inv := by
  rw [appTop_eq]; simp

theorem surjTop {R S : CommRingCat.{0}} (f : R ⟶ S) (h : Function.Surjective f) :
    Function.Surjective (Spec.map f).appTop := by
  rw [appTop_eq]
  have h1 := (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.surjective
  have h2 := (Scheme.ΓSpecIso S).symm.commRingCatIsoToRingEquiv.surjective
  exact (h2.comp h).comp h1

theorem nilTop {R S : CommRingCat.{0}} (f : R ⟶ S) (h : IsNilpotent (RingHom.ker f.hom)) :
    IsNilpotent (RingHom.ker (Spec.map f).appTop.hom) := by
  rw [appTop_eq]
  exact nilKer (Scheme.ΓSpecIso R) f (Scheme.ΓSpecIso S).symm h

theorem pushout_of_eq (X X' S S' : Scheme.{0}) (f : X' ⟶ X) (g : X' ⟶ S') (p : X ⟶ S) (q : S' ⟶ S)
    (h : IsPullback f g p q) [IsAffine S] [IsAffine S'] (W : X.Opens) (hW : IsAffineOpen W)
    (O : X'.Opens) (hO : f ⁻¹ᵁ W = O) :
    IsPushout (p.appLE ⊤ W (fun _ _ => trivial)) q.appTop (f.appLE W O hO.ge)
      (g.appLE ⊤ O (fun _ _ => trivial)) := by
  subst hO
  have := GlobalTheory.AffBaseChange.isPushout_appLE_of_isPullback_of_isAffine X X' S S' f g p q h
    inferInstance inferInstance W hW
  rwa [Scheme.Hom.app_eq_appLE] at this

end GlobalTheory.SchlessingerAffine


open GlobalTheory.SchlessingerAffine in
theorem GlobalTheory.SchlessingerAffine.flat_and_pushouts : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → Function.Surjective g₁ → Function.Surjective g₂ → IsNilpotent (RingHom.ker g₁.hom) → IsNilpotent (RingHom.ker g₂.hom) → ∀ (Y₁ Y₂ Y₀ : Scheme.{0}) (p₁ : Y₁ ⟶ Spec R₁) (p₂ : Y₂ ⟶ Spec R₂) (p₀ : Y₀ ⟶ Spec R₀) (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂), IsPullback i₁ p₀ p₁ (Spec.map g₁) → IsPullback i₂ p₀ p₂ (Spec.map g₂) → Flat p₁ → Flat p₂ → ∀ (Y : Scheme.{0}) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y) (hw : i₁ ≫ j₁ = i₂ ≫ j₂), IsClosedImmersion j₁ → IsClosedImmersion j₂ → (∀ V : Y.Opens, IsPullback (j₁.app V) (j₂.app V) (i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl) (i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (by rw [hw]; exact le_rfl))) → ∀ (y : Y ⟶ Spec P), j₁ ≫ y = p₁ ≫ Spec.map f₁ → j₂ ≫ y = p₂ ≫ Spec.map f₂ → ∀ V : Y.Opens, IsAffineOpen V → (y.appLE ⊤ V (fun _ _ => trivial)).hom.Flat ∧ IsPushout (y.appLE ⊤ V (fun _ _ => trivial)) (Spec.map f₁).appTop (j₁.app V) (p₁.appLE ⊤ (j₁ ⁻¹ᵁ V) (fun _ _ => trivial)) ∧ IsPushout (y.appLE ⊤ V (fun _ _ => trivial)) (Spec.map f₂).appTop (j₂.app V) (p₂.appLE ⊤ (j₂ ⁻¹ᵁ V) (fun _ _ => trivial)) := by
  intro P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hs₁ hs₂ hn₁ hn₂ Y₁ Y₂ Y₀ p₁ p₂ p₀ i₁ i₂ h₁ h₂ hF₁ hF₂ Y j₁ j₂ hw
    hj₁ hj₂ hV y hy₁ hy₂ V hVa
  have hU₁ : IsAffineOpen (j₁ ⁻¹ᵁ V) := hVa.preimage j₁
  have hU₂ : IsAffineOpen (j₂ ⁻¹ᵁ V) := hVa.preimage j₂
  have hPT : IsPullback (Spec.map f₁).appTop (Spec.map f₂).appTop (Spec.map g₁).appTop
      (Spec.map g₂).appTop :=
    IsPullback.of_iso hP (Scheme.ΓSpecIso P).symm (Scheme.ΓSpecIso R₁).symm
      (Scheme.ΓSpecIso R₂).symm (Scheme.ΓSpecIso R₀).symm
      (inv_comp_appTop _ _ f₁).symm (inv_comp_appTop _ _ f₂).symm
      (inv_comp_appTop _ _ g₁).symm (inv_comp_appTop _ _ g₂).symm
  have q₁ := pushout_of_eq Y₁ Y₀ (Spec R₁) (Spec R₀) i₁ p₀ p₁ (Spec.map g₁) h₁ (j₁ ⁻¹ᵁ V) hU₁
    ((i₁ ≫ j₁) ⁻¹ᵁ V) rfl
  have q₂ := pushout_of_eq Y₂ Y₀ (Spec R₂) (Spec R₀) i₂ p₀ p₂ (Spec.map g₂) h₂ (j₂ ⁻¹ᵁ V) hU₂
    ((i₁ ≫ j₁) ⁻¹ᵁ V) (by rw [hw]; rfl)
  have c₁ : y.appLE ⊤ V (fun _ _ => trivial) ≫ j₁.app V =
      (Spec.map f₁).appTop ≫ p₁.appLE ⊤ (j₁ ⁻¹ᵁ V) (fun _ _ => trivial) := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    refine (Scheme.Hom.appLE_comp_appLE j₁ y _ _ _ _ _).trans ?_
    refine Eq.trans ?_ (Scheme.Hom.appLE_comp_appLE p₁ (Spec.map f₁) _ _ _ _ _).symm
    simp only [hy₁]
  have c₂ : y.appLE ⊤ V (fun _ _ => trivial) ≫ j₂.app V =
      (Spec.map f₂).appTop ≫ p₂.appLE ⊤ (j₂ ⁻¹ᵁ V) (fun _ _ => trivial) := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    refine (Scheme.Hom.appLE_comp_appLE j₂ y _ _ _ _ _).trans ?_
    refine Eq.trans ?_ (Scheme.Hom.appLE_comp_appLE p₂ (Spec.map f₂) _ _ _ _ _).symm
    simp only [hy₂]
  exact GlobalTheory.T.schlessinger_flat_fibreProduct _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hPT (surjTop g₁ hs₁) (surjTop g₂ hs₂)
    (nilTop g₁ hn₁) (nilTop g₂ hn₂) q₁ q₂
    (p₁.flat_appLE (isAffineOpen_top _) hU₁ le_top) (p₂.flat_appLE (isAffineOpen_top _) hU₂ le_top)
    (hV V) c₁ c₂
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.closedSubscheme_glue_local_condition : ∀ (S : Scheme.{0}) (Φ : ∀ (T : Scheme.{0}), (T ⟶ S) → Prop), (∀ (T T' : Scheme.{0}) (t : T ⟶ S) (u : T' ⟶ T), Φ T t → Φ T' (u ≫ t)) → (∀ (T : Scheme.{0}) (t : T ⟶ S), (∀ τ : T, ∃ V : T.Opens, τ ∈ V ∧ Φ V (V.ι ≫ t)) → Φ T t) → (∀ x : S, ∃ (U : S.Opens) (Z : Scheme.{0}) (i : Z ⟶ U), x ∈ U ∧ IsClosedImmersion i ∧ ∀ (T : Scheme.{0}) (t : T ⟶ U), Φ T (t ≫ U.ι) ↔ ∃ z : T ⟶ Z, z ≫ i = t) → ∃ (Z : Scheme.{0}) (i : Z ⟶ S), IsClosedImmersion i ∧ ∀ (T : Scheme.{0}) (t : T ⟶ S), Φ T t ↔ ∃ z : T ⟶ Z, z ≫ i = t := by
  first | exact @GlobalTheory.closedSubscheme_glue | exact GlobalTheory.closedSubscheme_glue | (intros; apply GlobalTheory.closedSubscheme_glue <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.irreducibleSpace_of_smooth_over_field_of_connected : ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k)), Smooth f → ConnectedSpace X → IrreducibleSpace X := by
  first | exact @GlobalTheory.irreducibleSpace_of_smooth_field_of_connectedSpace | exact GlobalTheory.irreducibleSpace_of_smooth_field_of_connectedSpace | (intros; apply GlobalTheory.irreducibleSpace_of_smooth_field_of_connectedSpace <;> assumption)
end

section

open Matrix
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.unitaryPQ_continuous_character_eq_det_pow_prod : ∀ (n p q : ℕ) (G s : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin p ⊕ Fin q) ℂ) (B' : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ), B * B' = 1 → B' * B = 1 → Bᴴ * G * B = Matrix.fromBlocks 1 0 0 (-1) → s * B = B * Matrix.fromBlocks 1 0 0 (-1) → ∀ c : Matrix (Fin n) (Fin n) ℂ → ℂ, (∀ k k' : Matrix (Fin n) (Fin n) ℂ, kᴴ * G * k = G → s * k = k * s → k'ᴴ * G * k' = G → s * k' = k' * s → c (k * k') = c k * c k') → (∀ k : Matrix (Fin n) (Fin n) ℂ, kᴴ * G * k = G → s * k = k * s → ‖c k‖ = 1) → ContinuousOn c {k | kᴴ * G * k = G ∧ s * k = k * s} → ∃ x y : ℤ, ∀ k : Matrix (Fin n) (Fin n) ℂ, kᴴ * G * k = G → s * k = k * s → c k = ((1 / 2 : ℂ) • (1 + s) * k + (1 / 2 : ℂ) • (1 - s)).det ^ x * ((1 / 2 : ℂ) • (1 - s) * k + (1 / 2 : ℂ) • (1 + s)).det ^ y := by
  first | exact @GlobalTheory.UpqChar.char_Upq | exact GlobalTheory.UpqChar.char_Upq | (intros; apply GlobalTheory.UpqChar.char_Upq <;> assumption)
end

section

open MeasureTheory

theorem _root_.GlobalTheory.T.translation_character_invariant_form : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (μ : @MeasureTheory.Measure V (borel V)), @MeasureTheory.Measure.IsAddHaarMeasure V _ _ (borel V) μ →
    ∀ (T : SchwartzMap V ℂ →L[ℂ] SchwartzMap V ℂ),
    (∀ (L : V →L[ℝ] ℝ) (f f' g g' : SchwartzMap V ℂ),
      (∀ x, f' x = Complex.exp (Complex.I * (L x : ℂ)) * f x) →
      (∀ x, g' x = Complex.exp (Complex.I * (L x : ℂ)) * g x) →
      @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => T f' x * starRingEnd ℂ (T g' x)) =
        @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => T f x * starRingEnd ℂ (T g x))) →
    ∀ (m f f' g g' : SchwartzMap V ℂ), (∀ x, f' x = m x * f x) → (∀ x, g' x = starRingEnd ℂ (m x) * g x) →
      @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => T f' x * starRingEnd ℂ (T g x)) =
        @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => T f x * starRingEnd ℂ (T g' x)) := by
  first | exact @GlobalTheory.CharMult.multiplier_symm | exact GlobalTheory.CharMult.multiplier_symm | (intros; apply GlobalTheory.CharMult.multiplier_symm <;> assumption)
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.exists_concaveTwist_eta_inequalities : ∀ T : ℝ, 300 ≤ T → ∃ η η1 η2 : ℝ → ℝ, ContDiffOn ℝ ∞ η (Set.Ioi (-1/4)) ∧ (∀ y, -1/4 < y → 0 < η y ∧ HasDerivAt η (η1 y) y ∧ HasDerivAt η1 (η2 y) y) ∧ (∀ y, 0 ≤ y → 0 ≤ η1 y ∧ η1 y ≤ 2 ∧ 2 ≤ η y ∧ η2 y < 0 ∧ η y ≤ 2 + 2 * min y (T + 1) ∧ η y + η1 y ^ 2 / (-η2 y) ≤ 8 * (1 + (min y (T + 1)) ^ 2)) ∧ (∀ y, T - 1 ≤ y → y ≤ T + 1 → 3 / 16 ≤ -η2 y ∧ T ≤ η y) := by
  first | exact @GlobalTheory.concave_twist_exists | exact GlobalTheory.concave_twist_exists | (intros; apply GlobalTheory.concave_twist_exists <;> assumption)
end

section

open FourierTransform MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.mem_closure_gaussian_convolutions : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : SchwartzMap E ℂ),
    f ∈ closure {u : SchwartzMap E ℂ | ∃ (c : ℝ) (s : ℂ), 0 < c ∧
      ∀ y, u y = s * ∫ a, f a * Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ))} := by
  first | exact @GlobalTheory.narrowGauss_convolution_dense | exact GlobalTheory.narrowGauss_convolution_dense | (intros; apply GlobalTheory.narrowGauss_convolution_dense <;> assumption)
end

section

open Module

theorem _root_.GlobalTheory.T.finrank_iInf_ker_semilinear_standardBasis : ∀ (K V ι : Type) [Field K] [AddCommGroup V] [Module ℂ V] [Finite ι] (σ : K →+* ℂ) (N : ℕ) (f : (Fin N → K) →ₛₗ[σ] V), (LinearIndependent ℂ fun k => f (Pi.single k 1)) → Submodule.span ℂ (Set.range f) = ⊤ → ∀ (a : ι → (Fin N → K) →ₗ[K] (Fin N → K)) (a' : ι → V →ₗ[ℂ] V), (∀ i v, a' i (f v) = f (a i v)) → finrank ℂ (⨅ i, LinearMap.ker (a' i) : Submodule ℂ V) = finrank K (⨅ i, LinearMap.ker (a i) : Submodule K (Fin N → K)) := by
  first | exact @GlobalTheory.BadCount.finrank_iInf_ker_semilinear | exact GlobalTheory.BadCount.finrank_iInf_ker_semilinear | (intros; apply GlobalTheory.BadCount.finrank_iInf_ker_semilinear <;> assumption)
end
