module

public import Development.AbelianVarietyTheory.Definitions.RegularCharts.Bundle001
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle010
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsChartFiniteType
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsFlagCoordinatesCellChangeBirational
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle007
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsNoetherianRingTensor
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle003
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem _root_.GlobalTheory.T.isEigenvector_iff_lieBasis_coordinates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (R : Type) [CommRing R] [Algebra c.F R] (f : Γ(Y.X, M.U) →+* R) (x : Sp R ⟶ Xo.X) (Λ : M.Lift f x), ∀ (τ : E →+* ℂ) (cv : Fin M.n → R) (w : Sp (DualNumber R) ⟶ Xo.univ.t.G.left), Λ.Vec cv w → (IsEigAt c τ w ↔ M.Eig f τ cv) := by
  first | exact @GlobalTheory.Reg.isEigAt_iff_eig | exact GlobalTheory.Reg.isEigAt_iff_eig | (intros; apply GlobalTheory.Reg.isEigAt_iff_eig <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem _root_.GlobalTheory.T.lieBasis_coordinates_bijective_tangent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (R : Type) [CommRing R] [Algebra c.F R] (f : Γ(Y.X, M.U) →+* R) (x : Sp R ⟶ Xo.X) (Λ : M.Lift f x), (∀ cv, ∃! w, Λ.Vec cv w) ∧ (∀ cv w, Λ.Vec cv w → IsTanAt x w) ∧ ∀ w, IsTanAt x w → ∃! cv, Λ.Vec cv w := by
  first | exact @GlobalTheory.Reg.vec_bijective | exact GlobalTheory.Reg.vec_bijective | (intros; apply GlobalTheory.Reg.vec_bijective <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.Reg.ChartOpens

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem away_irreducible {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] {ϖ : O} (hϖ : Irreducible ϖ) : IsLocalization.Away ϖ K := by
  have hi := IsFractionRing.injective O K
  refine IsLocalization.Away.mk _ (IsUnit.mk0 _ (by simpa using hϖ.ne_zero)) (fun z => ?_)
    (fun a b h => ⟨0, by rw [hi h]⟩)
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) z
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero hb) hϖ
  refine ⟨n, a * ↑u⁻¹, ?_⟩
  have h1 : algebraMap O K ϖ ≠ 0 := by simpa using hϖ.ne_zero
  have h2 : algebraMap O K u * algebraMap O K ↑u⁻¹ = 1 := by rw [← map_mul]; simp
  have h3 : algebraMap O K u ≠ 0 := left_ne_zero_of_mul_eq_one h2
  rw [map_mul, map_mul, map_pow, eq_inv_of_mul_eq_one_right h2]
  field_simp

theorem exists_finset_basicOpen {A : Type} [CommRing A] [IsNoetherianRing A] (V : Set (PrimeSpectrum A))
    (hV : IsOpen V) (hne : V.Nonempty) :
    ∃ es : Finset A, es.Nonempty ∧ (∀ e ∈ es, e ≠ 0) ∧ ∀ p, p ∈ V ↔ ∃ e ∈ es, e ∉ p.asIdeal := by
  classical
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).1 hV.isClosed_compl
  obtain ⟨s, rfl⟩ := IsNoetherian.noetherian I
  have key : ∀ p, p ∈ V ↔ ∃ e ∈ s.filter (· ≠ 0), e ∉ p.asIdeal := by
    intro p
    have : p ∉ V ↔ (s : Set A) ⊆ p.asIdeal := by
      rw [← Set.mem_compl_iff, hI]
      exact (PrimeSpectrum.mem_zeroLocus _ _).trans Ideal.span_le
    constructor
    · intro hp
      obtain ⟨e, he, h⟩ := Set.not_subset.1 (fun h => this.2 h hp)
      exact ⟨e, Finset.mem_filter.2 ⟨he, fun h0 => h (h0 ▸ p.asIdeal.zero_mem)⟩, h⟩
    · rintro ⟨e, he, h⟩
      by_contra hp
      exact h (this.1 hp (Finset.mem_filter.1 he).1)
  obtain ⟨p, hp⟩ := hne
  obtain ⟨e, he, -⟩ := (key p).1 hp
  exact ⟨_, ⟨e, he⟩, fun e he => (Finset.mem_filter.1 he).2, key⟩

theorem isOpenImmersion_of_surj {O K A R : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
    [Algebra O K] [IsFractionRing O K] [CommRing A] [CommRing R] [Algebra K R] (α : O →+* A) (f : A →+* R)
    (hf : f.comp α = (algebraMap K R).comp (algebraMap O K)) (x : A) (hx : IsUnit (f x)) (hi : Function.Injective f)
    (hs : ∀ r : R, ∃ (a : A) (k : K) (N : ℕ), r * f x ^ N = algebraMap K R k * f a) :
    IsOpenImmersion (spMap f) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have := away_irreducible (K := K) hϖ
  have hfo : ∀ o, f (α o) = algebraMap K R (algebraMap O K o) := fun o => RingHom.congr_fun hf o
  letI := f.toAlgebra
  have : IsLocalization.Away (α ϖ * x) R := by
    refine IsLocalization.Away.mk _ ?_ (fun r => ?_) (fun a b h => ⟨0, by rw [hi h]⟩)
    · show IsUnit (f _)
      rw [map_mul, hfo]
      exact ((IsLocalization.Away.algebraMap_isUnit (S := K) ϖ).map _).mul hx
    · obtain ⟨a, k, N, h⟩ := hs r
      obtain ⟨n, o, ho⟩ := IsLocalization.Away.surj ϖ k
      refine ⟨N + n, α (o * ϖ ^ N) * x ^ n * a, ?_⟩
      show r * f _ ^ _ = f _
      have h2 : algebraMap K R k * f (α ϖ) ^ n = f (α o) := by
        rw [hfo, hfo, ← ho, map_mul, map_pow]
      simp only [map_mul, map_pow]
      rw [← h2]
      linear_combination (f (α ϖ) ^ (N + n) * f x ^ n) * h
  exact IsOpenImmersion.of_isLocalization (α ϖ * x)

theorem chart_opens {O K A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
    [Algebra O K] [IsFractionRing O K] [CommRing A] [IsDomain A] {X Z : Scheme.{0}} (s : X ⟶ Sp O) [Flat s]
    (g : Sp A ⟶ X) [IsOpenImmersion g] (α : O →+* A) (hα : g ≫ s = spMap α) (hft : α.FiniteType)
    (t : Z ⟶ Sp K) [Smooth t] (jQ : Z ⟶ pullback s (spMap (algebraMap O K))) [IsOpenImmersion jQ]
    (hd : Dense (Set.range jQ)) (hj : jQ ≫ pullback.snd _ _ = t) :
    ∃ es : Finset A, Function.Injective α ∧ es.Nonempty ∧ (∀ e ∈ es, e ≠ 0) ∧
      (∀ e ∈ es, ∀ (R : Type) [CommRing R] [Algebra K R] (f : A →+* R),
        f.comp α = (algebraMap K R).comp (algebraMap O K) → IsUnit (f e) →
          (∃ xF : Sp R ⟶ Z, xF ≫ t = spMap (algebraMap K R) ∧ xF ≫ jQ ≫ pullback.fst _ _ = spMap f ≫ g) ∧
          ∀ d : A, Function.Injective f → IsUnit (f d) →
            (∀ r : R, ∃ (a : A) (k : K) (N : ℕ), r * f (e * d) ^ N = algebraMap K R k * f a) → Algebra.Smooth K R) ∧
      ∀ (L : Type) [Field L] [Algebra K L] (f : A →+* L) (xF : Sp L ⟶ Z), xF ≫ t = spMap (algebraMap K L) →
        xF ≫ jQ ≫ pullback.fst _ _ = spMap f ≫ g →
          f.comp α = (algebraMap K L).comp (algebraMap O K) ∧ ∃ e ∈ es, f e ≠ 0 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have := away_irreducible (K := K) hϖ
  have hopen : IsOpenImmersion (spMap (algebraMap O K)) := IsOpenImmersion.of_isLocalization ϖ
  have hjs : (jQ ≫ pullback.fst _ _) ≫ s = t ≫ spMap (algebraMap O K) := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hj]
  have hflat : α.Flat := (HasRingHomProperty.Spec_iff (P := @Flat) (φ := CommRingCat.ofHom α)).1 (by
    show Flat (spMap α)
    rw [← hα]; infer_instance)
  have hinj : Function.Injective α := by
    letI := α.toAlgebra
    have : Module.Flat O A := hflat
    exact FaithfulSMul.algebraMap_injective O A
  have hN : IsNoetherianRing A := by
    letI := α.toAlgebra
    have : Algebra.FiniteType O A := hft
    exact Algebra.FiniteType.isNoetherianRing O A
  let j := jQ ≫ pullback.fst s (spMap (algebraMap O K))
  let V : Set (PrimeSpectrum A) := g ⁻¹' Set.range j
  have hV : IsOpen V := j.isOpenEmbedding.isOpen_range.preimage g.continuous
  have hne : V.Nonempty := by
    have h0 : g (⊥ : PrimeSpectrum A) ∈ Set.range (pullback.fst s (spMap (algebraMap O K))) := by
      rw [Scheme.Pullback.range_fst]
      refine ⟨(⊥ : PrimeSpectrum K), ?_⟩
      refine Eq.trans ?_ (Scheme.Hom.comp_apply g s _)
      rw [hα]
      refine PrimeSpectrum.ext ?_
      show Ideal.comap (algebraMap O K) ⊥ = Ideal.comap α ⊥
      rw [Ideal.comap_bot_of_injective _ hinj, Ideal.comap_bot_of_injective _ (IsFractionRing.injective O K)]
    obtain ⟨y, hy⟩ := h0
    obtain ⟨_, ⟨p, hp⟩, z, rfl⟩ := hd.inter_open_nonempty
      (pullback.fst s (spMap (algebraMap O K)) ⁻¹' Set.range g)
      (g.isOpenEmbedding.isOpen_range.preimage (Scheme.Hom.continuous _)) ⟨y, _, hy.symm⟩
    exact ⟨p, z, by rw [hp]; exact Scheme.Hom.comp_apply _ _ _⟩
  obtain ⟨es, h1, h2, h3⟩ := exists_finset_basicOpen V hV hne
  refine ⟨es, hinj, h1, h2, fun e he R _ _ f hf hu => ?_, fun L _ _ f xF hx1 hx2 => ⟨?_, ?_⟩⟩
  · have hr : Set.range (spMap f ≫ g) ⊆ Set.range j := by
      rintro _ ⟨p, rfl⟩
      rw [Scheme.Hom.comp_apply]
      refine (h3 (spMap f p)).2 ⟨e, he, fun h => ?_⟩
      exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ (show f e ∈ p.asIdeal from h) hu)
    let xF := IsOpenImmersion.lift j (spMap f ≫ g) hr
    have hx : xF ≫ j = spMap f ≫ g := IsOpenImmersion.lift_fac _ _ _
    have ht : xF ≫ t = spMap (algebraMap K R) := by
      rw [← cancel_mono (spMap (algebraMap O K)), Category.assoc, ← hjs, ← Category.assoc, hx, Category.assoc, hα,
        ← spMap_comp, ← spMap_comp, hf]
    refine ⟨⟨xF, ht, hx⟩, fun d hi hdu hs => ?_⟩
    have := isOpenImmersion_of_surj α f hf (e * d) (by rw [map_mul]; exact hu.mul hdu) hi hs
    have : IsOpenImmersion (xF ≫ j) := by rw [hx]; infer_instance
    have : IsOpenImmersion xF := IsOpenImmersion.of_comp xF j
    have : Smooth (spMap (algebraMap K R)) := by rw [← ht]; infer_instance
    exact RingHom.smooth_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @Smooth)).1 this)
  · have : spMap (f.comp α) = spMap ((algebraMap K L).comp (algebraMap O K)) := by
      rw [spMap_comp, spMap_comp, ← hα, ← Category.assoc, ← hx2, ← hx1, Category.assoc, hjs, Category.assoc]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective this)
  · obtain ⟨e, he, h⟩ := (h3 (spMap f (⊥ : PrimeSpectrum L))).1
      ⟨xF (⊥ : PrimeSpectrum L), (Scheme.Hom.comp_apply xF j _).symm.trans
        ((congrArg (fun φ : Sp L ⟶ X => φ (⊥ : PrimeSpectrum L)) hx2).trans (Scheme.Hom.comp_apply _ _ _))⟩
    exact ⟨e, he, fun h0 => h (show f e ∈ (⊥ : Ideal L) from h0)⟩

theorem moduli_basicOpens :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O c.F] [IsFractionRing O c.F] (Y : Model Xo c (algebraMap O c.F)) (M : MChart Y), ∃ (α : O →+* Γ(Y.X, M.U)) (es : Finset Γ(Y.X, M.U)), M.hU.fromSpec ≫ Y.s = spMap α ∧ α.FiniteType ∧ Function.Injective α ∧ es.Nonempty ∧ (∀ e ∈ es, e ≠ 0) ∧ (∀ e ∈ es, ∀ (R : Type) [CommRing R] [Algebra c.F R] (f : Γ(Y.X, M.U) →+* R), f.comp α = (algebraMap c.F R).comp (algebraMap O c.F) → IsUnit (f e) → (∃ xF : Sp R ⟶ Xo.XF c, xF ≫ pullback.snd _ _ = spMap (algebraMap c.F R) ∧ xF ≫ Y.j = spMap f ≫ M.hU.fromSpec) ∧ ∀ d : Γ(Y.X, M.U), Function.Injective f → IsUnit (f d) → (∀ r : R, ∃ (a : Γ(Y.X, M.U)) (k : c.F) (N : ℕ), r * f (e * d) ^ N = algebraMap c.F R k * f a) → Algebra.Smooth c.F R) ∧ ∀ (L : Type) [Field L] [Algebra c.F L] (f : Γ(Y.X, M.U) →+* L) (xF : Sp L ⟶ Xo.XF c), xF ≫ pullback.snd _ _ = spMap (algebraMap c.F L) → xF ≫ Y.j = spMap f ≫ M.hU.fromSpec → f.comp α = (algebraMap c.F L).comp (algebraMap O c.F) ∧ ∃ e ∈ es, f e ≠ 0 := by
  intro E _ _ _ H Dw l Xo c O _ _ _ _ _ Y M
  obtain ⟨α, h1, h2, -⟩ := (GlobalTheory.ModelPoints.model_points_charts E H Dw l Xo c O _ Y).2.2 M.U M.hU
  have := M.dom
  have := Y.flat
  have := Y.jQ_open
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim Xo.s
  have hg : IsOpenImmersion (X := Sp Γ(Y.X, M.U)) M.hU.fromSpec := inferInstanceAs (IsOpenImmersion M.hU.fromSpec)
  obtain ⟨es, h⟩ := chart_opens (A := Γ(Y.X, M.U)) Y.s M.hU.fromSpec α h1 h2
    (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) Y.jQ Y.jQ_dense Y.jQ_over
  exact ⟨α, es, h1, h2, h⟩

end GlobalTheory.Reg.ChartOpens
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem _root_.GlobalTheory.T.exists_flagCoordinates_cellChange_birational : ∀ (κ T : Type) [Field κ] [Infinite κ] [Finite T] (r : T → ℕ) (G : ∀ τ, Matrix (Fin (r τ)) (Fin (r τ)) κ) (σ : ∀ τ, Equiv.Perm (Fin (r τ))), (∀ τ, IsUnit (G τ).det) → ∃ (e : FractionRing (MvPolynomial (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) κ) ≃ₐ[κ] FractionRing (MvPolynomial (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) κ)) (b : ∀ τ, Matrix (Fin (r τ)) (Fin (r τ)) (FractionRing (MvPolynomial (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) κ))), (∀ τ, (b τ).BlockTriangular id ∧ ∀ i, b τ i i ≠ 0) ∧ ∀ τ, (G τ).map (algebraMap κ _) * lowM (fun v => algebraMap (MvPolynomial _ κ) _ (MvPolynomial.X v)) τ = (lowM (fun v => e (algebraMap (MvPolynomial _ κ) _ (MvPolynomial.X v))) τ).submatrix (σ τ).symm id * b τ := by
  first | exact @GlobalTheory.Reg.cell_change_birational | exact GlobalTheory.Reg.cell_change_birational | (intros; apply GlobalTheory.Reg.cell_change_birational <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg

theorem exists_extend_of_pow_denom {R A L : Type} [CommRing R] [CommRing A] [IsDomain A] [Field L]
    (β : R →+* FractionRing A) (d : A)
    (h : ∀ r, ∃ (x : A) (t : ℕ), β r * algebraMap A _ (d ^ t) = algebraMap A _ x)
    (φ : A →+* L) (hd : φ d ≠ 0) :
    ∃ ψ : R →+* L, ∀ (r : R) (x s : A),
      β r * algebraMap A _ s = algebraMap A _ x → ψ r * φ s = φ x := by
  choose X T hXT using h
  have hp : ∀ t : ℕ, φ (d ^ t) ≠ 0 := fun t => by rw [map_pow]; exact pow_ne_zero _ hd
  have key : ∀ (r : R) (x s : A), β r * algebraMap A _ s = algebraMap A _ x →
      φ (X r) / φ (d ^ T r) * φ s = φ x := by
    intro r x s hx
    have h1 : X r * s = x * d ^ T r := by
      apply IsFractionRing.injective A (FractionRing A)
      rw [map_mul, map_mul, ← hXT r, ← hx]; ring
    have h2 := congrArg φ h1
    rw [map_mul, map_mul] at h2
    rw [div_mul_eq_mul_div, h2, mul_div_assoc, div_self (hp _), _root_.mul_one]
  refine ⟨{ toFun := fun r => φ (X r) / φ (d ^ T r), map_one' := ?_, map_mul' := ?_,
            map_zero' := ?_, map_add' := ?_ }, key⟩
  · have := key 1 1 1 (by simp)
    simpa using this
  · intro r s
    have := key (r * s) (X r * X s) (d ^ T r * d ^ T s) (by
      rw [map_mul, map_mul, map_mul, ← hXT r, ← hXT s]; ring)
    rw [map_mul, map_mul] at this
    rw [div_mul_div_comm, eq_div_iff (mul_ne_zero (hp _) (hp _))]
    exact this
  · have := key 0 0 1 (by simp)
    simpa using this
  · intro r s
    have := key (r + s) (X r * d ^ T s + d ^ T r * X s) (d ^ T r * d ^ T s) (by
      rw [map_add (f := _), map_add (f := _), map_mul, map_mul, map_mul, ← hXT r, ← hXT s]; ring)
    rw [map_add (f := _), map_mul, map_mul, map_mul] at this
    rw [div_add_div _ _ (hp _) (hp _), eq_div_iff (mul_ne_zero (hp _) (hp _))]
    exact this

theorem openChart_regular_away :
    ∀ (K Ω O A : Type) [Field K] [Field Ω] [Algebra K Ω] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing A] [IsDomain A] [Algebra O A] (io : K →+* FractionRing O) (gens : Finset Ω) (e : Ω) (α : Ω →+* FractionRing A) (eb : A) (ϖ : O), Irreducible ϖ → e ≠ 0 → algebraMap A (FractionRing A) eb = α e → (∀ (k : K) (a b : O), io k * algebraMap O _ b = algebraMap O _ a → α (algebraMap K Ω k) * algebraMap A _ (algebraMap O A b) = algebraMap A _ (algebraMap O A a)) → (∀ g ∈ gens, α g ∈ Set.range (algebraMap A (FractionRing A))) → (∀ r ∈ Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)), ∃ (x : A) (t : ℕ), α r * algebraMap A _ ((algebraMap O A ϖ * eb) ^ t) = algebraMap A _ x) ∧ ∀ (L : Type) [Field L] (φ : A →+* L), φ (algebraMap O A ϖ * eb) ≠ 0 → ∃ ψ : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)) →+* L, ∀ (r : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω))) (x s : A), α r * algebraMap A _ s = algebraMap A _ x → ψ r * φ s = φ x := by
  intro K Ω O A _ _ _ _ _ _ _ _ _ io gens e α eb ϖ hϖ he heb hk hg
  have h1 : ∀ r ∈ Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)), ∃ (x : A) (t : ℕ),
      α r * algebraMap A _ ((algebraMap O A ϖ * eb) ^ t) = algebraMap A _ x := by
    intro r hr
    induction hr using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with rfl | hx
      · refine ⟨algebraMap O A ϖ, 1, ?_⟩
        rw [pow_one, map_mul, heb, _root_.mul_comm _ (α e), ← _root_.mul_assoc, ← map_mul, inv_mul_cancel₀ he,
          map_one, _root_.one_mul]
      · obtain ⟨y, hy⟩ := hg x hx
        exact ⟨y, 0, by simp [hy]⟩
    | algebraMap k =>
      obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := O) (io k)
      have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
      obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hb0 hϖ
      have hb1 : algebraMap O (FractionRing O) b ≠ 0 := by simpa using hb0
      have := hk k (a * u) (ϖ ^ n) (by
        rw [← hu, ← hab, map_mul, map_mul, ← _root_.mul_assoc, div_mul_cancel₀ _ hb1])
      refine ⟨algebraMap O A (a * u) * eb ^ n, n, ?_⟩
      rw [mul_pow, ← map_pow, map_mul, ← _root_.mul_assoc, this, ← map_mul]
    | add x y _ _ ihx ihy =>
      obtain ⟨a, s, ha⟩ := ihx
      obtain ⟨b, t, hb⟩ := ihy
      refine ⟨a * (algebraMap O A ϖ * eb) ^ t + b * (algebraMap O A ϖ * eb) ^ s, s + t, ?_⟩
      generalize algebraMap O A ϖ * eb = d at *
      rw [pow_add, map_add (f := _), map_add (f := _), map_mul, map_mul, map_mul, ← ha, ← hb]; ring
    | mul x y _ _ ihx ihy =>
      obtain ⟨a, s, ha⟩ := ihx
      obtain ⟨b, t, hb⟩ := ihy
      refine ⟨a * b, s + t, ?_⟩
      generalize algebraMap O A ϖ * eb = d at *
      rw [pow_add, map_mul, map_mul, map_mul, ← ha, ← hb]; ring
  refine ⟨h1, fun L _ φ hφ => ?_⟩
  exact exists_extend_of_pow_denom
    (α.comp (Algebra.adjoin K (insert e⁻¹ (gens : Set Ω))).val.toRingHom) _
    (fun r => h1 r r.2) φ hφ

end GlobalTheory.Reg
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory

theorem exists_mul_eq_of_subfield_closure_eq_top {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
    {t : Set Ω} (ht : Subfield.closure (Set.range (algebraMap K Ω) ∪ t) = ⊤)
    (R : Subalgebra K Ω) (hR : t ⊆ R) (x : Ω) : ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ x * b = a := by
  haveI : IsFractionRing R.toSubring Ω := isFractionRing_subring_of_closure_eq_top ht R.toSubring
    (Set.union_subset (by rintro _ ⟨a, rfl⟩; exact R.algebraMap_mem a) hR)
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R.toSubring) x
  have hb0 : (b : Ω) ≠ 0 := fun h => nonZeroDivisors.ne_zero hb (Subtype.ext h)
  exact ⟨a, a.2, b, b.2, hb0, div_mul_cancel₀ _ hb0⟩

theorem exists_normal_charts_over_dvr :
    ∀ (K Ω O : Type) [Field K] [Field Ω] [Algebra K Ω] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (io : K →+* FractionRing O) (gens es : Finset Ω), Subfield.closure (Set.range (algebraMap K Ω) ∪ (gens : Set Ω)) = ⊤ → (∀ e ∈ es, e ≠ 0 ∧ e ∈ Subring.closure ((algebraMap K Ω '' {a | io a ∈ Set.range (algebraMap O (FractionRing O))}) ∪ (gens : Set Ω))) → (∀ e ∈ es, Algebra.Smooth K (Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)))) → ∃ (J : Type) (_ : Finite J) (A : J → Type) (_ : ∀ j, CommRing (A j)) (_ : ∀ j, IsDomain (A j)) (_ : ∀ j, Algebra O (A j)) (α : ∀ j, Ω →+* FractionRing (A j)), (∀ j, Algebra.FiniteType O (A j) ∧ Module.Flat O (A j) ∧ IsIntegrallyClosed (A j)) ∧ (∀ j (k : K) (a b : O), io k * algebraMap O _ b = algebraMap O _ a → α j (algebraMap K Ω k) * algebraMap (A j) _ (algebraMap O (A j) b) = algebraMap (A j) _ (algebraMap O (A j) a)) ∧ (∀ j, ∀ g ∈ gens, α j g ∈ Set.range (algebraMap (A j) (FractionRing (A j)))) ∧ ∀ e ∈ es, ∀ (L : Type) [Field L] (W : ValuationSubring L) (χ : FractionRing O →+* L) (ψ : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)) →+* L), (∀ k : K, ψ (algebraMap K _ k) = χ (io k)) → (∀ a : O, χ (algebraMap O _ a) ∈ W) → (∀ g : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)), (g : Ω) ∈ gens → ψ g ∈ W) → ∃ (j : J) (φ : A j →+* L), (∀ x, φ x ∈ W) ∧ (∀ a : O, φ (algebraMap O (A j) a) = χ (algebraMap O _ a)) ∧ ∀ (r : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω))) (x s : A j), α j r * algebraMap (A j) _ s = algebraMap (A j) _ x → ψ r * φ s = φ x := by
  classical
  intro K Ω O _ _ _ _ _ _ _ io gens es hgen _ hsm
  letI : Algebra K (FractionRing O) := io.toAlgebra
  obtain ⟨J, hJ, Ω', hΩ', α, gm, hαgm, htop, hR⟩ :=
    GlobalTheory.BaseChangeComponents.components K (FractionRing O) Ω (Algebra.adjoin K (gens : Set Ω))
      (Subalgebra.fg_adjoin_finset gens)
      (exists_mul_eq_of_subfield_closure_eq_top hgen _ Algebra.subset_adjoin)
  have hαgm' : ∀ j (k : K), α j (algebraMap K Ω k) = gm j (io k) := hαgm
  letI : ∀ j, Algebra O (Ω' j) := fun j => ((gm j).comp (algebraMap O (FractionRing O))).toAlgebra
  have hO : ∀ j (a : O), algebraMap O (Ω' j) a = gm j (algebraMap O (FractionRing O) a) :=
    fun _ _ => rfl
  have hinj : ∀ j, Function.Injective (algebraMap O (Ω' j)) := fun j =>
    (gm j).injective.comp (IsFractionRing.injective O (FractionRing O))
  have hcl : ∀ j, Subfield.closure (Set.range (algebraMap O (Ω' j)) ∪
      ((gens.image (α j) : Finset (Ω' j)) : Set (Ω' j))) = ⊤ := by
    intro j
    set E := Subfield.closure (Set.range (algebraMap O (Ω' j)) ∪
      ((gens.image (α j) : Finset (Ω' j)) : Set (Ω' j))) with hE
    have hgm : ∀ a, gm j a ∈ E := by
      intro a
      obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (A := O) a
      rw [map_div₀, ← hO, ← hO]
      exact div_mem (Subfield.subset_closure (Or.inl ⟨x, rfl⟩))
        (Subfield.subset_closure (Or.inl ⟨y, rfl⟩))
    have hα : (⊤ : Subfield Ω) ≤ E.comap (α j) := by
      rw [← hgen, Subfield.closure_le]
      rintro x (⟨k, rfl⟩ | hx)
      · change α j _ ∈ E
        rw [hαgm']; exact hgm _
      · change α j _ ∈ E
        exact Subfield.subset_closure (Or.inr (by
          rw [Finset.coe_image]; exact ⟨x, hx, rfl⟩))
    rw [eq_top_iff, ← htop j, Subfield.closure_le]
    rintro x (⟨y, rfl⟩ | ⟨y, rfl⟩)
    · exact hα (Subfield.mem_top y)
    · exact hgm y
  choose A hsA hft hfl hic hfr hmin hW using fun j =>
    GlobalTheory.exists_normalisation_adjoin_finset_dvr O (Ω' j) (hinj j) (gens.image (α j)) (hcl j)
  let ε : ∀ j, Ω' j ≃ₐ[A j] FractionRing (A j) := fun j =>
    (FractionRing.algEquiv (A j) (Ω' j)).symm
  have hε : ∀ j (x : A j), algebraMap (A j) (FractionRing (A j)) x = ε j (x : Ω' j) :=
    fun j x => ((ε j).commutes x).symm
  refine ⟨J, hJ, fun j => A j, inferInstance, inferInstance, inferInstance,
    fun j => ((ε j).toRingEquiv.toRingHom).comp (α j),
    fun j => ⟨hft j, hfl j, hic j⟩, ?_, ?_, ?_⟩
  · intro j k a b h
    rw [hε, hε]
    change ε j (α j _) * ε j (algebraMap O (Ω' j) b) = ε j (algebraMap O (Ω' j) a)
    rw [← map_mul, hαgm', hO, hO, ← map_mul, h]
  · intro j g hg
    refine ⟨⟨α j g, hsA j (by rw [Finset.coe_image]; exact ⟨g, hg, rfl⟩)⟩, ?_⟩
    rw [hε]; rfl
  · intro e he L _ W χ ψ hψ hχ hg
    have hsub : (gens : Set Ω) ⊆ Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)) :=
      (Set.subset_insert _ _).trans Algebra.subset_adjoin
    obtain ⟨hD, hφ⟩ := hR (Algebra.adjoin K (insert e⁻¹ (gens : Set Ω))) (hsm e he)
      (exists_mul_eq_of_subfield_closure_eq_top hgen _ hsub)
    obtain ⟨j, φ, h1, h2⟩ := hφ L χ ψ hψ
    have hgmD : ∀ a, gm j a ∈ Subring.closure (α j '' (Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)) : Set Ω) ∪ Set.range (gm j)) :=
      fun a => Subring.subset_closure (Or.inr ⟨a, rfl⟩)
    have hαD : ∀ r : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)), α j r ∈ Subring.closure (α j '' (Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)) : Set Ω) ∪ Set.range (gm j)) :=
      fun r => Subring.subset_closure (Or.inl ⟨r, r.2, rfl⟩)
    have hAD := hmin j _ (hD j) (fun a => hgmD _) (by
      rw [Finset.coe_image]
      rintro _ ⟨g, hg, rfl⟩
      exact hαD ⟨g, hsub hg⟩)
    let inc : A j →+* Subring.closure (α j '' (Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)) : Set Ω) ∪ Set.range (gm j)) :=
      ((A j).val : A j →+* Ω' j).codRestrict _ fun x => hAD x.2
    have hφO : ∀ a : O, (φ.comp inc) (algebraMap O (A j) a) = χ (algebraMap O _ a) :=
      fun a => h2 _ (hgmD _)
    refine ⟨j, φ.comp inc, hW j L W (φ.comp inc) (fun a => by rw [hφO]; exact hχ a) ?_, hφO, ?_⟩
    · intro x hx
      obtain ⟨g, hg', hgx⟩ := Finset.mem_image.mp hx
      have : inc x = ⟨α j (⟨g, hsub hg'⟩ : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω))), hαD _⟩ :=
        Subtype.ext hgx.symm
      rw [RingHom.comp_apply, this, h1]
      exact hg _ hg'
    · intro r x s h
      rw [hε, hε] at h
      have h' : α j r * (s : Ω' j) = x := (ε j).injective (by rw [map_mul]; exact h)
      rw [← h1 r (hαD r), RingHom.comp_apply, RingHom.comp_apply, ← map_mul]
      exact congrArg φ (Subtype.ext h')

end GlobalTheory
end
