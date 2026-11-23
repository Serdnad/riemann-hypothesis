module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealEqBotOfFlatQuotientOfMapMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineHomOfFlatQuotientOfAffineKernel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.PowerSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle010
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.TensorProduct.Basic
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle011
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
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
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteAlgebraLocalCompletion
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

universe u


open TensorProduct in
theorem ringHom_formallyUnramified_of_comp_faithfullyFlat {A B C : Type*} [CommRing A]
    [CommRing B] [CommRing C] {φ : A →+* B} {β : B →+* C} (hβ : β.FaithfullyFlat)
    (hs : β.FormallySmooth) (hu : β.FormallyUnramified) (h : (β.comp φ).FormallyUnramified) :
    φ.FormallyUnramified := by
  algebraize [φ, β, β.comp φ]
  have : Algebra.FormallyEtale B C :=
    Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr ⟨hu, hs⟩
  have h1 : Subsingleton (C ⊗[B] Ω[B⁄A]) :=
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale A B C).subsingleton
  exact ⟨(Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right B C).mp h1⟩

theorem faithfullyFlat_stalkMap_of_flat {W X : Scheme.{u}} (g : W ⟶ X) [Flat g] (w : W) :
    (g.stalkMap w).hom.FaithfullyFlat := by
  have h := Flat.stalkMap g w
  algebraize [(g.stalkMap w).hom]
  have : IsLocalHom (algebraMap (X.presheaf.stalk (g w)) (W.presheaf.stalk w)) :=
    inferInstanceAs <| IsLocalHom (g.stalkMap w).hom
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

theorem flat_of_comp_of_flat_of_surjective {W X Y : Scheme.{u}} (g : W ⟶ X) (u : X ⟶ Y)
    [Flat g] [Surjective g] [Flat (g ≫ u)] : Flat u := by
  refine Flat.of_stalkMap u fun x => ?_
  obtain ⟨w, rfl⟩ := g.surjective x
  have h := Flat.stalkMap (g ≫ u) w
  rw [Scheme.Hom.stalkMap_comp] at h
  exact ringHom_flat_of_comp_faithfullyFlat (faithfullyFlat_stalkMap_of_flat g w) h

theorem formallyUnramified_of_comp_of_etale_of_surjective {W X Y : Scheme.{u}} (g : W ⟶ X)
    (u : X ⟶ Y) [Etale g] [Surjective g] [FormallyUnramified (g ≫ u)] :
    FormallyUnramified u := by
  have : Flat g := (Etale.iff_flat_and_formallyUnramified.mp ‹Etale g›).1
  refine HasRingHomProperty.of_stalkMap RingHom.FormallyUnramified.ofLocalizationPrime fun x => ?_
  obtain ⟨w, rfl⟩ := g.surjective x
  have h := FormallyUnramified.stalkMap (g ≫ u) w
  rw [Scheme.Hom.stalkMap_comp] at h
  have hs : (g.stalkMap w).hom.FormallySmooth :=
    Scheme.Hom.mem_smoothLocus.mp (g.smoothLocus_eq_top.ge (Set.mem_univ w))
  exact ringHom_formallyUnramified_of_comp_faithfullyFlat (faithfullyFlat_stalkMap_of_flat g w)
    hs (FormallyUnramified.stalkMap g w) h

theorem etale_of_comp_of_etale_of_surjective {W X Y : Scheme.{u}} (g : W ⟶ X)
    (u : X ⟶ Y) [Etale g] [Surjective g] [Etale (g ≫ u)] [LocallyOfFinitePresentation u] :
    Etale u := by
  have : Flat g := (Etale.iff_flat_and_formallyUnramified.mp ‹Etale g›).1
  have : Flat (g ≫ u) := (Etale.iff_flat_and_formallyUnramified.mp ‹Etale (g ≫ u)›).1
  have := flat_of_comp_of_flat_of_surjective g u
  have := formallyUnramified_of_comp_of_etale_of_surjective g u
  exact Etale.of_formallyUnramified_of_flat u

theorem exists_opens_range_etale_of_comp :
    ∀ (W X Y : Scheme.{0}) (g : W ⟶ X) (u : X ⟶ Y) [Etale g] [Etale (g ≫ u)]
      [LocallyOfFinitePresentation u],
      ∃ V : X.Opens, (V : Set X) = Set.range g ∧ Etale (V.ι ≫ u) := by
  intro W X Y g u _ _ _
  have : Flat g := (Etale.iff_flat_and_formallyUnramified.mp ‹Etale g›).1
  let V : X.Opens := ⟨Set.range g, g.isOpenMap.isOpen_range⟩
  refine ⟨V, rfl, ?_⟩
  have hr : Set.range g ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]; exact subset_rfl
  let g' : W ⟶ V := IsOpenImmersion.lift V.ι g hr
  have hg' : g' ≫ V.ι = g := IsOpenImmersion.lift_fac _ _ _
  have : Etale (g' ≫ V.ι) := by rw [hg']; infer_instance
  have : Etale g' := Etale.of_comp g' V.ι
  have : Surjective g' := by
    refine ⟨fun v => ?_⟩
    obtain ⟨w, hw⟩ : V.ι v ∈ Set.range g := v.2
    refine ⟨w, V.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hg', hw]
  have : Etale (g' ≫ V.ι ≫ u) := by rw [← Category.assoc, hg']; infer_instance
  exact etale_of_comp_of_etale_of_surjective g' (V.ι ≫ u)

end GlobalTheory
end

section

open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory


open CategoryTheory Limits AlgebraicGeometry in
theorem _root_.GlobalTheory.isAffineHom_of_isAffineHom_pullback_snd_of_fpqc :
    ∀ (X Y Y' : Scheme.{0}) (f : X ⟶ Y) (g : Y' ⟶ Y), Surjective g → Flat g → QuasiCompact g →
      IsAffineHom (pullback.snd f g) → IsAffineHom f := by
  intro X Y Y' f g hs hf hq h
  haveI := _root_.GlobalTheory.isAffineHom_descendsAlong_fpqc
  exact MorphismProperty.DescendsAlong.of_isPullback (P := @IsAffineHom)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (IsPullback.of_hasPullback f g).flip
    ⟨⟨hs, hf⟩, hq⟩ h

end GlobalTheory
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory

theorem isAbelianScheme_overPullback {S S' : Scheme.{0}} (f : S' ⟶ S) (A : Over S) [GrpObj A]
    (h : IsAbelianScheme A) : IsAbelianScheme ((Over.pullback f).obj A) := by
  constructor
  · have := h.comm
    infer_instance
  · have := h.smooth
    change Smooth (pullback.snd A.hom f)
    infer_instance
  · have := h.proper
    change IsProper (pullback.snd A.hom f)
    infer_instance
  · have := h.geomConnected
    change GeometricallyConnected (pullback.snd A.hom f)
    infer_instance

end GlobalTheory
end

section


theorem _root_.GlobalTheory.T.exists_powerSeries_ringHom_extending_finite_free : ∀ (O O₁ K : Type) [CommRing O] [CommRing O₁] [CommRing K] [Algebra O O₁] [Module.Free O O₁] [Module.Finite O O₁] (i : PowerSeries O →+* K) (io : O₁ →+* K), (∀ a, io (algebraMap O O₁ a) = i (PowerSeries.C a)) → ∃ Φ : PowerSeries O₁ →+* K, (∀ a, Φ (PowerSeries.C a) = io a) ∧ Φ PowerSeries.X = i PowerSeries.X ∧ ∀ f, Φ f ∈ Subring.closure (Set.range i ∪ Set.range io) := by
  first | exact @GlobalTheory.powerSeries_extend_finite_free | exact GlobalTheory.powerSeries_extend_finite_free | (intros; apply GlobalTheory.powerSeries_extend_finite_free <;> assumption)
end

section

namespace GlobalTheory

theorem integralClosure_finite_local_of_isAdicComplete :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R]
      [CharZero R], IsAdicComplete (IsLocalRing.maximalIdeal R) R →
      ∀ (L : Type) [Field L] [Algebra (FractionRing R) L] [FiniteDimensional (FractionRing R) L]
        [Algebra R L] [IsScalarTower R (FractionRing R) L],
        Module.Finite R (integralClosure R L) ∧ IsLocalRing (integralClosure R L) ∧
          IsNoetherianRing (integralClosure R L) ∧ IsIntegrallyClosed (integralClosure R L) ∧
          IsFractionRing (integralClosure R L) L := by
  intro R _ _ _ _ _ _ hR L _ _ _ _ _
  have : CharZero (FractionRing R) := IsFractionRing.charZero_of_isFractionRing R
  have : Algebra.IsSeparable (FractionRing R) L := inferInstance
  have hfin : Module.Finite R (integralClosure R L) :=
    IsIntegralClosure.finite R (FractionRing R) L (integralClosure R L)
  have hfr : IsFractionRing (integralClosure R L) L :=
    integralClosure.isFractionRing_of_finite_extension (FractionRing R) L
  refine ⟨hfin, ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := R) _,
    IsNoetherianRing.of_finite R _, ?_, hfr⟩
  exact (isIntegrallyClosed_iff_isIntegrallyClosedIn L).2 inferInstance

end GlobalTheory
end

section

open scoped BigOperators TensorProduct

namespace GlobalTheory

theorem sum_mul_eq_zero_of_forall_dual {F K σ : Type} [Field F] [Field K] [Algebra F K]
    (S : Finset σ) (c m : σ → K)
    (h : ∀ l : K →ₗ[F] F, ∑ s ∈ S, l (c s) • m s = 0) : ∑ s ∈ S, c s * m s = 0 := by
  classical
  let b := Module.Basis.ofVectorSpace F K
  let T := S.biUnion fun s => (b.repr (c s)).support
  have hc : ∀ s ∈ S, c s = ∑ j ∈ T, b.coord j (c s) • b j := fun s hs => by
    conv_lhs => rw [← b.linearCombination_repr (c s)]
    rw [Finsupp.linearCombination_apply, Finsupp.sum_of_support_subset (s := T)]
    · rfl
    · exact Finset.subset_biUnion_of_mem (fun s => (b.repr (c s)).support) hs
    · simp
  calc ∑ s ∈ S, c s * m s = ∑ s ∈ S, ∑ j ∈ T, b j * (b.coord j (c s) • m s) := by
        refine Finset.sum_congr rfl fun s hs => ?_
        conv_lhs => rw [hc s hs]
        rw [Finset.sum_mul]
        simp
    _ = 0 := by
        rw [Finset.sum_comm]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [← Finset.mul_sum, h, mul_zero]

theorem eval_eq_zero_of_aeval_tmul_eq_zero {F K J ι : Type} [Field F] [Field K] [Algebra F K]
    (A : ι → Type) [∀ i, CommRing (A i)] [∀ i, Algebra F (A i)] (w : ∀ i, J → A i) (v : J → K)
    (h : ∀ (G : MvPolynomial J F) (d : ℕ), G.IsHomogeneous d →
      (∀ i, MvPolynomial.aeval (w i) G = 0) → MvPolynomial.aeval v G = 0)
    (G : MvPolynomial J K) (d : ℕ) (hG : G.IsHomogeneous d)
    (h0 : ∀ i, MvPolynomial.aeval (fun j => (1 : K) ⊗ₜ[F] w i j) G = 0) :
    MvPolynomial.eval v G = 0 := by
  rw [MvPolynomial.eval_eq]
  refine sum_mul_eq_zero_of_forall_dual (F := F) _ _ _ fun l => ?_
  have key : ∀ (B : Type) [CommRing B] [Algebra F B] (u : J → B),
      MvPolynomial.aeval u (∑ s ∈ G.support, MvPolynomial.monomial s (l (G.coeff s))) =
        ∑ s ∈ G.support, l (G.coeff s) • ∏ j ∈ s.support, u j ^ s j := fun B _ _ u => by

    rw [map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [MvPolynomial.aeval_monomial, Algebra.smul_def]
    rfl
  rw [← key]
  refine h _ d (MvPolynomial.IsHomogeneous.sum _ _ _ fun s hs => ?_) fun i => ?_
  · refine MvPolynomial.isHomogeneous_monomial _ ?_
    rw [Finsupp.degree_eq_weight_one]
    exact hG (MvPolynomial.mem_support_iff.mp hs)
  · rw [key]
    have h1 := congrArg ((TensorProduct.lid F (A i)).toLinearMap ∘ₗ l.rTensor (A i)) (h0 i)

    rw [map_zero, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq, map_sum] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun s _ => ?_
    have h2 : algebraMap K (K ⊗[F] A i) (G.coeff s) * ∏ j ∈ s.support, ((1 : K) ⊗ₜ[F] w i j) ^ s j
        = G.coeff s ⊗ₜ[F] ∏ j ∈ s.support, w i j ^ s j := by
      have : ∏ j ∈ s.support, ((1 : K) ⊗ₜ[F] w i j) ^ s j
          = (1 : K) ⊗ₜ[F] ∏ j ∈ s.support, w i j ^ s j := by
        simp only [← Algebra.TensorProduct.includeRight_apply (R := F) (A := K), map_prod, map_pow]
      rw [this]
      simp
    rw [h2]
    simp

theorem exists_complete_discreteValuationRing_of_mem_closure_cones :
    ∀ (F K J ι : Type) [Field F] [Field K] [Algebra F K] [Fintype J] [Finite ι] (A : ι → Type) [∀ i, CommRing (A i)] [∀ i, Algebra F (A i)], (∀ i, Algebra.FiniteType F (A i)) → ∀ (w : ∀ i, J → A i) (v : J → K), v ≠ 0 → (∀ (G : MvPolynomial J F) (d : ℕ), G.IsHomogeneous d → (∀ i, MvPolynomial.aeval (w i) G = 0) → MvPolynomial.aeval v G = 0) → ∃ (i : ι) (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : Algebra K W) (f : A i →+* FractionRing W) (s : FractionRing W) (w' : J → W), IsAdicComplete (IsLocalRing.maximalIdeal W) W ∧ s ≠ 0 ∧ (∀ x : F, f (algebraMap F (A i) x) = algebraMap W (FractionRing W) (algebraMap K W (algebraMap F K x))) ∧ ∀ j, algebraMap W (FractionRing W) (w' j) = s * f (w i j) ∧ w' j - algebraMap K W (v j) ∈ IsLocalRing.maximalIdeal W := by
  intro F K J ι _ _ _ _ _ A _ _ hA w v hv h
  classical
  have hN : ∀ i, IsNoetherianRing (K ⊗[F] A i) := fun i =>
    Algebra.FiniteType.isNoetherianRing K _
  by_cases hex : ∃ (i : ι) (P : Ideal (K ⊗[F] A i)), P ∈ minimalPrimes (K ⊗[F] A i) ∧
      ∀ (G : MvPolynomial J K) (d : ℕ), G.IsHomogeneous d →
        MvPolynomial.aeval (fun j => Ideal.Quotient.mk P ((1 : K) ⊗ₜ[F] w i j)) G = 0 →
        MvPolynomial.eval v G = 0
  · obtain ⟨i, P, hP, hG⟩ := hex
    have : P.IsPrime := hP.1.1
    obtain ⟨W, _, _, _, _, f, s, w', h1, h2, h3⟩ :=
      exists_complete_discreteValuationRing_of_mem_closure_cone K ((K ⊗[F] A i) ⧸ P) J
        inferInstance _ v hv hG
    refine ⟨i, W, inferInstance, inferInstance, inferInstance, inferInstance,
      f.toRingHom.comp ((Ideal.Quotient.mk P).comp
        (Algebra.TensorProduct.includeRight (R := F) (A := K) (B := A i)).toRingHom),
      s, w', h1, h2, fun x => ?_, h3⟩
    rw [← IsScalarTower.algebraMap_apply K W (FractionRing W), ← f.commutes]
    change f (Ideal.Quotient.mk P (Algebra.TensorProduct.includeRight (R := F) (A := K)
      (algebraMap F (A i) x))) = f (Ideal.Quotient.mk P (algebraMap K _ (algebraMap F K x)))
    rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
  · exfalso
    push_neg at hex
    choose G d hG hG0 hGv using hex
    have : ∀ i, Finite (minimalPrimes (K ⊗[F] A i)) := fun i =>
      (minimalPrimes.finite_of_isNoetherianRing _).to_subtype
    letI : Fintype (Σ i, minimalPrimes (K ⊗[F] A i)) := Fintype.ofFinite _
    let H : MvPolynomial J K := ∏ x : Σ i, minimalPrimes (K ⊗[F] A i), G x.1 x.2.1 x.2.2
    have hH : H.IsHomogeneous (∑ x : Σ i, minimalPrimes (K ⊗[F] A i), d x.1 x.2.1 x.2.2) :=
      MvPolynomial.IsHomogeneous.prod _ _ _ fun x _ => hG _ _ _
    have hHv : MvPolynomial.eval v H ≠ 0 := by
      rw [map_prod]
      exact Finset.prod_ne_zero_iff.mpr fun x _ => hGv _ _ _
    have hnil : ∀ i, IsNilpotent (MvPolynomial.aeval (fun j => (1 : K) ⊗ₜ[F] w i j) H) := by
      intro i
      rw [nilpotent_iff_mem_prime]
      intro Q hQ
      obtain ⟨P, hP, hPQ⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := Q) bot_le
      refine hPQ ?_
      rw [map_prod]
      refine Ideal.prod_mem P (Finset.mem_univ
        (⟨i, P, hP⟩ : Σ i, minimalPrimes (K ⊗[F] A i))) ?_
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← hG0 i P hP]
      exact MvPolynomial.comp_aeval_apply _ (Ideal.Quotient.mkₐ K P) _
    choose n hn using hnil
    letI : Fintype ι := Fintype.ofFinite ι
    refine pow_ne_zero (∑ i, n i) hHv ?_
    rw [← map_pow]
    refine eval_eq_zero_of_aeval_tmul_eq_zero A w v h _ _ (hH.pow _) fun i => ?_
    rw [map_pow]
    exact pow_eq_zero_of_le (Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)) (hn i)

end GlobalTheory
end
