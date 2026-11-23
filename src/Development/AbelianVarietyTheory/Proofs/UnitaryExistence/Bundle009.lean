module

public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealEqBotOfFlatQuotientOfMapMaximalIdeal
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle007
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Mathlib.Tactic.TypeStar
public import Mathlib.AlgebraicGeometry.Noetherian
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors

namespace GlobalTheory.AdLat

theorem one_ne_zero_fracIdeal (F : Type) [Field F] [NumberField F] :
    (1 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := one_ne_zero

theorem mem_adelicIdeal_one_iff_integral (F : Type) [Field F] [NumberField F]
    (a : FiniteAdeleRing (𝓞 F) F) :
    a ∈ GlobalTheory.Idele.adelicIdeal (1 : FractionalIdeal (𝓞 F)⁰ F) ↔
      ∀ v, a v ∈ v.adicCompletionIntegers F := by
  constructor
  · intro h v
    have hv := h v
    unfold GlobalTheory.Idele.localIdeal at hv
    revert hv
    generalize a v = y
    intro hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hk
      exact HeightOneSpectrum.coe_algebraMap_mem (R := 𝓞 F) (K := F) (v := v) r
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul c x _ hx =>
      rw [show c • x = (c : v.adicCompletion F) * x from rfl]
      exact mul_mem c.2 hx
  · intro h v
    unfold GlobalTheory.Idele.localIdeal
    rw [← mul_one (a v), show a v * 1 = (⟨a v, h v⟩ : v.adicCompletionIntegers F) •
      (1 : v.adicCompletion F) from rfl]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨1, (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩, map_one _⟩)

private theorem exists_valuation_sub_lt_of_injective (F : Type) [Field F] [NumberField F]
    (T : Finset (HeightOneSpectrum (𝓞 F))) (c : HeightOneSpectrum (𝓞 F) → F) :
    ∃ w : F, (∀ v ∈ T, v.valuation F (w - c v) ≤ 1) ∧ ∀ v ∉ T, v.valuation F w ≤ 1 := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (𝓞 F)⁰ T c
  set d : 𝓞 F := (b : 𝓞 F) with hd_def
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero b.2
  have hdK : algebraMap (𝓞 F) F d ≠ 0 := by
    rwa [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)]
  have hex : ∀ v : HeightOneSpectrum (𝓞 F), ∃ r : 𝓞 F,
      algebraMap (𝓞 F) F r = algebraMap (𝓞 F) F d * (if v ∈ T then c v else 0) := by
    intro v
    by_cases hv : v ∈ T
    · obtain ⟨r, hr⟩ := RingHom.mem_rangeS.1 (hb v hv)
      refine ⟨r, ?_⟩
      rw [if_pos hv, hr, Algebra.smul_def]
    · exact ⟨0, by simp [hv]⟩
  choose g hg using hex
  have hfin : {v : HeightOneSpectrum (𝓞 F) | v.asIdeal ∣ Ideal.span {d}}.Finite :=
    Ideal.finite_factors (by
      simpa only [Submodule.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot] using hd0)
  set S : Finset (HeightOneSpectrum (𝓞 F)) := T ∪ hfin.toFinset with hS
  obtain ⟨r, hr⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S)
    (fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal)
    (fun v : HeightOneSpectrum (𝓞 F) =>
      (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {d} : Ideal (𝓞 F))).factors)
    (fun v _ => v.prime) (fun i _ j _ hij h => hij (HeightOneSpectrum.ext h)) (fun i => g i)
  have key : ∀ v ∈ S, v.valuation F (algebraMap (𝓞 F) F r / algebraMap (𝓞 F) F d -
      (if v ∈ T then c v else 0)) ≤ 1 := by
    intro v hv
    have h1 : algebraMap (𝓞 F) F r / algebraMap (𝓞 F) F d - (if v ∈ T then c v else 0)
        = algebraMap (𝓞 F) F (r - g v) / algebraMap (𝓞 F) F d := by
      rw [map_sub, hg v, sub_div, mul_div_cancel_left₀ _ hdK]
    rw [h1, map_div₀, div_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff (v.valuation F)).2 hdK)),
      HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
      v.intValuation_if_neg hd0]
    exact (v.intValuation_le_pow_iff_mem _ _).2 (hr v hv)
  refine ⟨algebraMap (𝓞 F) F r / algebraMap (𝓞 F) F d, fun v hv => ?_, fun v hv => ?_⟩
  · have h := key v (Finset.mem_union_left _ hv)
    rwa [if_pos hv] at h
  · by_cases hvS : v ∈ S
    · have h := key v hvS
      rwa [if_neg hv, sub_zero] at h
    · have hnd : ¬ v.asIdeal ∣ Ideal.span {d} := fun h =>
        hvS (Finset.mem_union_right _ (hfin.mem_toFinset.2 h))
      have hd1 : v.valuation F (algebraMap (𝓞 F) F d) = 1 := by
        rw [HeightOneSpectrum.valuation_of_algebraMap]
        exact le_antisymm (v.intValuation_le_one d)
          (not_lt.1 (fun h => hnd ((v.intValuation_lt_one_iff_dvd d).1 h)))
      rw [map_div₀, hd1, div_one, HeightOneSpectrum.valuation_of_algebraMap]
      exact v.intValuation_le_one r

private theorem exists_sub_mem_adicCompletionIntegers' (F : Type) [Field F] [NumberField F]
    (z : FiniteAdeleRing (𝓞 F) F) :
    ∃ w : F, ∀ v, z v - algebraMap F (FiniteAdeleRing (𝓞 F) F) w v ∈
      v.adicCompletionIntegers F := by
  classical
  have hfin : {v : HeightOneSpectrum (𝓞 F) | ¬ z v ∈ v.adicCompletionIntegers F}.Finite :=
    Filter.eventually_cofinite.1 z.2
  have hc : ∀ v : HeightOneSpectrum (𝓞 F), ∃ c : F,
      z v - (c : v.adicCompletion F) ∈ v.adicCompletionIntegers F := by
    intro v
    have hdense : DenseRange (fun c : F => (c : v.adicCompletion F)) :=
      HeightOneSpectrum.denseRange_algebraMap (K := F) (v := v)
    have hopen : IsOpen {t : v.adicCompletion F | z v - t ∈ v.adicCompletionIntegers F} :=
      (Valued.isOpen_valuationSubring _).preimage (continuous_const.sub continuous_id)
    have hne : z v ∈ {t : v.adicCompletion F | z v - t ∈ v.adicCompletionIntegers F} := by
      show z v - z v ∈ v.adicCompletionIntegers F
      rw [sub_self]
      exact zero_mem _
    exact hdense.exists_mem_open hopen ⟨z v, hne⟩
  choose c hc using hc
  obtain ⟨w, hw1, hw2⟩ := exists_valuation_sub_lt_of_injective F hfin.toFinset c
  refine ⟨w, fun v => ?_⟩
  rw [FiniteAdeleRing.algebraMap_apply]
  by_cases hv : v ∈ hfin.toFinset
  · have h1 : ((c v : F) : v.adicCompletion F) =
        ((c v - w : F) : v.adicCompletion F) + (w : v.adicCompletion F) := by
      rw [← HeightOneSpectrum.adicCompletion.coe_add, sub_add_cancel]
    have h2 : z v - (w : v.adicCompletion F) =
        (z v - (c v : v.adicCompletion F)) + ((c v - w : F) : v.adicCompletion F) := by
      rw [h1]; ring
    rw [h2]
    refine add_mem (hc v) ?_
    rw [HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation', Valuation.map_sub_swap]
    exact hw1 v hv
  · have hz : z v ∈ v.adicCompletionIntegers F := by
      by_contra h
      exact hv (hfin.mem_toFinset.2 h)
    refine sub_mem hz ?_
    rw [HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hw2 v hv

theorem exists_eq_algebraMap_add_nsmul (F : Type) [Field F] [NumberField F] (N : ℕ) (hN : 0 < N)
    (y : FiniteAdeleRing (𝓞 F) F) :
    ∃ (x : F) (a : FiniteAdeleRing (𝓞 F) F), (∀ v, a v ∈ v.adicCompletionIntegers F) ∧
      y = algebraMap F _ x + N • a := by
  have hN' : (N : F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  obtain ⟨w, hw⟩ := exists_sub_mem_adicCompletionIntegers' F
    (algebraMap F (FiniteAdeleRing (𝓞 F) F) (N : F)⁻¹ * y)
  refine ⟨N * w, algebraMap F (FiniteAdeleRing (𝓞 F) F) (N : F)⁻¹ * y -
    algebraMap F (FiniteAdeleRing (𝓞 F) F) w, fun v => hw v, ?_⟩
  have hA : (N : FiniteAdeleRing (𝓞 F) F) * algebraMap F (FiniteAdeleRing (𝓞 F) F) (N : F)⁻¹ = 1 := by
    rw [← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)) N, ← map_mul,
      mul_inv_cancel₀ hN', map_one]
  rw [nsmul_eq_mul, map_mul, map_natCast]
  linear_combination (-y) * hA

theorem strong_approximation_mod_nat : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ), 0 < N → (∀ y : FiniteAdeleRing (𝓞 F) F, ∃ (x : F) (a : FiniteAdeleRing (𝓞 F) F), (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ y = algebraMap F _ x + N • a) ∧ ∀ y : FiniteAdeleRing (𝓞 F) F, (∀ v, y v ∈ v.adicCompletionIntegers F) → ∃ (x : 𝓞 F) (a : FiniteAdeleRing (𝓞 F) F), (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ y = algebraMap F _ (x : F) + N • a := by
  intro F _ _ N hN
  refine ⟨exists_eq_algebraMap_add_nsmul F N hN, fun y hy => ?_⟩
  obtain ⟨x, a, ha, rfl⟩ := exists_eq_algebraMap_add_nsmul F N hN y
  have hx : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F x ≤ 1 := by
    intro v
    have hNa : (N • a) v ∈ v.adicCompletionIntegers F := by
      rw [show (N • a) v = N • a v from rfl]
      exact nsmul_mem (ha v) N
    have e : (algebraMap F (FiniteAdeleRing (𝓞 F) F) x + N • a) v =
        algebraMap F (FiniteAdeleRing (𝓞 F) F) x v + (N • a) v := rfl
    have h := sub_mem (hy v) hNa
    rw [e, add_sub_cancel_right, FiniteAdeleRing.algebraMap_apply,
      HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h
    exact h
  obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) (K := F) x hx
  subst hr
  exact ⟨r, a, ha, rfl⟩

end GlobalTheory.AdLat
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

namespace UnramifiedEndFlat

open IsLocalRing

theorem flat_of_map_maximalIdeal_self {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (φ : A →+* A) (hm : (maximalIdeal A).map φ = maximalIdeal A)
    (h₀ : ∀ b, ∃ a, φ a - b ∈ maximalIdeal A) : φ.Flat := by
  have hle : maximalIdeal A ≤ (maximalIdeal A).comap φ := Ideal.le_comap_of_map_le hm.le
  refine flat_of_surjective_quotient_sq (maximalIdeal_le_jacobson _) hle h₀ fun y hy => ?_
  rw [← hm, Ideal.map] at hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, hx, by simp⟩
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a + b, add_mem ha hb, ?_⟩
    rw [show φ (a + b) - (y + z) = (φ a - y) + (φ b - z) by rw [map_add (f := _)]; ring]
    exact add_mem hay hbz
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨d, hd⟩ := h₀ c
    refine ⟨d * a, Ideal.mul_mem_left _ _ ha, ?_⟩
    rw [show φ (d * a) - c • y = (φ d - c) * φ a + c * (φ a - y) by
      rw [map_mul, smul_eq_mul]; ring]
    refine add_mem ?_ (Ideal.mul_mem_left _ _ hay)
    rw [pow_two]
    exact Ideal.mul_mem_mul hd (hle ha)

theorem flat_of_map_maximalIdeal {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] [IsNoetherianRing A] (e : B ≃+* A)
    (φ : A →+* B) (hm : (maximalIdeal A).map φ = maximalIdeal B)
    (h₀ : ∀ b, ∃ a, φ a - b ∈ maximalIdeal B) : φ.Flat := by
  have he : (maximalIdeal B).map (e : B →+* A) = maximalIdeal A :=
    map_maximalIdeal_of_surjective _ e.surjective
  have h : ((e : B →+* A).comp φ).Flat := by
    refine flat_of_map_maximalIdeal_self _ (by rw [← Ideal.map_map, hm, he]) fun b => ?_
    obtain ⟨a, ha⟩ := h₀ (e.symm b)
    refine ⟨a, ?_⟩
    have := Ideal.mem_map_of_mem (e : B →+* A) ha
    rw [he] at this
    simpa using this
  have := h.comp (RingHom.Flat.of_bijective (f := (e.symm : A →+* B)) e.symm.bijective)
  convert this
  ext x
  simp

theorem flat_iff_comp_germ {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {x : X}
    (hx : x ∈ U) {C : CommRingCat.{0}} (g : X.presheaf.stalk x ⟶ C) :
    g.hom.Flat ↔ (X.presheaf.germ U x hx ≫ g).hom.Flat := by
  letI := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : U)
  haveI := hU.isLocalization_stalk ⟨x, hx⟩
  letI := g.hom.toAlgebra
  letI := (X.presheaf.germ U x hx ≫ g).hom.toAlgebra
  haveI : IsScalarTower Γ(X, U) (X.presheaf.stalk x) C := IsScalarTower.of_algebraMap_eq' rfl
  exact Module.flat_iff_of_isLocalization (X.presheaf.stalk x)
    (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl C

theorem flat_stalkSpecializes {X : Scheme.{0}} {x x' : X} (h : x ⤳ x') :
    (X.presheaf.stalkSpecializes h).hom.Flat := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hx', -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x') isOpen_univ
  rw [flat_iff_comp_germ hU hx', TopCat.Presheaf.germ_stalkSpecializes,
    ← Category.comp_id (X.presheaf.germ U x _), ← flat_iff_comp_germ hU]
  exact RingHom.Flat.id _

theorem flat_stalkMap_of_specializes {X Y : Scheme.{0}} (f : X ⟶ Y) {x x' : X} (h : x ⤳ x')
    (hf : (f.stalkMap x').hom.Flat) : (f.stalkMap x).hom.Flat := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hx', -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x')) isOpen_univ
  have h' : f x ⤳ f x' := h.map f.continuous
  rw [flat_iff_comp_germ hU (h'.mem_open U.2 hx'),
    ← TopCat.Presheaf.germ_stalkSpecializes Y.presheaf hx' h', Category.assoc,
    Scheme.Hom.stalkSpecializes_stalkMap f x x' h, ← flat_iff_comp_germ hU hx']
  exact hf.comp (flat_stalkSpecializes h)

theorem flat_of_closedPoints {X Y : Scheme.{0}} [JacobsonSpace X] (f : X ⟶ Y)
    (hf : ∀ x : X, IsClosed {x} → (f.stalkMap x).hom.Flat) : Flat f := by
  refine Flat.of_stalkMap f fun x => ?_
  obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints (Z := closure {x})
    ⟨x, subset_closure rfl⟩ isClosed_closure.isLocallyClosed
  exact flat_stalkMap_of_specializes f (specializes_iff_mem_closure.mpr hy) (hf y hyc)

theorem residueFieldMap_surjective {k : Type} [Field k] [IsAlgClosed k] {X Y : Scheme.{0}}
    (f : X ⟶ Y) (g : Y ⟶ Spec (.of k)) [LocallyOfFiniteType (f ≫ g)] (x : X)
    (hx : IsClosed {x}) : Function.Surjective (f.residueFieldMap x) := by
  have h : (residueFieldIsoBase (f ≫ g) x hx).inv =
      Spec.preimage (Y.fromSpecResidueField (f x) ≫ g) ≫ f.residueFieldMap x := by
    apply Spec.map_injective
    simp
  have h2 : Function.Surjective (residueFieldIsoBase (f ≫ g) x hx).inv :=
    (ConcreteCategory.bijective_of_isIso _).2
  rw [h] at h2
  exact Function.Surjective.of_comp (g := Spec.preimage (Y.fromSpecResidueField (f x) ≫ g)) h2

theorem flat_stalkMap_of_fixed {k : Type} [Field k] [IsAlgClosed k] {X : Scheme.{0}}
    (f : X ⟶ X) (g : X ⟶ Spec (.of k)) [LocallyOfFiniteType g] (hfg : f ≫ g = g)
    [FormallyUnramified f] (x : X) (hx : IsClosed {x}) (hfx : f x = x) :
    (f.stalkMap x).hom.Flat := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian g
  have : LocallyOfFiniteType (f ≫ g) := by rw [hfg]; infer_instance
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f g
  have h1 := FormallyUnramified.stalkMap f x
  have h2 := LocallyOfFiniteType.stalkMap f x
  refine flat_of_map_maximalIdeal
    (X.presheaf.stalkCongr (Inseparable.of_eq hfx.symm)).commRingCatIsoToRingEquiv _ ?_ fun b => ?_
  · algebraize [(f.stalkMap x).hom]
    have : IsLocalHom (algebraMap (X.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
      inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
    exact Algebra.FormallyUnramified.map_maximalIdeal
  · obtain ⟨a, ha⟩ := residueFieldMap_surjective f g x hx (X.residue x b)
    obtain ⟨a, rfl⟩ := X.residue_surjective (f x) a
    refine ⟨a, Ideal.Quotient.eq.mp ?_⟩
    exact ha

end UnramifiedEndFlat


open UnramifiedEndFlat in
theorem flat_of_formallyUnramified_grpEnd (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k))
    [GrpObj G] (φ : G ⟶ G) (hG : LocallyOfFiniteType G.hom) (hφ : IsMonHom φ)
    (hu : FormallyUnramified φ.left) : Flat φ.left := by
  have := LocallyOfFiniteType.jacobsonSpace G.hom
  refine UnramifiedEndFlat.flat_of_closedPoints _ fun x hx => ?_
  let x' : 𝟙_ _ ⟶ G := Over.homMk _ ((pointEquivClosedPoint G.hom).symm ⟨x, hx⟩).2
  let o : G.left := η[G].left (IsLocalRing.closedPoint k)
  have ho : IsClosed {o} := (pointEquivClosedPoint G.hom ⟨η[G].left, η[G].w⟩).2
  have hfo : φ.left o = o := by
    have : η[G] ≫ φ = η[G] := IsMonHom.one_hom φ
    exact congr(($this).left (IsLocalRing.closedPoint k))
  have h0 := UnramifiedEndFlat.flat_stalkMap_of_fixed φ.left G.hom φ.w o ho hfo
  let α := GrpObj.mulRight (A := G) x'
  let β := GrpObj.mulRight (A := G) (x' ≫ φ)
  have hαβ : α.hom ≫ φ = φ ≫ β.hom := by
    simp [α, β, comp_lift_assoc]
  have hα : η[G] ≫ α.hom = x' := by
    simpa [α, comp_lift_assoc] using lift_comp_one_left (𝟙 (𝟙_ (Over (Sp k)))) x'
  have hα' : α.hom.left o = x :=
    (congr(($hα).left (IsLocalRing.closedPoint k))).trans (pointOfClosedPoint_apply G.hom x hx _)
  have : IsIso α.hom.left := inferInstanceAs (IsIso ((Over.forget _).map α.hom))
  have : IsIso β.hom.left := inferInstanceAs (IsIso ((Over.forget _).map β.hom))
  have h1 : ((φ.left ≫ β.hom.left).stalkMap o).hom.Flat := by
    rw [Scheme.Hom.stalkMap_comp]
    exact (Flat.stalkMap β.hom.left _).comp h0
  rw [← Over.comp_left, ← hαβ, Over.comp_left, Scheme.Hom.stalkMap_comp] at h1
  rw [← hα']
  exact (RingHom.Flat.respectsIso.cancel_right_isIso
    (φ.left.stalkMap (α.hom.left o)) (α.hom.left.stalkMap o)).mp h1

end GlobalTheory
end

section

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors

theorem _root_.GlobalTheory.T.exists_idempotent_isUnit_one_add_or_sub_adele : ∀ (F : Type) [Field F] [NumberField F] (s : AdeleRing (𝓞 F) F), ∃ e : AdeleRing (𝓞 F) F, e * e = e ∧ IsUnit (e * (1 + s) + (1 - e) * (1 - s)) := by
  first | exact @GlobalTheory.AdIdem.exists_idem_isUnit | exact GlobalTheory.AdIdem.exists_idem_isUnit | (intros; apply GlobalTheory.AdIdem.exists_idem_isUnit <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Topology Matrix

theorem _root_.GlobalTheory.T.exists_adeleRing_tensor_equiv_infinite_prod_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] , letI : TopologicalSpace (AdeleRing (𝓞 F) F ⊗[F] E) := moduleTopology (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F ⊗[F] E); letI : TopologicalSpace (FiniteAdeleRing (𝓞 F) F ⊗[F] E) := moduleTopology (FiniteAdeleRing (𝓞 F) F) (FiniteAdeleRing (𝓞 F) F ⊗[F] E); letI : TopologicalSpace (InfiniteAdeleRing F ⊗[F] E) := moduleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E); ∃ e : (AdeleRing (𝓞 F) F ⊗[F] E) ≃+* (InfiniteAdeleRing F ⊗[F] E) × (FiniteAdeleRing (𝓞 F) F ⊗[F] E), (∀ z, (e z).1 = Algebra.TensorProduct.map (AlgHom.fst F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) (AlgHom.id F E) z ∧ (e z).2 = Algebra.TensorProduct.map (AlgHom.snd F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) (AlgHom.id F E) z) ∧ Continuous e ∧ Continuous e.symm := by
    exact @GlobalTheory.AdSplit.exists_adele_equiv
end
