module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.MorphismProperty.Descent
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.SplitTorusAff
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Countable.Defs
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle003
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.OreLocalization.Ring
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
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
public import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors

namespace GlobalTheory.AdLat

section

variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem adele_mul_integral {a b : FiniteAdeleRing (𝓞 F) F} {v : HeightOneSpectrum (𝓞 F)}
    (ha : a v ∈ v.adicCompletionIntegers F) (hb : b v ∈ v.adicCompletionIntegers F) :
    (a * b) v ∈ v.adicCompletionIntegers F := by
  have : (a * b) v = a v * b v := RestrictedProduct.mul_apply _ a b v
  rw [this]; exact mul_mem ha hb

theorem adele_add_integral {a b : FiniteAdeleRing (𝓞 F) F} {v : HeightOneSpectrum (𝓞 F)}
    (ha : a v ∈ v.adicCompletionIntegers F) (hb : b v ∈ v.adicCompletionIntegers F) :
    (a + b) v ∈ v.adicCompletionIntegers F := by
  have : (a + b) v = a v + b v := RestrictedProduct.add_apply _ a b v
  rw [this]; exact add_mem ha hb

theorem adele_neg_integral {a : FiniteAdeleRing (𝓞 F) F} {v : HeightOneSpectrum (𝓞 F)}
    (ha : a v ∈ v.adicCompletionIntegers F) :
    (-a) v ∈ v.adicCompletionIntegers F := by
  have : (-a) v = -a v := RestrictedProduct.neg_apply _ a v
  rw [this]; exact neg_mem ha

theorem adele_one_integral (v : HeightOneSpectrum (𝓞 F)) :
    (1 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F := by
  have : (1 : FiniteAdeleRing (𝓞 F) F) v = 1 := RestrictedProduct.one_apply _ _
  rw [this]; exact one_mem _

theorem adele_zero_integral (v : HeightOneSpectrum (𝓞 F)) :
    (0 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F := by
  have : (0 : FiniteAdeleRing (𝓞 F) F) v = 0 := RestrictedProduct.zero_apply _ _
  rw [this]; exact zero_mem _

theorem tmul_mem_adelicCompletion_of_integral {J : Set E} {a : FiniteAdeleRing (𝓞 F) F}
    (ha : ∀ v, a v ∈ v.adicCompletionIntegers F) {x : E} (hx : x ∈ J) :
    a ⊗ₜ[F] x ∈ hat1 F J :=
  AddSubgroup.subset_closure ⟨a, ha, x, hx, rfl⟩

theorem one_tmul_mem_adelicCompletionOfElementSet {J : Set E} {x : E} (hx : x ∈ J) :
    (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x ∈ hat1 F J :=
  tmul_mem_adelicCompletion_of_integral F (adele_one_integral F) hx

theorem mul_mem_adelicCompletionOfElementSet_of_mul_mem {I J K : Set E} (h : ∀ x ∈ I, ∀ y ∈ J, x * y ∈ K)
    {x y : RA F E} (hx : x ∈ hat1 F I) (hy : y ∈ hat1 F J) : x * y ∈ hat1 F K := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hx
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨b, hb, y, hy, rfl⟩ := hy
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      exact tmul_mem_adelicCompletion_of_integral F (fun v => adele_mul_integral F (ha v) (hb v))
        (h x hx y hy)
    | zero => rw [mul_zero]; exact zero_mem _
    | add y z _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
    | neg y _ h1 => rw [mul_neg]; exact neg_mem h1
  | zero => rw [zero_mul]; exact zero_mem _
  | add y z _ _ h1 h2 => rw [add_mul]; exact add_mem h1 h2
  | neg y _ h1 => rw [neg_mul]; exact neg_mem h1

theorem galoisAut_mem_adelicCompletionOfElementSet (c : E ≃ₐ[F] E) {I J : Set E} (h : ∀ x ∈ I, c x ∈ J)
    {z : RA F E} (hz : z ∈ hat1 F I) : sg (FiniteAdeleRing (𝓞 F) F) c z ∈ hat1 F J := by
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hx
    exact tmul_mem_adelicCompletion_of_integral F ha (h x hx)
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ h1 h2 => rw [map_add (f := _)]; exact add_mem h1 h2
  | neg y _ h1 => rw [map_neg]; exact neg_mem h1

theorem mem_range_iff_adele_integral (x : F) :
    x ∈ (algebraMap (𝓞 F) F).range ↔
      ∀ v, algebraMap F (FiniteAdeleRing (𝓞 F) F) x v ∈ v.adicCompletionIntegers F := by
  simp only [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.mem_adicCompletionIntegers,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  constructor
  · rintro ⟨a, rfl⟩ v
    exact v.valuation_le_one a
  · exact HeightOneSpectrum.mem_integers_of_valuation_le_one F x

theorem linearForm_integral_of_one_tmul_mem_adelicCompletion {I : Set E} (t : E →ₗ[F] F)
    (ht : ∀ y ∈ I, t y ∈ (algebraMap (𝓞 F) F).range) {x : E}
    (hx : (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x ∈ hat1 F I) :
    t x ∈ (algebraMap (𝓞 F) F).range := by
  let T : RA F E →ₗ[F] FiniteAdeleRing (𝓞 F) F :=
    (TensorProduct.rid F _).toLinearMap ∘ₗ LinearMap.lTensor _ t
  have hT : ∀ a y, T (a ⊗ₜ[F] y) = algebraMap F _ (t y) * a := by
    intro a y
    simp [T, Algebra.smul_def]
  have key : ∀ z ∈ hat1 F I, ∀ v, T z v ∈ v.adicCompletionIntegers F := by
    intro z hz v
    induction hz using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨a, ha, y, hy, rfl⟩ := hx
      rw [hT]
      exact adele_mul_integral F
        ((mem_range_iff_adele_integral F _).1 (ht y hy) v) (ha v)
    | zero => rw [map_zero]; exact adele_zero_integral F v
    | add y z _ _ h1 h2 => rw [map_add (f := _)]; exact adele_add_integral F h1 h2
    | neg y _ h1 => rw [map_neg]; exact adele_neg_integral F h1
  rw [mem_range_iff_adele_integral]
  have := key _ hx
  rwa [hT, mul_one] at this

variable [NumberField E]

theorem one_tmul_mem_adelicCompletion_fractionalIdeal_iff (I : FractionalIdeal (𝓞 E)⁰ E) (x : E) :
    (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x ∈ hat1 F (I : Set E) ↔ x ∈ I := by
  refine ⟨fun hx => ?_, fun hx => one_tmul_mem_adelicCompletionOfElementSet F hx⟩
  by_cases hI : I = 0
  · subst hI
    rw [FractionalIdeal.mem_zero_iff]
    by_contra h0
    obtain ⟨t, ht⟩ := Module.Projective.exists_dual_eq_one F h0
    apply RingOfIntegers.not_isField F
    rw [← IsFractionRing.surjective_iff_isField (K := F)]
    intro c
    have := linearForm_integral_of_one_tmul_mem_adelicCompletion F (c • t) (fun y hy => by
      have hy' : y = 0 := (FractionalIdeal.mem_zero_iff _).1 hy
      rw [hy', map_zero]; exact zero_mem _) hx
    simpa [ht] using this
  · rw [← FractionalIdeal.dual_dual (𝓞 F) F I,
      FractionalIdeal.mem_dual (FractionalIdeal.dual_ne_zero _ _ hI)]
    intro y hy
    rw [FractionalIdeal.mem_dual hI] at hy
    have := linearForm_integral_of_one_tmul_mem_adelicCompletion F (Algebra.traceForm F E y) hy hx
    rwa [Algebra.traceForm_apply, mul_comm] at this

theorem mem_adelicCompletion_mul_inv_fractionalIdeal (I J : FractionalIdeal (𝓞 E)⁰ E) (z : RA F E) (hI : I ≠ 0)
    (h : ∀ x ∈ I, z * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x) ∈ hat1 F (J : Set E)) :
    z ∈ hat1 F ((J * I⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
  have h1 : (1 : E) ∈ I * I⁻¹ := by
    rw [mul_inv_cancel₀ hI]; exact FractionalIdeal.one_mem_one _
  have key : ∀ w ∈ I * I⁻¹, z * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] w) ∈
      hat1 F ((J * I⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
    intro w hw
    refine FractionalIdeal.mul_induction_on hw (fun x hx y hy => ?_) (fun x y hx hy => ?_)
    · have := mul_mem_adelicCompletionOfElementSet_of_mul_mem F (K := ((J * I⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E))
        (fun a ha b hb => FractionalIdeal.mul_mem_mul ha hb) (h x hx) (one_tmul_mem_adelicCompletionOfElementSet F hy)
      rwa [mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, mul_one] at this
    · rw [TensorProduct.tmul_add, mul_add]; exact add_mem hx hy
  have := key 1 h1
  rwa [← Algebra.TensorProduct.one_def, mul_one] at this

end

theorem adelicCompletion_fractionalIdeal_properties : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], (∀ I J : FractionalIdeal (𝓞 E)⁰ E, ∀ x ∈ hat1 F (I : Set E), ∀ y ∈ hat1 F (J : Set E), x * y ∈ hat1 F ((I * J : FractionalIdeal (𝓞 E)⁰ E) : Set E)) ∧ (∀ (I : FractionalIdeal (𝓞 E)⁰ E) (x : E), (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x ∈ hat1 F (I : Set E) ↔ x ∈ I) ∧ (∀ (I J : FractionalIdeal (𝓞 E)⁰ E) (z : RA F E), I ≠ 0 → (∀ x ∈ I, z * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x) ∈ hat1 F (J : Set E)) → z ∈ hat1 F ((J * I⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E)) ∧ ∀ (c : E ≃ₐ[F] E) (I I' : FractionalIdeal (𝓞 E)⁰ E), (∀ x ∈ I, c x ∈ I') → ∀ z ∈ hat1 F (I : Set E), sg (FiniteAdeleRing (𝓞 F) F) c z ∈ hat1 F (I' : Set E) := by
  intro F E _ _ _ _ _
  exact ⟨fun I J x hx y hy => mul_mem_adelicCompletionOfElementSet_of_mul_mem F
      (fun a ha b hb => FractionalIdeal.mul_mem_mul ha hb) hx hy,
    one_tmul_mem_adelicCompletion_fractionalIdeal_iff F, mem_adelicCompletion_mul_inv_fractionalIdeal F, fun c I I' h z hz => galoisAut_mem_adelicCompletionOfElementSet F c h hz⟩

end GlobalTheory.AdLat
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.KernelNoTorsion

theorem eq_of_isSchemeTheoreticallyDominant {X S Y Z : Scheme.{0}} (f : X ⟶ S) [IsSeparated f]
    {a b : Y ⟶ X} (hab : a ≫ f = b ≫ f) (j : Z ⟶ Y) [IsSchemeTheoreticallyDominant j]
    (hj : j ≫ a = j ≫ b) : a = b := by
  have := GlobalTheory.isClosedImmersion_equalizer_ι_of_isSeparated f hab
  have hk : (equalizer.ι a b).ker = ⊥ := by
    have h := Scheme.Hom.le_ker_comp (equalizer.lift j hj) (equalizer.ι a b)
    rw [equalizer.lift_ι, j.ker_eq_bot] at h
    exact le_bot_iff.mp h
  have : IsIso (equalizer.ι a b) := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hk
  rw [← cancel_epi (equalizer.ι a b), equalizer.condition]

theorem eq_of_generic (T K : Type) [CommRing T] [IsDomain T] [Field K] [Algebra T K]
    [IsFractionRing T K] {Y X : Over (Sp T)} [Flat Y.hom] [IsSeparated X.hom] {a b : Y ⟶ X}
    (h : (Over.pullback (spMap (algebraMap T K))).map a =
      (Over.pullback (spMap (algebraMap T K))).map b) : a = b := by
  have : IsDominant (spMap (algebraMap T K)) := by
    rw [isDominant_iff]
    refine (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap T K)).mpr ?_
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective T K)]
    exact bot_le
  have := IsSchemeTheoreticallyDominant.of_isDominant (spMap (algebraMap T K))
  apply Over.OverMorphism.ext
  refine eq_of_isSchemeTheoreticallyDominant X.hom ((Over.w a).trans (Over.w b).symm)
    (pullback.fst Y.hom (spMap (algebraMap T K))) ?_
  have h' := congr(($h).left ≫ pullback.fst X.hom (spMap (algebraMap T K)))
  exact (pullback.lift_fst _ _ _).symm.trans (h'.trans (pullback.lift_fst _ _ _))

theorem comp_mulN {S : Scheme.{0}} {Y G : Over S} [GrpObj G] (x : Y ⟶ G) (n : ℕ) :
    x ≫ mulN G n = x ^ n := by
  induction n with
  | zero => rw [pow_zero, mulN, Hom.one_def, comp_toUnit_assoc]
  | succ n ih => rw [pow_succ, mulN, Hom.mul_def, comp_lift_assoc, ih, Category.comp_id]

noncomputable def torsionLift {S : Scheme.{0}} {Y G : Over S} [GrpObj G] {n : ℕ} (x : Y ⟶ G)
    (hx : x ^ n = 1) : Y ⟶ torsion G n :=
  pullback.lift x (toUnit Y) (by rw [comp_mulN, hx, Hom.one_def])

theorem torsionLift_ι {S : Scheme.{0}} {Y G : Over S} [GrpObj G] {n : ℕ} (x : Y ⟶ G)
    (hx : x ^ n = 1) : torsionLift x hx ≫ torsion.ι G n = x :=
  pullback.lift_fst _ _ _

theorem torsion_hom_ext {S : Scheme.{0}} {Y G : Over S} [GrpObj G] {n : ℕ}
    {a b : Y ⟶ torsion G n} (h : a ≫ torsion.ι G n = b ≫ torsion.ι G n) : a = b :=
  pullback.hom_ext h (toUnit_unique _ _)

theorem torsionι_pow {S : Scheme.{0}} (G : Over S) [GrpObj G] (n : ℕ) :
    torsion.ι G n ^ n = 1 := by
  rw [← comp_mulN, Hom.one_def]
  refine (pullback.condition).trans ?_
  congr 1
  exact toUnit_unique _ _

theorem eq_one_of_pow_eq_one_of_comp_eq_one :
    ∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (Ga G : Over (Sp T)) [GrpObj Ga] [GrpObj G] [IsCommMonObj Ga] [IsCommMonObj G] (p : Ga ⟶ G) (n : ℕ), IsMonHom p → IsSeparated Ga.hom → Etale (torsion Ga n).hom → Etale (torsion G n).hom → IsIso ((Over.pullback (spMap (algebraMap T K))).map p) → ∀ (Y : Over (Sp T)) (x : Y ⟶ Ga), x ^ n = 1 → x ≫ p = 1 → x = 1 := by
  intro T K _ _ _ _ _ _ Ga G _ _ _ _ p n hp hsep hA hB hiso Y x hx hxp
  have hq : (torsion.ι Ga n ≫ p) ^ n = 1 := by
    rw [← MonObj.pow_comp, torsionι_pow, MonObj.one_comp]
  let q : torsion Ga n ⟶ torsion G n := torsionLift _ hq
  let e : torsion Ga n ⟶ torsion G n := torsionLift 1 (one_pow n)
  have hopen := GlobalTheory.isOpenImmersion_equalizer_ι_left_of_unramified q e
  have hflat : Flat (equalizer q e).hom := by
    rw [← Over.w (equalizer.ι q e)]
    infer_instance
  have h1 : (equalizer.ι q e ≫ torsion.ι Ga n) ≫ p = (1 : equalizer q e ⟶ Ga) ≫ p := by
    have := equalizer.condition q e =≫ torsion.ι G n
    rw [Category.assoc, Category.assoc, torsionLift_ι, torsionLift_ι, MonObj.comp_one] at this
    rw [Category.assoc, this, MonObj.one_comp]
  have h2 : equalizer.ι q e ≫ torsion.ι Ga n = 1 := by
    apply eq_of_generic T K
    rw [← cancel_mono ((Over.pullback (spMap (algebraMap T K))).map p), ← Functor.map_comp,
      ← Functor.map_comp, h1]
  have h3 : torsionLift x hx ≫ q = torsionLift x hx ≫ e := by
    apply torsion_hom_ext
    rw [Category.assoc, Category.assoc, torsionLift_ι, torsionLift_ι, MonObj.comp_one,
      ← Category.assoc, torsionLift_ι, hxp]
  rw [← torsionLift_ι x hx, ← equalizer.lift_ι (torsionLift x hx) h3, Category.assoc, h2,
    MonObj.comp_one]

end GlobalTheory.KernelNoTorsion
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem ringHom_flat_codescendsAlong_faithfullyFlat :
    RingHom.CodescendsAlong.{0} RingHom.Flat RingHom.FaithfullyFlat := by
  refine .mk _ RingHom.Flat.respectsIso fun R S T _ _ _ _ _ h h' ↦ ?_
  rw [RingHom.flat_algebraMap_iff] at h' ⊢
  rw [RingHom.faithfullyFlat_algebraMap_iff] at h
  exact .of_flat_tensorProduct R T S

theorem flat_descendsAlong_fpqc :
    MorphismProperty.DescendsAlong (@Flat : MorphismProperty Scheme.{0})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  HasRingHomProperty.descendsAlong_flat ringHom_flat_codescendsAlong_faithfullyFlat

theorem isPullback_overPullback_map_left {S S' : Scheme.{0}} (f : S' ⟶ S) {X Y : Over S}
    (φ : X ⟶ Y) :
    IsPullback ((Over.pullback f).map φ).left (pullback.fst X.hom f) (pullback.fst Y.hom f)
      φ.left := by
  refine IsPullback.flip (IsPullback.of_bot (v₂₁ := pullback.snd Y.hom f) (v₂₂ := Y.hom) (h₃₁ := f)
    ?_ (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback Y.hom f))
  have h₁ : ((Over.pullback f).map φ).left ≫ pullback.snd Y.hom f = pullback.snd X.hom f :=
    pullback.lift_snd _ _ _
  rw [h₁, Over.w φ]
  exact IsPullback.of_hasPullback X.hom f

theorem flat_of_flat_fieldBaseChange (k k' : Type) [Field k] [Field k'] (σ : k →+* k')
    (X Y : Over (Sp k)) (φ : X ⟶ Y)
    (h : Flat ((Over.pullback (spMap σ)).map φ).left) : Flat φ.left := by
  haveI := flat_descendsAlong_fpqc
  have h₁ : Flat (spMap σ) := inferInstance
  have h₂ : Surjective (spMap σ) := inferInstance
  have h₃ : QuasiCompact (spMap σ) := inferInstance
  exact MorphismProperty.of_isPullback_of_descendsAlong (P := @Flat)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (isPullback_overPullback_map_left (spMap σ) φ)
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ h

end GlobalTheory
end

section

namespace GlobalTheory.CompRat

theorem exists_ringEquiv_complex_comp_eq :
    ∀ (k : Type) [Field k] [Countable k] (φ ψ : k →+* ℂ), ∃ τ : ℂ ≃+* ℂ, ∀ x, τ (φ x) = ψ x :=
  fun _ _ _ φ ψ => GlobalTheory.GaloisDescent.exists_complex_ringEquiv_comp_eq φ ψ

end GlobalTheory.CompRat
end

section

namespace GlobalTheory

theorem exists_awayMap_subalgebra (K : Type) [Field K] (S : Type) [CommRing S] [Algebra K S]
    (S₁ : Subalgebra K S) (x : S) (hx : x ∈ S₁) :
    ∃ κ : Localization.Away (⟨x, hx⟩ : S₁) →ₐ[K] Localization.Away x,
      (∀ s : S₁, κ (algebraMap S₁ _ s) = algebraMap S _ (s : S)) ∧ Function.Injective κ ∧
      ∀ (z : Localization.Away x) (m : ℕ) (s : S), s ∈ S₁ →
        z * algebraMap S _ x ^ m = algebraMap S _ s → z ∈ κ.range := by
  first
  | exact @_root_.GlobalTheory.AwaySubalgebraEmbedding.exists_away_subalgebra_embedding
  | exact _root_.GlobalTheory.AwaySubalgebraEmbedding.exists_away_subalgebra_embedding
  | (apply _root_.GlobalTheory.AwaySubalgebraEmbedding.exists_away_subalgebra_embedding <;> assumption)
  | (intros; apply _root_.GlobalTheory.AwaySubalgebraEmbedding.exists_away_subalgebra_embedding <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AwaySubalgebraEmbedding.exists_away_subalgebra_embedding <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AwaySubalgebraEmbedding.exists_away_subalgebra_embedding ..)

theorem exists_fg_subalgebra_desc_away : ∀ (K : Type) [Field K] (S : Type) [CommRing S] [Algebra K S] (S₀ : Subalgebra K S), S₀.FG → ∀ (n : ℕ) (h : Fin n → S) (A : Fin n → Type) [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)], (∀ i, Algebra.FiniteType K (A i)) → ∀ a : ∀ i, A i →ₐ[K] Localization.Away (h i), Ideal.span (Set.range h) = ⊤ → ∃ (S₁ : Subalgebra K S) (h₁ : Fin n → S₁), S₁.FG ∧ S₀ ≤ S₁ ∧ (∀ i, (h₁ i : S) = h i) ∧ Ideal.span (Set.range h₁) = ⊤ ∧ ∀ i, ∃ (κ : Localization.Away (h₁ i) →ₐ[K] Localization.Away (h i)) (a' : A i →ₐ[K] Localization.Away (h₁ i)), (∀ s : S₁, κ (algebraMap S₁ _ s) = algebraMap S _ (s : S)) ∧ Function.Injective κ ∧ κ.comp a' = a i := by
  classical
  intro K _ S _ _ S₀ hS₀ n h A _ _ hA a hspan
  obtain ⟨c, hc⟩ : ∃ c : Fin n → S, ∑ i, c i * h i = 1 :=
    Ideal.mem_span_range_iff_exists_fun.1 (hspan ▸ Submodule.mem_top)
  choose G hG using fun i => (hA i).out
  choose m s hs using fun i (g : A i) => IsLocalization.Away.surj (h i) (a i g)
  let T : Finset S := Finset.univ.image h ∪ Finset.univ.image c ∪
    Finset.univ.biUnion fun i => (G i).image (s i)
  let S₁ : Subalgebra K S := S₀ ⊔ Algebra.adjoin K (T : Set S)
  have hT : ∀ t ∈ T, t ∈ S₁ := fun t ht =>
    (le_sup_right : Algebra.adjoin K (T : Set S) ≤ S₁) (Algebra.subset_adjoin ht)
  have hh : ∀ i, h i ∈ S₁ := fun i => hT _ (by simp [T])
  have hcm : ∀ i, c i ∈ S₁ := fun i => hT _ (by simp [T])
  have hsm : ∀ i, ∀ g ∈ G i, s i g ∈ S₁ := fun i g hg => hT _ (by
    simp only [T, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image]
    exact Or.inr ⟨i, Finset.mem_univ _, g, hg, rfl⟩)
  refine ⟨S₁, fun i => ⟨h i, hh i⟩, hS₀.sup ⟨T, rfl⟩, le_sup_left, fun _ => rfl, ?_, ?_⟩
  · rw [Ideal.eq_top_iff_one]
    refine Ideal.mem_span_range_iff_exists_fun.2 ⟨fun i => ⟨c i, hcm i⟩, Subtype.ext ?_⟩
    simpa using hc
  · intro i
    obtain ⟨κ, hκ, hinj, hr⟩ := exists_awayMap_subalgebra K S S₁ (h i) (hh i)
    have hmem : ∀ y : A i, a i y ∈ κ.range := by
      intro y
      have : (⊤ : Subalgebra K (A i)) ≤ κ.range.comap (a i) := by
        rw [← hG i, Algebra.adjoin_le_iff]
        intro g hg
        exact hr _ (m i g) _ (hsm i g hg) (hs i g)
      exact this Algebra.mem_top
    refine ⟨κ, (AlgEquiv.ofInjective κ hinj).symm.toAlgHom.comp ((a i).codRestrict _ hmem),
      hκ, hinj, ?_⟩
    ext y
    have := AlgEquiv.ofInjective_apply κ hinj
      ((AlgEquiv.ofInjective κ hinj).symm ⟨a i y, hmem y⟩)
    rw [AlgEquiv.apply_symm_apply] at this
    exact this.symm

end GlobalTheory
end
