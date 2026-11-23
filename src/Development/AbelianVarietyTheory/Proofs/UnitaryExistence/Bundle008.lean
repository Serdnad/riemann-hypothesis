module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle004
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsSmulMemOfMemSpanFraction
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle007
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle005
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.InvariantProbabilityLatticeQuotientUnique
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.Group.Smooth
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Connected
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
import Mathlib.Tactic.TypeStar
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors

theorem _root_.GlobalTheory.T.adelicCompletion_fractionalIdeal_properties_alt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], (∀ I J : FractionalIdeal (𝓞 E)⁰ E, ∀ x ∈ hat1 F (I : Set E), ∀ y ∈ hat1 F (J : Set E), x * y ∈ hat1 F ((I * J : FractionalIdeal (𝓞 E)⁰ E) : Set E)) ∧ (∀ (I : FractionalIdeal (𝓞 E)⁰ E) (x : E), (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x ∈ hat1 F (I : Set E) ↔ x ∈ I) ∧ (∀ (I J : FractionalIdeal (𝓞 E)⁰ E) (z : RA F E), I ≠ 0 → (∀ x ∈ I, z * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x) ∈ hat1 F (J : Set E)) → z ∈ hat1 F ((J * I⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E)) ∧ ∀ (c : E ≃ₐ[F] E) (I I' : FractionalIdeal (𝓞 E)⁰ E), (∀ x ∈ I, c x ∈ I') → ∀ z ∈ hat1 F (I : Set E), sg (FiniteAdeleRing (𝓞 F) F) c z ∈ hat1 F (I' : Set E) := by
  first | exact @GlobalTheory.AdLat.adelicCompletion_fractionalIdeal_properties | exact GlobalTheory.AdLat.adelicCompletion_fractionalIdeal_properties | (intros; apply GlobalTheory.AdLat.adelicCompletion_fractionalIdeal_properties <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors

namespace GlobalTheory.AdLat

section

variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem prod_mem_adelicCompletionOfElementSet {ι : Type} (s : Finset ι) (I : ι → FractionalIdeal (𝓞 E)⁰ E)
    (x : ι → RA F E) (h : ∀ i ∈ s, x i ∈ hat1 F (I i : Set E)) :
    ∏ i ∈ s, x i ∈ hat1 F ((∏ i ∈ s, I i : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.prod_empty, Algebra.TensorProduct.one_def]
    exact one_tmul_mem_adelicCompletionOfElementSet F (FractionalIdeal.one_mem_one _)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact (adelicCompletion_fractionalIdeal_properties F E).1 _ _ _ (h a (Finset.mem_insert_self _ _)) _
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem det_mem_adelicCompletionOfElementSet {n : ℕ} (r s : Fin n → FractionalIdeal (𝓞 E)⁰ E)
    (M : Matrix (Fin n) (Fin n) (RA F E))
    (h : ∀ i j, M i j ∈ hat1 F ((r i * s j : FractionalIdeal (𝓞 E)⁰ E) : Set E)) :
    M.det ∈ hat1 F (((∏ i, r i) * ∏ j, s j : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
  rw [Matrix.det_apply]
  refine sum_mem fun σ _ => ?_
  have := prod_mem_adelicCompletionOfElementSet F Finset.univ (fun j => r (σ j) * s j) (fun j => M (σ j) j)
    (fun j _ => h _ _)
  rw [Finset.prod_mul_distrib, Equiv.prod_comp σ r] at this
  rw [Units.smul_def]
  exact zsmul_mem this _

theorem cramer_mem_adelicCompletionOfElementSet {n : ℕ} (cI : Fin n → FractionalIdeal (𝓞 E)⁰ E) (hc : ∀ a, cI a ≠ 0)
    (M : Matrix (Fin n) (Fin n) (RA F E))
    (h : ∀ i j, M i j ∈ hat1 F ((cI i * (cI j)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E))
    (w : Fin n → RA F E) (hw : ∀ i, w i ∈ hat1 F (cI i : Set E)) (a : Fin n) :
    M.cramer w a ∈ hat1 F (cI a : Set E) := by
  rw [Matrix.cramer_apply]
  have := det_mem_adelicCompletionOfElementSet F cI (Function.update (fun j => (cI j)⁻¹) a 1) (M.updateCol a w) (by
    intro i j
    by_cases hj : j = a
    · subst hj
      simpa using hw i
    · simpa [hj] using h i j)
  have e : (∏ i, cI i) * ∏ j, Function.update (fun j => (cI j)⁻¹) a 1 j = cI a := by
    rw [← Finset.prod_mul_distrib, Finset.prod_eq_single a]
    · simp
    · intro b _ hb
      simp [hb, hc b]
    · simp
  rwa [e] at this

theorem algEquiv_mem_one (c : E ≃ₐ[F] E) (x : E) (hx : x ∈ (1 : FractionalIdeal (𝓞 E)⁰ E)) :
    c x ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
  rw [FractionalIdeal.mem_one_iff] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  exact ⟨⟨c y, (RingOfIntegers.isIntegral_coe y).map c.toRingEquiv.toRingHom.toIntAlgHom⟩, rfl⟩

end

theorem inv_mulVec_mem_hat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (g : GL (Fin n) (RA F E)) (c : E ≃ₐ[F] E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → (∀ z ∈ (hat F (L : Set (Fin n → E))), (g : Matrix (Fin n) (Fin n) (RA F E)) *ᵥ z ∈ (hat F (L : Set (Fin n → E)))) → (g : Matrix (Fin n) (Fin n) (RA F E)).det * sg (FiniteAdeleRing (𝓞 F) F) c (g : Matrix (Fin n) (Fin n) (RA F E)).det = 1 → ∀ z ∈ (hat F (L : Set (Fin n → E))), ((g⁻¹ : GL (Fin n) (RA F E)) : Matrix (Fin n) (Fin n) (RA F E)) *ᵥ z ∈ (hat F (L : Set (Fin n → E))) := by
  intro F E _ _ _ _ _ n L g c hfg hsp hg hdet z hz
  obtain ⟨-, e, cI, hc, hL, -⟩ := GlobalTheory.exists_pseudoBasis_adapted E n L ⊤ hfg hsp
  have key := mem_hat_pseudoBasis_iff F E n L e cI hL
  let P : Matrix (Fin n) (Fin n) (RA F E) := Matrix.of fun i a => fv F (e a) i
  let Q : Matrix (Fin n) (Fin n) (RA F E) := Matrix.of fun b i =>
    (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ e.repr (Pi.single i 1) b
  have hP : ∀ w : Fin n → RA F E, P *ᵥ w = ∑ a, w a • fv F (e a) := by
    intro w
    funext i
    simp [P, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hQ : ∀ w b, (Q *ᵥ w) b = adCoord F e b w := by
    intro w b
    change ∑ i : Fin n, _ = ∑ i : Fin n, _
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hQP : Q * P = 1 := by
    refine Matrix.ext_of_mulVec_single fun i => ?_
    funext b
    rw [← Matrix.mulVec_mulVec, hQ, hP, adCoord_sum, Matrix.one_mulVec]
  have hPQ : P * Q = 1 := mul_eq_one_comm.1 hQP
  have key' : ∀ w, P *ᵥ w ∈ hat F (L : Set (Fin n → E)) ↔ ∀ a, w a ∈ hat1 F (cI a : Set E) := by
    intro w; rw [hP]; exact key w
  set G : Matrix (Fin n) (Fin n) (RA F E) := (g : Matrix (Fin n) (Fin n) (RA F E)) with hG
  let k : Matrix (Fin n) (Fin n) (RA F E) := Q * G * P
  have hPk : P * k = G * P := by
    simp only [k, ← Matrix.mul_assoc, hPQ, Matrix.one_mul]
  have hkdet : k.det = G.det := by
    have : Q.det * P.det = 1 := by rw [← Matrix.det_mul, hQP, Matrix.det_one]
    simp only [k, Matrix.det_mul]
    linear_combination G.det * this
  have hk : ∀ i j, k i j ∈ hat1 F ((cI i * (cI j)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
    intro i j
    refine mem_adelicCompletion_mul_inv_fractionalIdeal F _ _ _ (hc j) fun x hx => ?_
    have h1 : P *ᵥ (Pi.single j ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x)) ∈
        hat F (L : Set (Fin n → E)) := by
      rw [key']
      intro a
      by_cases ha : a = j
      · subst ha
        rw [Pi.single_eq_same]
        exact one_tmul_mem_adelicCompletionOfElementSet F hx
      · rw [Pi.single_eq_of_ne ha]
        exact zero_mem _
    have h2 := hg _ h1
    rw [Matrix.mulVec_mulVec, ← hPk, ← Matrix.mulVec_mulVec, key'] at h2
    have h3 := h2 i
    rwa [Matrix.mulVec_single, Pi.smul_apply, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op] at h3
  have hd : G.det ∈ hat1 F ((1 : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
    have := det_mem_adelicCompletionOfElementSet F cI (fun j => (cI j)⁻¹) k hk
    rwa [← Finset.prod_mul_distrib, Finset.prod_eq_one fun i _ => mul_inv_cancel₀ (hc i),
      hkdet] at this
  have hd' := galoisAut_mem_adelicCompletionOfElementSet F c (algEquiv_mem_one F c) hd
  have hw : ∀ a, (Q *ᵥ z) a ∈ hat1 F (cI a : Set E) := by
    rw [← key', Matrix.mulVec_mulVec, hPQ, Matrix.one_mulVec]
    exact hz
  have hu : P *ᵥ (sg (FiniteAdeleRing (𝓞 F) F) c G.det • k.cramer (Q *ᵥ z)) ∈
      hat F (L : Set (Fin n → E)) := by
    rw [key']
    intro a
    have := (adelicCompletion_fractionalIdeal_properties F E).1 1 (cI a) _ hd' _ (cramer_mem_adelicCompletionOfElementSet F cI hc k hk _ hw a)
    rwa [one_mul] at this
  have hz' : G *ᵥ (P *ᵥ (sg (FiniteAdeleRing (𝓞 F) F) c G.det • k.cramer (Q *ᵥ z))) = z := by
    rw [Matrix.mulVec_mulVec, ← hPk, ← Matrix.mulVec_mulVec, Matrix.mulVec_smul,
      Matrix.mulVec_cramer, smul_smul, hkdet, mul_comm, hdet, one_smul, Matrix.mulVec_mulVec, hPQ,
      Matrix.one_mulVec]
  rw [← hz', Matrix.mulVec_mulVec, hG, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mulVec]
  exact hu

end GlobalTheory.AdLat
end

section

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors

theorem _root_.GlobalTheory.T.mem_adelicCompletion_pseudoBasis_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (e : Module.Basis (Fin n) E (Fin n → E)) (cI : Fin n → FractionalIdeal (𝓞 E)⁰ E), (∀ v, v ∈ L ↔ ∀ a, e.repr v a ∈ cI a) → ∀ z : Fin n → RA F E, (∑ a, z a • fv F (e a)) ∈ (hat F (L : Set (Fin n → E))) ↔ ∀ a, z a ∈ hat1 F (cI a : Set E) := by
  first | exact @GlobalTheory.AdLat.mem_hat_pseudoBasis_iff | exact GlobalTheory.AdLat.mem_hat_pseudoBasis_iff | (intros; apply GlobalTheory.AdLat.mem_hat_pseudoBasis_iff <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ReducedSubgroup

section Cat

variable {𝒞 : Type*} [Category 𝒞] [CartesianMonoidalCategory 𝒞]

theorem exists_grpObj_of_mono {N B : 𝒞} [GrpObj B] (ν : N ⟶ B) [Mono ν] (e : 𝟙_ 𝒞 ⟶ N)
    (m : N ⊗ N ⟶ N) (i : N ⟶ N) (he : e ≫ ν = η[B]) (hm : m ≫ ν = (ν ⊗ₘ ν) ≫ μ[B])
    (hi : i ≫ ν = ν ≫ GrpObj.inv) : ∃ _ : GrpObj N, IsMonHom ν := by
  have hl : ∀ {T : 𝒞} (a b : T ⟶ N), lift a b ≫ m ≫ ν = (a ≫ ν) * (b ≫ ν) := by
    intro T a b
    rw [hm, lift_map_assoc, Hom.mul_def]
  have hm' : m ≫ ν = (fst N N ≫ ν) * (snd N N ≫ ν) := by
    rw [← hl, lift_fst_snd, Category.id_comp]
  have he' : ∀ {T : 𝒞} (a : T ⟶ 𝟙_ 𝒞), a ≫ e ≫ ν = 1 := by
    intro T a
    rw [he, Hom.one_def, toUnit_unique a (toUnit T)]
  have hi' : i ≫ ν = ν⁻¹ := by rw [hi, Hom.inv_def]
  letI M : MonObj N :=
    { one := e
      mul := m
      one_mul := by
        rw [← cancel_mono ν, Category.assoc, hm', comp_mul, whiskerRight_fst_assoc,
          whiskerRight_snd_assoc, he', _root_.one_mul, leftUnitor_hom]
      mul_one := by
        rw [← cancel_mono ν, Category.assoc, hm', comp_mul, whiskerLeft_fst_assoc,
          whiskerLeft_snd_assoc, he', _root_.mul_one, rightUnitor_hom]
      mul_assoc := by
        rw [← cancel_mono ν]
        simp only [Category.assoc]
        conv_lhs => rw [hm', comp_mul, whiskerRight_fst_assoc, whiskerRight_snd_assoc, hm',
          comp_mul]
        conv_rhs => rw [hm', comp_mul, whiskerLeft_fst_assoc, whiskerLeft_snd_assoc, hm',
          comp_mul, comp_mul, comp_mul]
        simp [_root_.mul_assoc] }
  refine ⟨{ inv := i, left_inv := ?_, right_inv := ?_ }, ⟨he, hm⟩⟩
  · rw [← cancel_mono ν, Category.assoc, Category.assoc]
    exact (hl i (𝟙 N)).trans (by rw [hi', Category.id_comp, inv_mul_cancel]; exact (he' _).symm)
  · rw [← cancel_mono ν, Category.assoc, Category.assoc]
    exact (hl (𝟙 N) i).trans (by rw [hi', Category.id_comp, mul_inv_cancel]; exact (he' _).symm)

end Cat

section Reduced

universe u


open Scheme.IdealSheafData in
theorem isReduced_subscheme_vanishingIdeal {X : Scheme.{u}} (Z : TopologicalSpace.Closeds X) :
    IsReduced (vanishingIdeal Z).subscheme := by
  have : ∀ U, IsReduced ((vanishingIdeal Z).subschemeCover.openCover.X U) := fun U => by
    refine (affine_isReduced_iff (.of (Γ(X, U.1) ⧸ (vanishingIdeal Z).ideal U))).mpr ?_
    refine (Ideal.isRadical_iff_quotient_reduced _).mp ?_
    exact PrimeSpectrum.isRadical_vanishingIdeal _
  exact IsReduced.of_openCover _ (vanishingIdeal Z).subschemeCover.openCover


open Scheme.IdealSheafData in
theorem vanishingIdeal_le_ker {T X : Scheme.{u}} [IsReduced T] (g : T ⟶ X)
    (Z : TopologicalSpace.Closeds X) (h : Set.range g ⊆ Z) : vanishingIdeal Z ≤ g.ker := by
  refine le_ofIdeals_iff.mpr fun U a ha => ?_
  rw [RingHom.mem_ker, ← basicOpen_eq_bot_iff, ← Scheme.preimage_basicOpen, eq_bot_iff]
  intro t ht
  have h1 : g t ∈ (vanishingIdeal Z).support := h ⟨t, rfl⟩
  have h2 := ((coe_support_inter (vanishingIdeal Z) U).le
    ⟨h1, X.basicOpen_le a ht⟩).1
  exact ((Scheme.mem_zeroLocus_iff _ _ _).mp h2 a ha ht).elim

theorem geometricallyReduced_of_perfectField {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} [IsReduced X] (f : X ⟶ Spec (.of k)) : GeometricallyReduced f := by
  refine ⟨geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms.mpr fun K _ _ => ?_⟩
  let 𝒰 := Scheme.Pullback.openCoverOfLeft X.affineOpenCover.openCover f
    (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  have : ∀ i, IsReduced (𝒰.X i) := fun i => by
    have := X.affineOpenCover.map_prop i
    have h0 : IsReduced (Spec (X.affineOpenCover.X i)) :=
      isReduced_of_isOpenImmersion (X.affineOpenCover.f i)
    have h1 := (affine_isReduced_iff _).mp h0
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.affineOpenCover.f i ≫ f)
    change IsReduced (pullback (X.affineOpenCover.f i ≫ f) _)
    rw [← hφ]
    letI : Algebra k (X.affineOpenCover.X i) := φ.hom.toAlgebra
    have h2 := ReducedAlg.isReduced_tensor (k := k) (X.affineOpenCover.X i) K
    have h3 := (affine_isReduced_iff
      (.of (TensorProduct k (X.affineOpenCover.X i) K))).mpr h2
    exact isReduced_of_isOpenImmersion (pullbackSpecIso k (X.affineOpenCover.X i) K).hom
  exact IsReduced.of_openCover _ 𝒰

end Reduced

theorem range_subset_of_points {k : Type} [Field k] [IsAlgClosed k] {T B : Over (Sp k)}
    [LocallyOfFiniteType T.hom] (g : T ⟶ B) {Z : Set B.left} (hZ : IsClosed Z)
    (h : ∀ x : 𝟙_ (Over (Sp k)) ⟶ T, Set.range (x ≫ g).left ⊆ Z) : Set.range g.left ⊆ Z := by
  have := LocallyOfFiniteType.jacobsonSpace T.hom
  rintro _ ⟨t, rfl⟩
  by_contra ht
  obtain ⟨x, hx, hxc⟩ := nonempty_inter_closedPoints (Z := (g.left ⁻¹' Z)ᶜ) ⟨t, ht⟩
    (hZ.preimage g.left.continuous).isOpen_compl.isLocallyClosed
  let x' : 𝟙_ (Over (Sp k)) ⟶ T :=
    Over.homMk (pointOfClosedPoint T.hom x hxc) (pointOfClosedPoint_comp T.hom x hxc)
  refine hx (h x' ⟨IsLocalRing.closedPoint k, ?_⟩)
  exact congrArg g.left (pointOfClosedPoint_apply T.hom x hxc _)


open Scheme.IdealSheafData in
theorem exists_smooth_closed_subgroup (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k))
    [GrpObj B] (hB : LocallyOfFiniteType B.hom) (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ B))
    (Z : Set B.left) (hZ : IsClosed Z) (hC : ∀ x, x ∈ C ↔ Set.range x.left ⊆ Z) :
    ∃ (N : Over (Sp k)) (_ : GrpObj N) (ν : N ⟶ B), IsMonHom ν ∧ IsClosedImmersion ν.left ∧
      Smooth N.hom ∧ Set.range ν.left = Z := by
  let I : B.left.IdealSheafData := vanishingIdeal ⟨Z, hZ⟩
  let N : Over (Sp k) := Over.mk (I.subschemeι ≫ B.hom)
  let ν : N ⟶ B := Over.homMk I.subschemeι rfl
  have hν : IsClosedImmersion ν.left := inferInstanceAs (IsClosedImmersion I.subschemeι)
  have hr : Set.range ν.left = Z := by
    change Set.range I.subschemeι = Z
    rw [range_subschemeι]
    rfl
  have : Mono ν := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono ν.left))
  have hred : IsReduced N.left := isReduced_subscheme_vanishingIdeal _
  have hft : LocallyOfFiniteType N.hom :=
    inferInstanceAs (LocallyOfFiniteType (I.subschemeι ≫ B.hom))
  have hgr : GeometricallyReduced N.hom := geometricallyReduced_of_perfectField N.hom
  have hnoeth : IsLocallyNoetherian N.left := LocallyOfFiniteType.isLocallyNoetherian N.hom
  have hlift : ∀ {T : Over (Sp k)} [IsReduced T.left] [LocallyOfFiniteType T.hom] (g : T ⟶ B),
      (∀ x : 𝟙_ (Over (Sp k)) ⟶ T, x ≫ g ∈ C) → ∃ l : T ⟶ N, l ≫ ν = g := by
    intro T _ _ g hg
    have h1 := range_subset_of_points g hZ fun x => (hC _).mp (hg x)
    have h2 : I.subschemeι.ker ≤ g.left.ker := by
      rw [ker_subschemeι]
      exact vanishingIdeal_le_ker g.left ⟨Z, hZ⟩ h1
    have h3 := IsClosedImmersion.lift_fac I.subschemeι g.left h2
    refine ⟨Over.homMk (IsClosedImmersion.lift I.subschemeι g.left h2) ?_, ?_⟩
    · change _ ≫ I.subschemeι ≫ B.hom = _
      rw [← Category.assoc, h3, Over.w]
    · ext1
      exact h3
  have hmem : ∀ x : 𝟙_ (Over (Sp k)) ⟶ N, x ≫ ν ∈ C := fun x => by
    rw [hC, ← hr]
    rintro _ ⟨t, rfl⟩
    exact ⟨x.left t, rfl⟩
  have : IsReduced (𝟙_ (Over (Sp k))).left := inferInstanceAs (IsReduced (Sp k))
  have : LocallyOfFiniteType (𝟙_ (Over (Sp k))).hom :=
    inferInstanceAs (LocallyOfFiniteType (𝟙 (Sp k)))
  have : IsReduced (N ⊗ N).left := inferInstanceAs (IsReduced (pullback N.hom N.hom))
  have : LocallyOfFiniteType (N ⊗ N).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.fst N.hom N.hom ≫ N.hom))
  obtain ⟨e, he⟩ := hlift η[B] fun x => by
    rw [toUnit_unique x (toUnit _), ← Hom.one_def]
    exact C.one_mem
  obtain ⟨m, hm⟩ := hlift ((ν ⊗ₘ ν) ≫ μ[B]) fun x => by
    have : x ≫ (ν ⊗ₘ ν) ≫ μ[B] = ((x ≫ fst N N) ≫ ν) * ((x ≫ snd N N) ≫ ν) := by
      rw [Hom.mul_def, ← lift_map, Category.assoc, ← comp_lift, lift_fst_snd, Category.comp_id]
    rw [this]
    exact C.mul_mem (hmem _) (hmem _)
  obtain ⟨i, hi⟩ := hlift (ν ≫ GrpObj.inv) fun x => by
    rw [← Category.assoc, ← Hom.inv_def]
    exact C.inv_mem (hmem _)
  obtain ⟨G, hG⟩ := exists_grpObj_of_mono ν e m i he hm hi
  refine ⟨N, G, ν, hG, hν, ?_, hr⟩
  letI : GrpObj (Over.mk N.hom) := G
  exact smooth_of_grpObj N.hom

end GlobalTheory.ReducedSubgroup
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem isDominant_spMap_of_isFractionRing (T K : Type) [CommRing T] [IsDomain T] [Field K]
    [Algebra T K] [IsFractionRing T K] : IsDominant (spMap (algebraMap T K)) := by
  refine ⟨?_⟩
  change DenseRange (PrimeSpectrum.comap (algebraMap T K))
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
    (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective T K)]
  exact bot_le

theorem isDominant_genericFibre_of_flat (T K : Type) [CommRing T] [IsDomain T] [Field K]
    [Algebra T K] [IsFractionRing T K] {X : Scheme.{0}} (f : X ⟶ Sp T) [Flat f] :
    IsDominant (pullback.fst f (spMap (algebraMap T K))) := by
  have := isDominant_spMap_of_isFractionRing T K
  have := IsSchemeTheoreticallyDominant.of_isDominant (spMap (algebraMap T K))
  infer_instance

theorem connectedSpace_of_flat_of_genericFibre (T K : Type) [CommRing T] [IsDomain T] [Field K]
    [Algebra T K] [IsFractionRing T K] {X : Scheme.{0}} (f : X ⟶ Sp T) [Flat f]
    [ConnectedSpace ↥(pullback f (spMap (algebraMap T K)))] : ConnectedSpace X := by
  have := isDominant_genericFibre_of_flat T K f
  let g := pullback.fst f (spMap (algebraMap T K))
  have h : _root_.IsConnected (closure (Set.range g)) := (isConnected_range g.continuous).closure
  rw [g.denseRange.closure_range] at h
  exact connectedSpace_iff_univ.mpr h

theorem isIntegral_and_isNormalScheme_of_smooth (T K : Type) [CommRing T] [IsDomain T]
    [IsNoetherianRing T] [IsIntegrallyClosed T] [Field K] [Algebra T K] [IsFractionRing T K]
    {X : Scheme.{0}} (f : X ⟶ Sp T) [Smooth f]
    [ConnectedSpace ↥(pullback f (spMap (algebraMap T K)))] :
    IsIntegral X ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X := by
  have hT : GlobalTheory.IsNormalScheme (Sp T) := inferInstance
  have hX : GlobalTheory.IsNormalScheme X := (isNormalScheme_iff X).mpr
    (forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth f ((isNormalScheme_iff _).mp hT))
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have := connectedSpace_of_flat_of_genericFibre T K f
  exact ⟨IsNormalScheme.isIntegral_of_connectedSpace X, hX.pred X⟩

theorem isIntegral_and_isNormalScheme_of_smooth_dvr :
    ∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K]
      [IsFractionRing T K] (G : Over (Sp T)), Smooth G.hom →
      ConnectedSpace ((Over.pullback (spMap (algebraMap T K))).obj G).left →
      IsIntegral G.left ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme G.left := by
  intro T K _ _ _ _ _ _ G hG hc
  have : ConnectedSpace ↥(pullback G.hom (spMap (algebraMap T K))) := hc
  exact isIntegral_and_isNormalScheme_of_smooth T K G.hom

end GlobalTheory
end

section

open MeasureTheory Topology Matrix
open scoped ENNReal

theorem _root_.GlobalTheory.T.lintegral_unfold_arithmetic_quotient_doubleCosets : ∀ (G : Type) [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] (Γ H Kf : Subgroup G) [Countable Γ] (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → μ 𝓕 ≠ 0 → μ 𝓕 ≠ ⊤ → MeasurableSet (H : Set G) → Kf ≤ H → ∀ (ι : Type) [Fintype ι] (R : ι → Type) [∀ k, Group (R k)] [∀ k, TopologicalSpace (R k)] [∀ k, IsTopologicalGroup (R k)] [∀ k, T2Space (R k)] [∀ k, LocallyCompactSpace (R k)] [∀ k, SecondCountableTopology (R k)] [∀ k, MeasurableSpace (R k)] [∀ k, BorelSpace (R k)] (ν : ∀ k, Measure (R k)) [∀ k, (ν k).IsHaarMeasure] (ψ : ∀ k, G →* R k) (Λ : ∀ k, Subgroup (R k)) (s : ∀ k, R k) (g : ι → G) (P : Type) (Q : P → P → Prop) (dict : G → P) (pt : ∀ k, R k → P), (∀ k, Measurable (ψ k)) → (∀ k t, ∃ h ∈ H, ψ k h = t) → (∀ k, ∀ z ∈ Kf, ψ k z = 1) → (∀ k, ∀ γ ∈ Γ, ψ k γ = 1 → γ = 1) → (∀ k k', ∃ (e : R k ≃ᵐ R k') (α : R k → R k) (u : R k), MeasurePreserving e (ν k) (ν k') ∧ Measurable α ∧ (∀ x, ψ k' x = e (α (ψ k x))) ∧ ∀ t, α (α t) = u⁻¹ * t * u) → (∀ k, ∃ W ∈ 𝓝 (1 : R k), ∀ w ∈ Λ k, w ∈ W → w = 1) → Equivalence Q → (∀ x x', Q (dict x) (dict x') ↔ ∃ γ ∈ Γ, ∃ z ∈ Kf, x' = γ * x * z) → (∀ k, ∀ h ∈ H, Q (dict (g k * h)) (pt k (s k * ψ k h))) → (∀ x, ∃ k t, Q (dict x) (pt k t)) → (∀ k k' t t', Q (pt k t) (pt k' t') → k = k') → (∀ k t t', Q (pt k t) (pt k t') ↔ ∃ w ∈ Λ k, t' = w * t) → ∃ (κ : ℝ≥0∞) (D : ∀ k, Set (R k)), κ ≠ 0 ∧ κ ≠ ⊤ ∧ (∀ k, Countable (Λ k) ∧ IsFundamentalDomain (Λ k) (D k) (ν k)) ∧ ∀ Φ : P → ℝ≥0∞, (∀ x q, Q (dict x) q → Φ q = Φ (dict x)) → (∀ k, Measurable fun t => Φ (pt k t)) → Measurable (fun x => Φ (dict x)) ∧ ∫⁻ x in 𝓕, Φ (dict x) ∂μ = κ * ∑ k, ∫⁻ t in D k, Φ (pt k t) ∂(ν k) := by
  first | exact @GlobalTheory.PeterssonUnfold.unfold_lintegral | exact GlobalTheory.PeterssonUnfold.unfold_lintegral | (intros; apply GlobalTheory.PeterssonUnfold.unfold_lintegral <;> assumption)
end

section

open MeasureTheory

theorem _root_.GlobalTheory.T.invariant_probability_lattice_quotient_unique : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsHaarMeasure] (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → μ 𝓕 ≠ ⊤ → ∀ (ν : Measure (Quotient (QuotientGroup.rightRel Γ))) [IsProbabilityMeasure ν], (∀ (h : G) (ρ : Quotient (QuotientGroup.rightRel Γ) → Quotient (QuotientGroup.rightRel Γ)), (∀ g : G, ρ (Quotient.mk _ g) = Quotient.mk _ (g * h)) → ∀ s, MeasurableSet s → ν (ρ ⁻¹' s) = ν s) → ν = (μ 𝓕)⁻¹ • (μ.restrict 𝓕).map (fun g : G => (Quotient.mk _ g : Quotient (QuotientGroup.rightRel Γ))) := by
  first | exact @GlobalTheory.LatticeQuotUniq.invariant_prob_eq | exact GlobalTheory.LatticeQuotUniq.invariant_prob_eq | (intros; apply GlobalTheory.LatticeQuotUniq.invariant_prob_eq <;> assumption)
end
