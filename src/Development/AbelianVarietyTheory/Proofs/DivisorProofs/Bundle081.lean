module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Eigenspace.Basic

@[expose] public section

section

open Polynomial

namespace GlobalTheory

theorem exists_integral_domain_extension_monic_roots :
    ∀ (D : Type) [CommRing D] [IsDomain D], ∃ (C : Type) (_ : CommRing C) (_ : Algebra D C),
      IsDomain C ∧ Algebra.IsIntegral D C ∧ Function.Injective (algebraMap D C) ∧
      (∀ f : C[X], f.Monic → 0 < f.natDegree → ∃ y : C, f.eval y = 0) ∧
      ∀ (K : Type) [Field K] [IsAlgClosed K] (h : D →+* K), Function.Injective h →
        ∃ e : C →+* K, Function.Injective e ∧ e.comp (algebraMap D C) = h := by
  intro D _ _
  have hDL : Function.Injective (algebraMap D (AlgebraicClosure (FractionRing D))) := by
    rw [IsScalarTower.algebraMap_eq D (FractionRing D) (AlgebraicClosure (FractionRing D))]
    exact (algebraMap (FractionRing D) (AlgebraicClosure (FractionRing D))).injective.comp
      (IsFractionRing.injective D (FractionRing D))
  have hCL : Function.Injective (algebraMap (integralClosure D (AlgebraicClosure (FractionRing D)))
      (AlgebraicClosure (FractionRing D))) := Subtype.val_injective
  refine ⟨integralClosure D (AlgebraicClosure (FractionRing D)), inferInstance, inferInstance,
    inferInstance, inferInstance, ?_, ?_, ?_⟩
  · intro a b hab
    apply hDL
    simpa using congrArg Subtype.val hab
  · intro f hf hdeg
    have hdeg' : (f.map (algebraMap (integralClosure D (AlgebraicClosure (FractionRing D)))
        (AlgebraicClosure (FractionRing D)))).degree ≠ 0 := by
      rw [degree_map_eq_of_injective hCL, degree_eq_natDegree hf.ne_zero]
      exact_mod_cast hdeg.ne'
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_root _ hdeg'
    have hy' : f.eval₂ (algebraMap (integralClosure D (AlgebraicClosure (FractionRing D)))
        (AlgebraicClosure (FractionRing D))) y = 0 := by rwa [IsRoot, eval_map] at hy
    have hyC : IsIntegral (integralClosure D (AlgebraicClosure (FractionRing D))) y :=
      ⟨f, hf, hy'⟩
    have hyD : IsIntegral D y := isIntegral_trans y hyC
    refine ⟨⟨y, hyD⟩, ?_⟩
    apply hCL
    rw [← eval₂_at_apply, map_zero]
    exact hy'
  · intro K _ _ h hinj
    letI : Algebra (FractionRing D) K := (IsFractionRing.lift hinj : FractionRing D →+* K).toAlgebra
    let φ : AlgebraicClosure (FractionRing D) →ₐ[FractionRing D] K := (by
      refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
      solve_by_elim* (maxDepth := 2) only [*,
        @_root_.DivisionSemiring.to_moduleIsTorsionFree,
        @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
    refine ⟨φ.toRingHom.comp (integralClosure D (AlgebraicClosure (FractionRing D))).val.toRingHom,
      φ.toRingHom.injective.comp Subtype.val_injective, ?_⟩
    ext a
    show φ (algebraMap D (AlgebraicClosure (FractionRing D)) a) = h a
    rw [IsScalarTower.algebraMap_apply D (FractionRing D) (AlgebraicClosure (FractionRing D)),
      AlgHom.commutes]
    exact IsFractionRing.lift_algebraMap hinj a

end GlobalTheory
end

section

namespace GlobalTheory

open MvPolynomial

theorem exists_isAlgClosed_embeddings_of_family :
    ∀ (F : Type) [Field F] (I : Type) (k : I → Type) [∀ i, Field (k i)] (f : ∀ i, F →+* k i),
      ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (g : ∀ i, k i →+* L) (h : F →+* L),
        ∀ i, (g i).comp (f i) = h := by
  intro F _ I k _ f
  let K := FractionRing (MvPolynomial (Σ i, k i) F)
  let Ω := AlgebraicClosure K
  have key : ∀ i, ∃ g : k i →+* Ω, g.comp (f i) = algebraMap F Ω := by
    intro i
    letI : Algebra F (k i) := (f i).toAlgebra
    obtain ⟨s, hs⟩ := exists_isTranscendenceBasis F (k i)
    let x : (Σ i, k i) → Ω := fun j => algebraMap K Ω (algebraMap (MvPolynomial (Σ i, k i) F) K (X j))
    have hx : AlgebraicIndependent F x := by
      have h0 := MvPolynomial.algebraicIndependent_X (Σ i, k i) F
      have h1 : Function.Injective (IsScalarTower.toAlgHom F (MvPolynomial (Σ i, k i) F) K) :=
        IsFractionRing.injective _ _
      have h2 : Function.Injective (IsScalarTower.toAlgHom F K Ω) :=
        (algebraMap K Ω).injective
      have := (h0.map' h1).map' h2
      exact this
    have hv : AlgebraicIndependent F (fun b : s => x ⟨i, b.1⟩) :=
      hx.comp (fun b : s => (⟨i, b.1⟩ : Σ i, k i)) (by
        intro a b hab
        exact Subtype.ext (by simpa using hab))
    let φ0 : IntermediateField.adjoin F (Set.range ((↑) : s → k i)) →ₐ[F] Ω :=
      (IntermediateField.val _).comp (hv.aevalEquivField.toAlgHom.comp hs.1.reprField)
    have halg := hs.isAlgebraic_field
    obtain ⟨φ, -⟩ := IntermediateField.exists_algHom_of_splits' φ0
      (fun (y : k i) => ⟨(Algebra.IsAlgebraic.isAlgebraic
        (R := IntermediateField.adjoin F (Set.range ((↑) : s → k i))) y).isIntegral,
        IsAlgClosed.splits _⟩)
    refine ⟨φ.toRingHom, ?_⟩
    ext y
    exact φ.commutes y
  choose g hg using key
  exact ⟨Ω, inferInstance, inferInstance, g, algebraMap F Ω, hg⟩

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory
namespace NoCommonZeroSpread

lemma exists_common_denominator {A Ω : Type} [CommRing A] [Field Ω] (φ : A →+* Ω)
    (S : Finset Ω) (hS : ∀ x ∈ S, x ∈ Subfield.closure (φ.range : Set Ω)) :
    ∃ b : A, φ b ≠ 0 ∧ ∀ x ∈ S, φ b * x ∈ Set.range φ := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, by simp, by simp⟩
  | insert x S hx ih =>
    obtain ⟨b, hb, hbS⟩ := ih (fun y hy => hS y (Finset.mem_insert_of_mem hy))
    have hxK := hS x (Finset.mem_insert_self x S)
    rw [Subfield.mem_closure_iff, Subring.closure_eq] at hxK
    obtain ⟨y, hy, z, hz, hyz⟩ := hxK
    obtain ⟨a, rfl⟩ := RingHom.mem_range.1 hy
    obtain ⟨c, rfl⟩ := RingHom.mem_range.1 hz
    by_cases hc : φ c = 0
    · have hx0 : x = 0 := by rw [← hyz, hc, div_zero]
      refine ⟨b, hb, fun w hw => ?_⟩
      rcases Finset.mem_insert.1 hw with h | h
      · exact ⟨0, by rw [h, hx0, mul_zero, map_zero]⟩
      · exact hbS w h
    · refine ⟨b * c, by simp [hb, hc], fun w hw => ?_⟩
      rcases Finset.mem_insert.1 hw with h | h
      · refine ⟨b * a, ?_⟩
        rw [h, ← hyz, map_mul, map_mul]
        field_simp
      · obtain ⟨d, hd⟩ := hbS w h
        refine ⟨d * c, ?_⟩
        rw [map_mul, hd, map_mul]
        ring

theorem no_common_zero_spreads : ∀ (A : Type) [CommRing A] (τ J : Type) [Finite τ] (F : J → MvPolynomial τ A) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (φ : A →+* Ω), (¬ ∃ z : τ → Ω, ∀ j, MvPolynomial.eval₂ φ z (F j) = 0) → ∃ (a : A) (I : Finset A), φ a ≠ 0 ∧ (∀ c ∈ I, φ c = 0) ∧ ∀ (k : Type) [Field k] (ψ : A →+* k), ψ a ≠ 0 → (∀ c ∈ I, ψ c = 0) → ¬ ∃ z : τ → k, ∀ j, MvPolynomial.eval₂ ψ z (F j) = 0 := by
  intro A _ τ J _ F Ω _ _ φ hno
  classical
  let G : J → MvPolynomial τ Ω := fun j => MvPolynomial.map φ (F j)

  have h1 : (1 : MvPolynomial τ Ω) ∈ Ideal.span (Set.range G) := by
    have hz : MvPolynomial.zeroLocus Ω (Ideal.span (Set.range G)) = ∅ := by
      ext x
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hx
      apply hno
      refine ⟨x, fun j => ?_⟩
      have := hx (G j) (Ideal.subset_span ⟨j, rfl⟩)
      simpa [G, MvPolynomial.coe_aeval_eq_eval, MvPolynomial.eval_map] using this
    have := MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := Ω) (Ideal.span (Set.range G))
    rw [hz, MvPolynomial.vanishingIdeal_empty, eq_comm, Ideal.radical_eq_top] at this
    rw [this]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 h1

  let K : Subfield Ω := Subfield.closure (φ.range : Set Ω)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K Ω)
    (LinearMap.ker_eq_bot.2 (algebraMap K Ω).injective)
  have hg1 : ∀ y : K, g (y : Ω) = y := fun y => by
    exact LinearMap.congr_fun hg y
  have hgK : ∀ (x : Ω) (y : K), ((g (x * y) : K) : Ω) = (g x : Ω) * y := by
    intro x y
    have : x * (y : Ω) = y • x := by rw [mul_comm]; rfl
    rw [this, map_smul, smul_eq_mul, Subfield.coe_mul, mul_comm]
  have hφK : ∀ a : A, φ a ∈ K := fun a => Subfield.subset_closure (RingHom.mem_range_self φ a)
  let P : MvPolynomial τ Ω → MvPolynomial τ Ω := fun h =>
    ∑ m ∈ h.support, MvPolynomial.monomial m ((g (h.coeff m) : K) : Ω)
  have hPc : ∀ h n, (P h).coeff n = ((g (h.coeff n) : K) : Ω) := by
    intro h n
    simp only [P, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    rw [Finset.sum_ite_eq']
    split_ifs with hn
    · rfl
    · rw [MvPolynomial.notMem_support_iff.1 hn]; simp
  have hPadd : ∀ h₁ h₂, P (h₁ + h₂) = P h₁ + P h₂ := by
    intro h₁ h₂; ext n; simp [hPc, MvPolynomial.coeff_add]
  have hP1 : P 1 = 1 := by
    ext n
    rw [hPc, MvPolynomial.coeff_one]
    split_ifs
    · have := hg1 1; simpa using this
    · simp
  have hPmul : ∀ h j, P (h * G j) = P h * G j := by
    intro h j; ext n

    rw [hPc, MvPolynomial.coeff_mul, MvPolynomial.coeff_mul, map_sum]
    refine (map_sum K.subtype _ _).trans (Finset.sum_congr rfl fun x _ => ?_)
    show ((g _ : K) : Ω) = _
    have e : (G j).coeff x.2 = ((⟨φ ((F j).coeff x.2), hφK _⟩ : K) : Ω) := by
      simp [G, MvPolynomial.coeff_map]
    rw [e, hgK, hPc]
  let PA : MvPolynomial τ Ω →+ MvPolynomial τ Ω := AddMonoidHom.mk' P hPadd
  have hsum : ∑ j ∈ c.support, P (c j) * G j = 1 := by
    simp only [Finsupp.sum, smul_eq_mul] at hc
    have := congrArg PA hc

    rw [map_sum] at this
    simp only [PA, AddMonoidHom.mk'_apply] at this
    rw [← hP1]
    convert this using 1
    refine Finset.sum_congr rfl fun j _ => ?_
    exact (hPmul _ _).symm

  let S : Finset Ω := c.support.biUnion (fun j => (P (c j)).coeffs)
  obtain ⟨b, hb, hbS⟩ := exists_common_denominator φ S (by
    intro x hx
    obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 hx
    obtain ⟨n, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.1 hj
    rw [hPc]; exact (g _).2)
  have hQ : ∀ j, ∃ q : MvPolynomial τ A,
      MvPolynomial.map φ q = MvPolynomial.C (φ b) * P (c j) := by
    intro j
    have : MvPolynomial.C (φ b) * P (c j) ∈ Set.range (MvPolynomial.map (σ := τ) φ) := by
      rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
      intro y hy
      obtain ⟨n, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.1 (Finset.mem_coe.1 hy)
      rw [MvPolynomial.coeff_C_mul]
      by_cases hn : (P (c j)).coeff n = 0
      · rw [hn, mul_zero]; exact ⟨0, map_zero φ⟩
      · have hj : j ∈ c.support := by
          rw [Finsupp.mem_support_iff]
          intro h0; apply hn; rw [hPc, h0]; simp
        exact hbS _ (Finset.mem_biUnion.2 ⟨j, hj,
          MvPolynomial.mem_coeffs_iff.2 ⟨n, MvPolynomial.mem_support_iff.2 hn, rfl⟩⟩)
    exact this
  choose q hq using hQ
  let E : MvPolynomial τ A := MvPolynomial.C b - ∑ j ∈ c.support, q j * F j
  have hE : MvPolynomial.map φ E = 0 := by
    have hG : ∀ j, MvPolynomial.map φ (F j) = G j := fun j => rfl

    simp only [E, map_sub, map_sum, map_mul, MvPolynomial.map_C, hq, hG, _root_.mul_assoc]
    rw [← Finset.mul_sum, hsum, _root_.mul_one, sub_self]
  refine ⟨b, E.coeffs, hb, ?_, ?_⟩
  · intro y hy
    obtain ⟨n, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.1 hy
    have := congrArg (AddMonoidAlgebra.coeff · n) hE
    rwa [MvPolynomial.coeff_map, MvPolynomial.coeff_zero] at this
  · intro k _ ψ hψb hψI ⟨z, hz⟩
    have h0 : MvPolynomial.map ψ E = 0 := by
      ext n
      rw [MvPolynomial.coeff_map, MvPolynomial.coeff_zero]
      by_cases hn : n ∈ E.support
      · exact hψI _ (MvPolynomial.mem_coeffs_iff.2 ⟨n, hn, rfl⟩)
      · rw [MvPolynomial.notMem_support_iff.1 hn, map_zero]
        rfl
    have h2 : MvPolynomial.eval₂ ψ z E = 0 := by
      rw [MvPolynomial.eval₂_eq_eval_map, h0, map_zero]
    have h3 : MvPolynomial.eval₂ ψ z E = ψ b := by
      simp [E, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_C, MvPolynomial.eval₂_sum,
        MvPolynomial.eval₂_mul, hz]
    exact hψb (h3 ▸ h2)

end NoCommonZeroSpread
end GlobalTheory
end

section

universe u_1 u_2

namespace GlobalTheory.IrreducibleMembership

theorem mem_of_irreducible {K : Type u_1} {V : Type u_2} [Field K] [IsAlgClosed K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (S : Subalgebra K (Module.End K V))
    (h : ∀ N : Submodule K V, (∀ f ∈ S, ∀ v ∈ N, (f : V → V) v ∈ N) → N = ⊥ ∨ N = ⊤)
    (f : Module.End K V) : f ∈ S := by
  classical
  rcases subsingleton_or_nontrivial V with hV | hV
  · have hf1 : f = 1 := LinearMap.ext fun v => Subsingleton.elim _ _
    rw [hf1]
    exact S.one_mem
  · have hso : IsSimpleOrder (Submodule S V) := by
      refine ⟨fun N => ?_⟩
      have hN := h (N.restrictScalars K) fun g hg v hv => by
        have hmem : (⟨g, hg⟩ : S) • v ∈ N := N.smul_mem _ hv
        exact hmem
      rcases hN with hN | hN
      · left
        exact (Submodule.restrictScalars_eq_bot_iff K S V).1 hN
      · right
        exact (Submodule.restrictScalars_eq_top_iff K S V).1 hN
    have hsimp : IsSimpleModule S V := ⟨⟩
    have hbij := IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed (A := S) (V := V) K
    let F : Module.End (Module.End S V) V :=
      { toFun := f
        map_add' := f.map_add
        map_smul' := fun g v => by
          obtain ⟨c, hc⟩ := hbij.2 g
          rw [← hc]
          simp }
    let b := Module.finBasis K V
    obtain ⟨r, hr⟩ := jacobson_density F (Finset.univ.image b)
    have hfr : f = (r : Module.End K V) := by
      refine b.ext fun i => ?_
      have := hr (b i) (Finset.mem_image_of_mem b (Finset.mem_univ i))
      exact this
    rw [hfr]
    exact r.2

end GlobalTheory.IrreducibleMembership
end

section

open MeasureTheory Matrix
open scoped Classical

namespace GlobalTheory.CentSep

theorem apply_basis_eq_smul {L V κ : Type} [Field L] [AddCommGroup V] [Module L V]
    (b : Module.Basis κ L V) (μ : κ → L) (hμ : Function.Injective μ)
    (f g : Module.End L V) (hf : ∀ k, f (b k) = μ k • b k) (hg : g ∘ₗ f = f ∘ₗ g) (k : κ) :
    ∃ c : L, g (b k) = c • b k := by
  refine ⟨b.repr (g (b k)) k, ?_⟩
  set x := g (b k) with hx
  have hfx : f x = μ k • x := by
    have := congrArg (fun φ : Module.End L V => φ (b k)) hg
    simp only [LinearMap.comp_apply, hf] at this
    rw [hx, ← this, map_smul]
  have hrep : ∀ y : V, ∀ j, b.repr (f y) j = μ j * b.repr y j := by
    intro y j
    have key : (b.coord j).comp f = μ j • b.coord j := by
      refine b.ext fun i => ?_
      simp only [LinearMap.comp_apply, hf, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self,
        LinearMap.smul_apply, smul_eq_mul, Finsupp.single_apply]
      split_ifs with h
      · subst h; rfl
      · simp
    exact congrArg (fun φ : V →ₗ[L] L => φ y) key
  apply b.ext_elem
  intro j
  by_cases hj : j = k
  · subst hj; simp
  · have h1 := hrep x j
    rw [hfx, map_smul, Finsupp.smul_apply, smul_eq_mul] at h1
    have h0 : b.repr x j = 0 := by
      have h2 : (μ j - μ k) * b.repr x j = 0 := by linear_combination -h1
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd (hμ (sub_eq_zero.mp h)) hj
      · exact h
    rw [h0, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, if_neg (Ne.symm hj),
      smul_zero]

theorem comm_of_eigenbasis {L V κ : Type} [Field L] [AddCommGroup V] [Module L V]
    (b : Module.Basis κ L V) (μ : κ → L) (hμ : Function.Injective μ)
    (f g h : Module.End L V) (hf : ∀ k, f (b k) = μ k • b k) (hg : g ∘ₗ f = f ∘ₗ g)
    (hh : h ∘ₗ f = f ∘ₗ h) : g ∘ₗ h = h ∘ₗ g := by
  refine b.ext fun k => ?_
  obtain ⟨c, hc⟩ := apply_basis_eq_smul b μ hμ f g hf hg k
  obtain ⟨d, hd⟩ := apply_basis_eq_smul b μ hμ f h hf hh k
  simp only [LinearMap.comp_apply]
  rw [hd, map_smul, hc, map_smul, hd, smul_smul, smul_smul, mul_comm]

theorem comm_of_separable_algClosed {L ι : Type} [Field L] [IsAlgClosed L] [Fintype ι] [DecidableEq ι]
    (A G H : Matrix ι ι L) (hs : A.charpoly.Separable) (hG : G * A = A * G) (hH : H * A = A * H) :
    G * H = H * G := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact Subsingleton.elim _ _
  set f := Matrix.toLin' A with hfdef
  set s : Finset L := A.charpoly.roots.toFinset with hsdef
  have hcard : s.card = Fintype.card ι := by
    rw [hsdef, Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hs),
      IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim]
  have hev : ∀ μ : (s : Set L), Module.End.HasEigenvalue f μ := by
    intro μ
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, hfdef, Matrix.charpoly_toLin']
    have hμ := μ.2
    simp only [Finset.mem_coe, hsdef, Multiset.mem_toFinset] at hμ
    exact Polynomial.isRoot_of_mem_roots hμ
  choose v hv using fun μ : (s : Set L) => (hev μ).exists_hasEigenvector
  have hli := Module.End.eigenvectors_linearIndependent f (s : Set L) v hv
  have hc : Fintype.card (s : Set L) = Module.finrank L (ι → L) := by
    simp [hcard]
  haveI : Nonempty (s : Set L) := by
    rw [← Fintype.card_pos_iff, hc, Module.finrank_fintype_fun_eq_card]; exact Fintype.card_pos
  let b := basisOfLinearIndependentOfCardEqFinrank hli hc
  have hb : ∀ k, f (b k) = (k : L) • b k := fun k => by
    simp only [b, coe_basisOfLinearIndependentOfCardEqFinrank]
    exact (hv k).apply_eq_smul
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul]
  exact comm_of_eigenbasis b (fun k => (k : L)) Subtype.coe_injective f _ _ hb
    (by rw [← Matrix.toLin'_mul, hG, Matrix.toLin'_mul])
    (by rw [← Matrix.toLin'_mul, hH, Matrix.toLin'_mul])

theorem centraliser_comm_of_separable : ∀ (K : Type) [Field K] (ι : Type) [Fintype ι] [DecidableEq ι] (γ g h : GL ι K),
  (γ : Matrix ι ι K).charpoly.Separable → g * γ = γ * g → h * γ = γ * h → g * h = h * g := by
  intro K _ ι _ _ γ g h hs hg hh
  apply Units.ext
  have hg' := congrArg Units.val hg
  have hh' := congrArg Units.val hh
  simp only [Units.val_mul] at hg' hh' ⊢
  let φ := algebraMap K (AlgebraicClosure K)
  apply Matrix.map_injective φ.injective
  simp only [Matrix.map_mul]
  apply comm_of_separable_algClosed ((γ : Matrix ι ι K).map φ)
  · rw [Matrix.charpoly_map]; exact hs.map
  · rw [← Matrix.map_mul, hg', Matrix.map_mul]
  · rw [← Matrix.map_mul, hh', Matrix.map_mul]

end GlobalTheory.CentSep
end
