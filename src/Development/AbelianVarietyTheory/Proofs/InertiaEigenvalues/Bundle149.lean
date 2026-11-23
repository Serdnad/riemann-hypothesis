module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle103
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle133
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle134
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle135
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvolutionIdempotentDecompositionOfSeparableChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle111
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle130
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle119
public import GroundTheory.AutomorphicForms.FourierWhittaker.UMatColXEqFromBlocks
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Finiteness.Quotient
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Trace.Quotient
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Localization.NormTrace
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001

@[expose] public section

section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

theorem _root_.GlobalTheory.T.normCharacterOnIdempotentPart_prod_inl : ∀ (K : UQ) (B₁ B₂ : InvAlg K) (ι₁ ι₂ : Type) (e₁ : ι₁ → B₁.A) (e₂ : ι₂ → B₂.A) (S₁ : Finset ι₁) (x : B₁.A × B₂.A), chi (B₁.prod B₂) (Sum.elim (fun i => ((e₁ i, 0) : B₁.A × B₂.A)) (fun j => ((0, e₂ j) : B₁.A × B₂.A))) (S₁.map Function.Embedding.inl) x = chi B₁ e₁ S₁ x.1 := by
  first | exact @GlobalTheory.UnitLemma.Desc.chi_prod_inl | exact GlobalTheory.UnitLemma.Desc.chi_prod_inl | (intros; apply GlobalTheory.UnitLemma.Desc.chi_prod_inl <;> assumption)
end

section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial

theorem _root_.GlobalTheory.T.exists_injective_torus_classes_of_idempotent_decomposition : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] (e : ι → B.A) (S : Finset ι) (a : K.O), K.Small a → IsPre B e S → ∀ k : ℕ, ∃ f : ({i // i ∉ S} → Fin (k + 1)) → B.T ⧸ (intUnits K.O B.A).subgroupOf B.T, Function.Injective f ∧ ∀ n, IsIntegral K.O ((((Quotient.out (f n) : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * algebraMap K.O B.A a ^ k : B.A) := by
  first | exact @GlobalTheory.UnitLemma.TorusPts.torus_points | exact GlobalTheory.UnitLemma.TorusPts.torus_points | (intros; apply GlobalTheory.UnitLemma.TorusPts.torus_points <;> assumption)
end

section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

theorem _root_.GlobalTheory.T.latticeTerm_prod_eq_mul_components : ∀ (K : UQ) (B₁ B₂ : InvAlg K) (ι₁ ι₂ : Type) (e₁ π₁ : ι₁ → B₁.A) (e₂ π₂ : ι₂ → B₂.A) (S₁ : Finset ι₁) (S₂ : Finset ι₂) (a : K.O) (N : ℕ) (M : Submodule K.O (B₁.A × B₂.A)) (p : ι₁ ⊕ ι₂ → ℤ) (u₁ : B₁.A) (u₂ : B₂.A), (Pos (B₁.prod B₂) a (Sum.elim (fun i => ((e₁ i, 0) : B₁.A × B₂.A)) (fun j => ((0, e₂ j) : B₁.A × B₂.A))) N M p → Pos B₁ a e₁ N (M.comap (LinearMap.inl K.O B₁.A B₂.A)) (p ∘ Sum.inl) ∧ Pos B₂ a e₂ N (M.map (LinearMap.snd K.O B₁.A B₂.A)) (p ∘ Sum.inr)) ∧ term (B₁.prod B₂) (Sum.elim (fun i => ((π₁ i, 1) : B₁.A × B₂.A)) (fun j => ((1, π₂ j) : B₁.A × B₂.A))) (S₁.map Function.Embedding.inl) (S₂.map Function.Embedding.inr) (eS (B₁.prod B₂) (Sum.elim (fun i => ((e₁ i, 0) : B₁.A × B₂.A)) (fun j => ((0, e₂ j) : B₁.A × B₂.A))) (S₁.map Function.Embedding.inl) * (show (B₁.prod B₂).A from (u₁, u₂))) (eS (B₁.prod B₂) (Sum.elim (fun i => ((e₁ i, 0) : B₁.A × B₂.A)) (fun j => ((0, e₂ j) : B₁.A × B₂.A))) (S₂.map Function.Embedding.inr) * 1) M = term B₁ π₁ S₁ ∅ (eS B₁ e₁ S₁ * u₁) (eS B₁ e₁ ∅ * 1) (M.comap (LinearMap.inl K.O B₁.A B₂.A)) * term B₂ π₂ ∅ S₂ (eS B₂ e₂ ∅ * u₂) (eS B₂ e₂ S₂ * 1) (M.map (LinearMap.snd K.O B₁.A B₂.A)) := by
  first | exact @GlobalTheory.UnitLemma.Desc.pos_term_prod | exact GlobalTheory.UnitLemma.Desc.pos_term_prod | (intros; apply GlobalTheory.UnitLemma.Desc.pos_term_prod <;> assumption)
end

section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

theorem _root_.GlobalTheory.T.isUniformizerIdempotentFrame_prod : ∀ (K : UQ) (B₁ B₂ : InvAlg K) (ι₁ ι₂ : Type) [Fintype ι₁] [Fintype ι₂] (e₁ π₁ : ι₁ → B₁.A) (e₂ π₂ : ι₂ → B₂.A) (S₁ : Finset ι₁) (S₂ : Finset ι₂), IsFrame B₁ e₁ π₁ S₁ → IsFrame B₂ e₂ π₂ S₂ → IsFrame (B₁.prod B₂) (Sum.elim (fun i => ((e₁ i, 0) : B₁.A × B₂.A)) (fun j => ((0, e₂ j) : B₁.A × B₂.A))) (Sum.elim (fun i => ((π₁ i, 1) : B₁.A × B₂.A)) (fun j => ((1, π₂ j) : B₁.A × B₂.A))) (S₁.disjSum S₂) := by
  first | exact @GlobalTheory.UnitLemma.Desc.isFrame_prod | exact GlobalTheory.UnitLemma.Desc.isFrame_prod | (intros; apply GlobalTheory.UnitLemma.Desc.isFrame_prod <;> assumption)
end

section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

theorem _root_.GlobalTheory.T.normCharacterOnIdempotentPart_frame_properties : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] [DecidableEq ι] (e π : ι → B.A) (S : Finset ι), IsFrame B e π S → (∀ (I : Finset ι) (x y : B.A), IsUnit x → IsUnit y → chi B e I (x * y) = chi B e I x * chi B e I y) ∧ (∀ (I : Finset ι) (w : B.A), IsUnit w → chi B e I (w * B.σ w) = 1) ∧ (∀ I J : Finset ι, I ⊆ S → J ⊆ S → chi B e I (∏ j ∈ J, π j) = (-1) ^ (J ∩ I).card) ∧ (∀ y, B.Plus y → chi B e S y = K.eta (Algebra.norm K.E y)) := by
  first | exact @GlobalTheory.UnitLemma.Desc.chi_frame_props | exact GlobalTheory.UnitLemma.Desc.chi_frame_props | (intros; apply GlobalTheory.UnitLemma.Desc.chi_frame_props <;> assumption)
end

section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

theorem _root_.GlobalTheory.T.involutionIdempotentDecomposition_of_separable_charpoly : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∃ (ι : Type) (_ : Fintype ι) (e : ι → B.A) (S : Finset ι), IsPre B e S := by
  first | exact @GlobalTheory.UnitLemma.Desc.isPre_of_separable | exact GlobalTheory.UnitLemma.Desc.isPre_of_separable | (intros; apply GlobalTheory.UnitLemma.Desc.isPre_of_separable <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma Polynomial

variable {K K' : UQ} {d : ℕ} {φ : K.E →+* K'.E}

def intMap (hU : IsUnrExt K K' d φ) : K.O →+* K'.O where
  toFun a := Classical.choose (exists_int_image hU a)
  map_one' := IsFractionRing.injective K'.O K'.E (by
    rw [Classical.choose_spec (exists_int_image hU 1)]; simp)
  map_mul' a b := IsFractionRing.injective K'.O K'.E (by
    have h1 := Classical.choose_spec (exists_int_image hU (a * b))
    have h2 := Classical.choose_spec (exists_int_image hU a)
    have h3 := Classical.choose_spec (exists_int_image hU b)
    rw [h1]; simp only [map_mul, h2, h3])
  map_zero' := IsFractionRing.injective K'.O K'.E (by
    rw [Classical.choose_spec (exists_int_image hU 0)]; simp)
  map_add' a b := IsFractionRing.injective K'.O K'.E (by
    have h1 := Classical.choose_spec (exists_int_image hU (a + b))
    have h2 := Classical.choose_spec (exists_int_image hU a)
    have h3 := Classical.choose_spec (exists_int_image hU b)
    rw [h1]; simp only [map_add (f := _), h2, h3])

theorem intMap_spec (hU : IsUnrExt K K' d φ) (a : K.O) :
    algebraMap K'.O K'.E (intMap hU a) = φ (algebraMap K.O K.E a) :=
  Classical.choose_spec (exists_int_image hU a)

theorem intMap_injective (hU : IsUnrExt K K' d φ) : Function.Injective (intMap hU) := by
  intro a b h
  apply IsFractionRing.injective K.O K.E
  apply φ.injective
  rw [← intMap_spec hU, ← intMap_spec hU, h]

theorem val_mul_ne (K : UQ) {x y : K.E} (hx : x ≠ 0) (hy : y ≠ 0) :
    val K.O (x * y) = val K.O x + val K.O y := by
  unfold val
  rw [map_mul, WithZero.log_mul (by simpa using hx) (by simpa using hy)]; ring

theorem val_irreducible (K : UQ) {ϖ : K.O} (h : Irreducible ϖ) : val K.O (algebraMap K.O K.E ϖ) = 1 := by
  unfold val
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.intValuation_singleton _ h.ne_zero
      ((IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 h), WithZero.log_exp]; rfl

theorem val_pow_ne (K : UQ) {x : K.E} (hx : x ≠ 0) (n : ℕ) : val K.O (x ^ n) = n * val K.O x := by
  induction n with
  | zero => simp [val]
  | succ n ih => rw [pow_succ, val_mul_ne K (pow_ne_zero _ hx) hx, ih]; push_cast; ring

theorem val_isUnit (K : UQ) {u : K.O} (hu : IsUnit u) : val K.O (algebraMap K.O K.E u) = 0 := by
  obtain ⟨w, rfl⟩ := hu
  have h1 : (algebraMap K.O K.E (w : K.O)) ≠ 0 := by simp
  have h2 : (algebraMap K.O K.E ((w⁻¹ : K.Oˣ) : K.O)) ≠ 0 := by simp
  have h := val_mul_ne K h1 h2
  rw [← map_mul, Units.mul_inv, map_one] at h
  have h3 := val_algebraMap_nonneg K (w : K.O)
  have h4 := val_algebraMap_nonneg K ((w⁻¹ : K.Oˣ) : K.O)
  have h5 : val K.O (1 : K.E) = 0 := by simp [val]
  omega

theorem irreducible_of_val_one (K : UQ) {x : K.O} (hx : val K.O (algebraMap K.O K.E x) = 1) :
    Irreducible x := by
  have hx0 : x ≠ 0 := by rintro rfl; simp [val] at hx
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible K.O
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
  have hϖ0 : algebraMap K.O K.E ϖ ≠ 0 := by simpa using hϖ.ne_zero
  have hu0 : algebraMap K.O K.E (u : K.O) ≠ 0 := by simp
  rw [map_mul, map_pow, val_mul_ne K hu0 (pow_ne_zero _ hϖ0), val_pow_ne K hϖ0,
    val_isUnit K u.isUnit, val_irreducible K hϖ] at hx
  have hn : n = 1 := by omega
  subst hn
  rw [pow_one]
  exact (irreducible_units_mul u).2 hϖ

theorem map_maximalIdeal (hU : IsUnrExt K K' d φ) :
    Ideal.map (intMap hU) (IsLocalRing.maximalIdeal K.O) = IsLocalRing.maximalIdeal K'.O := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible K.O
  have h1 := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  have h2 : Irreducible (intMap hU ϖ) :=
    irreducible_of_val_one K' (by rw [intMap_spec, hU.2.2.1, val_irreducible K hϖ])
  rw [h1, Ideal.map_span, Set.image_singleton,
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 h2]


open scoped nonZeroDivisors in
theorem exists_trace_unit_of_span (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E) (hU : IsUnrExt K K' d φ)
    (hB : ∃ u : Fin d → K'.O, ∀ y : K'.O, ∃ a : Fin d → K.O,
      algebraMap K'.O K'.E y = ∑ i, φ (algebraMap K.O K.E (a i)) * algebraMap K'.O K'.E (u i)) :
    ∃ y : K'.O, ∃ a : K.O, IsUnit a ∧
      @Algebra.trace K.E K'.E _ _ φ.toAlgebra (algebraMap K'.O K'.E y) = algebraMap K.O K.E a := by
  letI : Algebra K.E K'.E := φ.toAlgebra
  letI : Algebra K.O K'.O := (intMap hU).toAlgebra
  letI : Algebra K.O K'.E := (φ.comp (algebraMap K.O K.E)).toAlgebra
  haveI : IsScalarTower K.O K.E K'.E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower K.O K'.O K'.E := IsScalarTower.of_algebraMap_eq fun a => (intMap_spec hU a).symm
  have hmap : ∀ a : K.O, algebraMap K.O K'.O a = intMap hU a := fun _ => rfl

  obtain ⟨u, hu⟩ := hB
  haveI hfin : Module.Finite K.O K'.O := by
    classical
    refine ⟨⟨Finset.univ.image u, eq_top_iff.2 fun y _ => ?_⟩⟩
    obtain ⟨a, ha⟩ := hu y
    have hy : y = ∑ i, a i • u i := by
      apply IsFractionRing.injective K'.O K'.E

      rw [ha, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, map_mul, hmap, intMap_spec]
    rw [hy]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  haveI : FaithfulSMul K.O K'.O :=
    (faithfulSMul_iff_algebraMap_injective K.O K'.O).2 (intMap_injective hU)
  haveI : Module.Free K.O K'.O := Module.free_of_finite_type_torsion_free'

  haveI : IsLocalization (Algebra.algebraMapSubmonoid K'.O K.O⁰) K'.E := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible K.O
    have hϖ0 : algebraMap K.O K.E ϖ ≠ 0 := by simpa using hϖ.ne_zero
    have hφϖ : φ (algebraMap K.O K.E ϖ) ≠ 0 := by simpa using hϖ0
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨y, hy⟩
      obtain ⟨r, hr, rfl⟩ := hy
      refine IsUnit.mk0 _ ?_
      change algebraMap K'.O K'.E (intMap hU r) ≠ 0
      rw [intMap_spec]
      simpa using nonZeroDivisors.ne_zero hr
    · intro z
      by_cases hz : z = 0
      · exact ⟨⟨0, 1⟩, by simp [hz]⟩
      obtain ⟨s, hs⟩ := mem_range_of_val_nonneg K'
        (z * φ (algebraMap K.O K.E ϖ) ^ (-(val K'.O z)).toNat) (by
          rw [val_mul_ne K' hz (pow_ne_zero _ hφϖ), val_pow_ne K' hφϖ, hU.2.2.1, val_irreducible K hϖ]
          omega)
      refine ⟨⟨s, ⟨algebraMap K.O K'.O (ϖ ^ (-(val K'.O z)).toNat),
        Algebra.mem_algebraMapSubmonoid_of_mem
          ⟨_, pow_mem (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero) _⟩⟩⟩, ?_⟩
      change z * algebraMap K'.O K'.E (intMap hU (ϖ ^ (-(val K'.O z)).toNat)) = algebraMap K'.O K'.E s
      rw [hs, intMap_spec, map_pow, map_pow]
    · intro x y h
      exact ⟨1, by rw [IsFractionRing.injective K'.O K'.E h]⟩

  have hpS : Ideal.map (algebraMap K.O K'.O) (IsLocalRing.maximalIdeal K.O) =
      IsLocalRing.maximalIdeal K'.O := map_maximalIdeal hU
  haveI hmax : (Ideal.map (algebraMap K.O K'.O) (IsLocalRing.maximalIdeal K.O)).IsMaximal := by
    rw [hpS]; infer_instance
  letI : Field (K.O ⧸ IsLocalRing.maximalIdeal K.O) := Ideal.Quotient.field _
  letI : Field (K'.O ⧸ Ideal.map (algebraMap K.O K'.O) (IsLocalRing.maximalIdeal K.O)) :=
    Ideal.Quotient.field _
  haveI : Finite (K'.O ⧸ IsLocalRing.maximalIdeal K'.O) := K'.fin
  haveI : Finite (K'.O ⧸ Ideal.map (algebraMap K.O K'.O) (IsLocalRing.maximalIdeal K.O)) :=
    Finite.of_equiv _ (Ideal.quotEquivOfEq hpS).symm.toEquiv
  haveI : Finite (K.O ⧸ IsLocalRing.maximalIdeal K.O) := K.fin
  haveI : FiniteDimensional (K.O ⧸ IsLocalRing.maximalIdeal K.O)
      (K'.O ⧸ Ideal.map (algebraMap K.O K'.O) (IsLocalRing.maximalIdeal K.O)) := inferInstance
  haveI : Algebra.IsSeparable (K.O ⧸ IsLocalRing.maximalIdeal K.O)
      (K'.O ⧸ Ideal.map (algebraMap K.O K'.O) (IsLocalRing.maximalIdeal K.O)) := inferInstance
  obtain ⟨z, hz⟩ := Algebra.trace_surjective (K.O ⧸ IsLocalRing.maximalIdeal K.O)
    (K'.O ⧸ Ideal.map (algebraMap K.O K'.O) (IsLocalRing.maximalIdeal K.O)) 1
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  have htr := Algebra.trace_quotient_mk (R := K.O) (S := K'.O) y
  rw [hz] at htr
  refine ⟨y, Algebra.trace K.O K'.O y, ?_, ?_⟩
  · by_contra h
    have h0 : Ideal.Quotient.mk (IsLocalRing.maximalIdeal K.O) (Algebra.trace K.O K'.O y) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 ((IsLocalRing.mem_maximalIdeal _).2 h)
    rw [h0] at htr
    exact one_ne_zero htr
  · exact Algebra.trace_localization K.O K.O⁰ (Rₘ := K.E) (Sₘ := K'.E) y

theorem exists_trace_unit (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E) (hU : IsUnrExt K K' d φ) :
    ∃ y : K'.O, ∃ a : K.O, IsUnit a ∧
      @Algebra.trace K.E K'.E _ _ φ.toAlgebra (algebraMap K'.O K'.E y) = algebraMap K.O K.E a :=
  exists_trace_unit_of_span K K' d φ hU (exists_int_basis_of_unr K K' d φ hU)

end GlobalTheory.UnitLemma.Unr
end
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

noncomputable section
namespace GlobalTheory.SchurExt

variable {E : Type} [Field E] [NumberField E]

theorem prS_finGL (S : Finset (HeightOneSpectrum (𝓞 E))) (a : ℕ) (k : GL (Fin a) (Af E)) :
    prS S a (finGL E a k) = finGL E a (prSf S a k) := by
  have hI : ∀ y, idemS S * sFin E y = sFin E (idemSf S * y) := fun y => Prod.ext (mul_zero _) rfl
  ext i j
  change (1 : Matrix (Fin a) (Fin a) (Ad E)) i j - idemS S * (1 : Matrix (Fin a) (Fin a) (Ad E)) i j
      + idemS S * ((1 : Matrix (Fin a) (Fin a) (Ad E)) i j - sFin E ((1 : Matrix (Fin a) (Fin a) (Af E)) i j)
        + sFin E (k i j)) = (1 : Matrix (Fin a) (Fin a) (Ad E)) i j
      - sFin E ((1 : Matrix (Fin a) (Fin a) (Af E)) i j)
      + sFin E ((1 : Matrix (Fin a) (Fin a) (Af E)) i j - idemSf S * (1 : Matrix (Fin a) (Fin a) (Af E)) i j
        + idemSf S * k i j)
  generalize idemS S = I at hI ⊢
  generalize idemSf S = J at hI ⊢
  simp only [Matrix.one_apply]
  split_ifs <;> simp only [mul_one, mul_zero, map_zero, map_sub, map_add (f := _), mul_add, mul_sub, hI, sub_zero,
    zero_sub, zero_add] <;> ring

theorem prO_finGL (S : Finset (HeightOneSpectrum (𝓞 E))) (a : ℕ) (k : GL (Fin a) (Af E)) :
    prO S a (finGL E a k) = finGL E a (prOf S a k) := by
  have hI : ∀ y, (1 - idemS S) * sFin E y = sFin E ((1 - idemSf S) * y) := fun y => Prod.ext (mul_zero _) rfl
  ext i j
  change (1 : Matrix (Fin a) (Fin a) (Ad E)) i j - (1 - idemS S) * (1 : Matrix (Fin a) (Fin a) (Ad E)) i j
      + (1 - idemS S) * ((1 : Matrix (Fin a) (Fin a) (Ad E)) i j - sFin E ((1 : Matrix (Fin a) (Fin a) (Af E)) i j)
        + sFin E (k i j)) = (1 : Matrix (Fin a) (Fin a) (Ad E)) i j
      - sFin E ((1 : Matrix (Fin a) (Fin a) (Af E)) i j)
      + sFin E ((1 : Matrix (Fin a) (Fin a) (Af E)) i j - (1 - idemSf S) * (1 : Matrix (Fin a) (Fin a) (Af E)) i j
        + (1 - idemSf S) * k i j)
  generalize (1 - idemS S) = I at hI ⊢
  generalize (1 - idemSf S) = J at hI ⊢
  simp only [Matrix.one_apply]
  split_ifs <;> simp only [mul_one, mul_zero, map_zero, map_sub, map_add (f := _), mul_add, mul_sub, hI, sub_zero,
    zero_sub, zero_add] <;> ring

theorem continuous_cornerGL_idemHom (a : ℕ) (e : Af E) (he : IsIdempotentElem e) :
    Continuous (cornerGL a (idemHom e he)) := by
  refine Continuous.units_map _ ?_
  change Continuous fun x : Matrix (Fin a) (Fin a) (Af E) => 1 - matN a (idemHom e he) 1 + matN a (idemHom e he) x
  refine continuous_const.add ?_
  exact continuous_pi fun i => continuous_pi fun j =>
    (continuous_const.mul continuous_id : Continuous fun x : Af E => e * x).comp
      ((continuous_apply j).comp (continuous_apply i))

theorem continuous_prSf (S : Finset (HeightOneSpectrum (𝓞 E))) (a : ℕ) : Continuous (prSf S a) :=
  continuous_cornerGL_idemHom a _ _

theorem continuous_prOf (S : Finset (HeightOneSpectrum (𝓞 E))) (a : ℕ) : Continuous (prOf S a) :=
  continuous_cornerGL_idemHom a _ _

end GlobalTheory.SchurExt

theorem GlobalTheory.SchurExt.eventually_prS_prO_finGL :
    ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (V V' : Set (GL (Fin a) (Af E))), V ∈ 𝓝 (1 : GL (Fin a) (Af E)) → V' ∈ 𝓝 (1 : GL (Fin a) (Af E)) → ∀ᶠ k in 𝓝 (1 : GL (Fin a) (Af E)), (∃ k' ∈ V, prS S a (finGL E a k) = finGL E a k') ∧ ∃ k'' ∈ V', prO S a (finGL E a k) = finGL E a k'' := by
  intro E _ _ a S V V' hV hV'
  have h1 := (continuous_prSf S a).tendsto 1
  have h2 := (continuous_prOf S a).tendsto 1
  rw [map_one] at h1 h2
  filter_upwards [h1 hV, h2 hV'] with k hk hk'
  exact ⟨⟨_, hk, prS_finGL S a k⟩, _, hk', prO_finGL S a k⟩
end
end

section

noncomputable section

namespace GlobalTheory.SchurExt

section LowerUnipotent

variable {R : Type} [CommRing R] {m r : ℕ}

def lowUni (Y : Matrix (Fin (r + 1)) (Fin (m + 1)) R) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R :=
  unblk (Matrix.fromBlocks 1 0 Y 1)

def conjLowUni (Y : Matrix (Fin (r + 1)) (Fin (m + 1)) R) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) :
    Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R :=
  lowUni Y * k * lowUni (-Y)

end LowerUnipotent

end GlobalTheory.SchurExt
end
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

namespace GlobalTheory.SchurExt

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem idemS_mul_sInf (S : Finset (HeightOneSpectrum (𝓞 E))) (x : Cinf E) : idemS S * sInf E x = sInf E x :=
  Prod.ext (one_mul _) (mul_zero _)

theorem one_sub_idemS_mul_sInf (S : Finset (HeightOneSpectrum (𝓞 E))) (x : Cinf E) :
    (1 - idemS S) * sInf E x = 0 := by
  rw [sub_mul, one_mul, idemS_mul_sInf, sub_self]

theorem prS_infGL (S : Finset (HeightOneSpectrum (𝓞 E))) (a : ℕ) (y : GL (Fin a) (Cinf E)) :
    prS S a (infGL E a y) = infGL E a y := by
  ext i j
  change (1 : Matrix (Fin a) (Fin a) (Ad E)) i j - idemS S * (1 : Matrix (Fin a) (Fin a) (Ad E)) i j +
      idemS S * ((1 : Matrix (Fin a) (Fin a) (Ad E)) i j - sInf E ((1 : Matrix (Fin a) (Fin a) (Cinf E)) i j) +
        sInf E (y i j)) =
    (1 : Matrix (Fin a) (Fin a) (Ad E)) i j - sInf E ((1 : Matrix (Fin a) (Fin a) (Cinf E)) i j) + sInf E (y i j)
  rw [mul_add, mul_sub, idemS_mul_sInf, idemS_mul_sInf]
  ring

theorem prO_infGL (S : Finset (HeightOneSpectrum (𝓞 E))) (a : ℕ) (y : GL (Fin a) (Cinf E)) :
    prO S a (infGL E a y) = 1 := by
  ext i j
  change (1 : Matrix (Fin a) (Fin a) (Ad E)) i j - (1 - idemS S) * (1 : Matrix (Fin a) (Fin a) (Ad E)) i j +
      (1 - idemS S) * ((1 : Matrix (Fin a) (Fin a) (Ad E)) i j - sInf E ((1 : Matrix (Fin a) (Fin a) (Cinf E)) i j) +
        sInf E (y i j)) =
    (1 : Matrix (Fin a) (Fin a) (Ad E)) i j
  rw [mul_add, mul_sub, one_sub_idemS_mul_sInf, one_sub_idemS_mul_sInf]
  ring

theorem prS_prO_mul_infGL : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (g : GA E a) (y : GL (Fin a) (Cinf E)),
    prS S a (g * infGL E a y) = prS S a g * infGL E a y ∧ prO S a (g * infGL E a y) = prO S a g := by
  intro E _ _ _ a S g y
  refine ⟨?_, ?_⟩
  · rw [map_mul, prS_infGL]
  · rw [map_mul, prO_infGL, mul_one]

end GlobalTheory.SchurExt
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

namespace GlobalTheory.SchurExt

theorem schurSquareMatrixToBlocks_blockDiagonal_one {R : Type} [CommRing R] (m r : ℕ) (h : Matrix (Fin (m + 1)) (Fin (m + 1)) R) :
    blk (GroundTheory.Automorphic.FourierWhittaker.blockMat (by omega : m + 1 ≤ m + r + 1 + 1) h) =
      Matrix.fromBlocks h 0 0 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [blk, eqv, GroundTheory.Automorphic.FourierWhittaker.blockMat_apply, Matrix.one_apply, Fin.ext_iff]
  all_goals
    have hi := i.isLt
    have hj := j.isLt
    try intro
    split_ifs <;> first | rfl | (exfalso; omega) | omega

theorem schurF_blockGL (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ)
    (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ) (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ)
    (h : GA E (m + 1)) :
    schurF β b₁ χ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h) =
      β h * b₁ 1 * (χ 0 : ℂ) := by
  classical
  have hb := schurSquareMatrixToBlocks_blockDiagonal_one (R := Ad E) m r (h : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E))
  have hD : Dof ((GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h : GA E (m + r + 1 + 1)) :
      Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) = 1 := by
    rw [Dof, GroundTheory.Automorphic.FourierWhittaker.coe_blockGL, hb, Matrix.toBlocks_fromBlocks₂₂]
  have hA : Aof ((GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h : GA E (m + r + 1 + 1)) :
      Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) = h := by
    rw [Aof, GroundTheory.Automorphic.FourierWhittaker.coe_blockGL, hb, Matrix.toBlocks_fromBlocks₁₁]
  have hB : Bof ((GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h : GA E (m + r + 1 + 1)) :
      Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) = 0 := by
    rw [Bof, GroundTheory.Automorphic.FourierWhittaker.coe_blockGL, hb, Matrix.toBlocks_fromBlocks₁₂]
  have hC : Cof ((GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h : GA E (m + r + 1 + 1)) :
      Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) = 0 := by
    rw [Cof, GroundTheory.Automorphic.FourierWhittaker.coe_blockGL, hb, Matrix.toBlocks_fromBlocks₂₁]
  have hmk : mkGL (h : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) = h :=
    Units.ext (coe_mkGL (Matrix.isUnits_det_units h))
  have hmk1 : mkGL (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)) = 1 :=
    Units.ext (by rw [coe_mkGL (by simp)]; rfl)
  have hpsi : psi (0 : Ad E) = 1 := by
    simp [psi]
  have hchi : chiF (m := m) (r := r) χ 0 = (χ 0 : ℂ) := by
    have h0 : (fun i j => pInf E ((0 : Matrix (Fin (r + 1)) (Fin (m + 1)) (Ad E)) i j)) = 0 := by
      funext i j; simp
    rw [chiF, h0]
    simp [zero_mem]
  rw [schurF, if_pos (by rw [hD]; simp), Xof, Scof, Yof, hA, hB, hC, hD]
  simp only [inv_one, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, sub_zero, Matrix.zero_apply]
  rw [hpsi, hmk, hmk1, hchi, one_mul]

end GlobalTheory.SchurExt
end
