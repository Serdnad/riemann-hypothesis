module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Smooth.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle235
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Support
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthCokerLsmulEqLengthKerAddSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle187
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle078
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle236
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle186
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
public import Mathlib.RingTheory.Localization.Away.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle237
public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import Mathlib.RingTheory.RamificationInertia.Inertia
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumOrdMulInertiaDegEqFinrankMulOrd
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle238
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle032
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
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004

@[expose] public section

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.isDomain_and_isIntegrallyClosed_atPrime_tensor_field_alt : (∀ (F K : Type) [Field F] [CharZero F] [Field K] [Algebra F K] (s : Finset K), ∃ R : Subalgebra F K, (↑s : Set K) ⊆ (R : Set K) ∧ Algebra.Smooth F R) → (∀ (B : Type) [CommRing B] (Q : Ideal B) [Q.IsPrime], (∀ s : Finset B, ∃ C : Subring B, (↑s : Set B) ⊆ (C : Set B) ∧ ∀ (q : Ideal C) [q.IsPrime], IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q)) → IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q)) → ∀ (F K A : Type) [Field F] [CharZero F] [Field K] [Algebra F K] [CommRing A] [Algebra F A], (∀ (P : Ideal A) [P.IsPrime], IsDomain (Localization.AtPrime P) ∧ IsIntegrallyClosed (Localization.AtPrime P)) → ∀ (Q : Ideal (TensorProduct F A K)) [Q.IsPrime], IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) := by
  first | exact @GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_tensor_field | exact GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_tensor_field | (intros; apply GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_tensor_field <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_idempotent_tmul_one_eq_of_smooth_algebra : ∀ (R A : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing A] [Algebra R A], Algebra.Smooth R A → ∀ ε : A ⊗[R] FractionRing R, IsIdempotentElem ε → ∃ a : A, IsIdempotentElem a ∧ a ⊗ₜ[R] (1 : FractionRing R) = ε := by
  first | exact @GlobalTheory.exists_isIdempotentElem_tmul_one_eq_of_smooth | exact GlobalTheory.exists_isIdempotentElem_tmul_one_eq_of_smooth | (intros; apply GlobalTheory.exists_isIdempotentElem_tmul_one_eq_of_smooth <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_root_of_unit_zero_dimensional : ∀ (R : Type) [CommRing R] [Ring.KrullDimLE 0 R] (q : ℕ), 0 < q → IsUnit (q : R) → ∀ u : Rˣ, (∀ m : Ideal R, m.IsMaximal → ∃ x : R, x ^ q - (u : R) ∈ m) → ∃ v : Rˣ, v ^ q = u := by
  first | (exact @GlobalTheory.exists_unit_pow_eq_of_krullDimLE_zero) | (exact GlobalTheory.exists_unit_pow_eq_of_krullDimLE_zero) | (intros; apply GlobalTheory.exists_unit_pow_eq_of_krullDimLE_zero  <;> assumption)
end

section


theorem _root_.GlobalTheory.T.length_coker_lsmul_eq_length_ker_add_sum' : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] (b : A) (P : Finset (PrimeSpectrum A)), (∀ p ∈ P, ringKrullDim (A ⧸ p.asIdeal) = 1 ∧ b ∉ p.asIdeal) → ∀ (M : Type) [AddCommGroup M] [Module A M] [Module.Finite A M], (∀ p ∈ Module.support A M, p ∈ P ∨ p.asIdeal = IsLocalRing.maximalIdeal A) → Module.length A (LinearMap.ker (LinearMap.lsmul A M b)) ≠ ⊤ ∧ Module.length A (M ⧸ LinearMap.range (LinearMap.lsmul A M b)) = Module.length A (LinearMap.ker (LinearMap.lsmul A M b)) + ∑ p ∈ P, Module.length (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M) * Module.length A (A ⧸ (p.asIdeal ⊔ Ideal.span {b})) := by
  first | exact @GlobalTheory.length_coker_lsmul_eq_length_ker_add_sum | exact GlobalTheory.length_coker_lsmul_eq_length_ker_add_sum | (intros; apply GlobalTheory.length_coker_lsmul_eq_length_ker_add_sum <;> assumption)
end

section

open scoped TensorProduct Polynomial
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem linearIndependent_tmul_D_of_regular_system :
    ∀ (k A : Type) [Field k] [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Algebra k A] [Algebra.FormallySmooth k (IsLocalRing.ResidueField A)] (n : ℕ) (t : Fin n → A), Ideal.span (Set.range t) = IsLocalRing.maximalIdeal A → (n : WithBot ℕ∞) = ringKrullDim A → LinearIndependent (IsLocalRing.ResidueField A) (fun a => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (t a)) := by
  intro k A _ _ _ _ _ _ n t hspan hdim
  classical
  have htm : ∀ i, t i ∈ maximalIdeal A := fun i => hspan ▸ Ideal.subset_span ⟨i, rfl⟩
  have hn : n = (maximalIdeal A).spanFinrank := by
    apply le_antisymm
    · have h := ringKrullDim_le_spanFinrank_maximalIdeal A
      rw [← hdim] at h
      exact_mod_cast h
    · rw [← hspan]
      refine (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range t)).trans ?_
      rw [← Set.image_univ]
      refine (Set.ncard_image_le Set.finite_univ).trans ?_
      simp
  have hker : RingHom.ker (algebraMap A (ResidueField A)) = maximalIdeal A := ker_residue
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  choose b hb using fun j => residue_surjective (R := A) (g j)
  have hx : ∑ j, b j * t j ∈ RingHom.ker (algebraMap A (ResidueField A)) := by
    rw [hker]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (htm j)
  have htk : ∀ j, algebraMap A (ResidueField A) (t j) = 0 := fun j => by
    rw [← RingHom.mem_ker, hker]; exact htm j
  have h0 : KaehlerDifferential.kerCotangentToTensor k A (ResidueField A)
      ((RingHom.ker (algebraMap A (ResidueField A))).toCotangent ⟨_, hx⟩) = 0 := by

    rw [KaehlerDifferential.kerCotangentToTensor_toCotangent, map_sum, tmul_sum, ← hg]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Derivation.leibniz, tmul_add, ← smul_tmul, ← smul_tmul, Algebra.smul_def, mul_one,
      Algebra.smul_def, mul_one, htk, zero_tmul, add_zero, smul_tmul', smul_eq_mul, mul_one]
    rw [← hb j]; rfl
  have hinj := kerCotangentToTensor_injective_of_formallySmooth k A (ResidueField A)
    residue_surjective
  have h2 : ∑ j, b j * t j ∈ RingHom.ker (algebraMap A (ResidueField A)) ^ 2 :=
    (Ideal.toCotangent_eq_zero _ _).mp (hinj (h0.trans (map_zero _).symm))
  rw [hker] at h2
  have := coeffs_mem_maximalIdeal_of_sum_mem_sq t hspan hn b h2 i
  rw [← hb i]
  exact (residue_eq_zero_iff _).2 this

end GlobalTheory
end

section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef.InfScale

variable {F : Type} [Field F]

noncomputable def polyScale (c : F) : F[X] →ₐ[F] F[X] := Polynomial.aeval (Polynomial.C c * Polynomial.X)

theorem polyScale_polyScale (c d : F) (p : F[X]) :
    polyScale d (polyScale c p) = polyScale (c * d) p := by
  have : (polyScale d).comp (polyScale c) = polyScale (c * d) := by
    apply Polynomial.algHom_ext
    simp only [polyScale, AlgHom.comp_apply, Polynomial.aeval_X, map_mul, Polynomial.aeval_C,
      Polynomial.algebraMap_eq, Polynomial.C_mul]
    ring
  exact congrArg (fun φ : F[X] →ₐ[F] F[X] => φ p) this

theorem polyScale_one (p : F[X]) : polyScale (1 : F) p = p := by
  show Polynomial.aeval (Polynomial.C (1 : F) * Polynomial.X) p = p
  rw [map_one, one_mul, Polynomial.aeval_X_left_apply]

theorem polyScale_injective {c : F} (hc : c ≠ 0) : Function.Injective (polyScale c) := by
  intro p q h
  have := congrArg (polyScale c⁻¹) h
  rwa [polyScale_polyScale, polyScale_polyScale, mul_inv_cancel₀ hc, polyScale_one, polyScale_one] at this

theorem rescale_injective {c : F} (hc : c ≠ 0) : Function.Injective (PowerSeries.rescale c) := by
  intro p q h
  have := congrArg (PowerSeries.rescale c⁻¹) h
  rwa [PowerSeries.rescale_rescale, PowerSeries.rescale_rescale, mul_inv_cancel₀ hc,
    PowerSeries.rescale_one, RingHom.id_apply, RingHom.id_apply] at this

theorem transcendental_X : Transcendental F (RatFunc.X : RatFunc F) := by
  rw [transcendental_iff_injective]
  intro p q h
  have e : ∀ r : F[X], Polynomial.aeval (RatFunc.X : RatFunc F) r = algebraMap F[X] (RatFunc F) r := by
    intro r
    rw [← RatFunc.algebraMap_X, Polynomial.aeval_algebraMap_apply, Polynomial.aeval_X_left_apply]
  rw [e, e] at h
  exact IsFractionRing.injective F[X] (RatFunc F) h

end GlobalTheory.Nef.InfScale

namespace GlobalTheory.Nef.InfScale

variable {F : Type} [Field F]

noncomputable def ratScale (c : F) (hc : c ≠ 0) : RatFunc F →+* RatFunc F :=
  IsFractionRing.lift (g := (algebraMap F[X] (RatFunc F)).comp (polyScale c).toRingHom)
    ((IsFractionRing.injective F[X] (RatFunc F)).comp (polyScale_injective hc))

noncomputable def lsScale (c : F) (hc : c ≠ 0) : LaurentSeries F →+* LaurentSeries F :=
  IsFractionRing.lift (g := (algebraMap (PowerSeries F) (LaurentSeries F)).comp (PowerSeries.rescale c))
    ((IsFractionRing.injective (PowerSeries F) (LaurentSeries F)).comp (rescale_injective hc))

noncomputable def ratInv : RatFunc F →+* RatFunc F :=
  IsFractionRing.lift (g := (Polynomial.aeval (RatFunc.X : RatFunc F)⁻¹).toRingHom)
    (fun x y h => (transcendental_iff_injective.1 fun h => transcendental_X (IsAlgebraic.inv_iff.1 h)) h)

theorem lsScale_comp (c : F) (hc : c ≠ 0) :
    (lsScale c hc).comp (algebraMap (PowerSeries F) (LaurentSeries F)) =
      (algebraMap (PowerSeries F) (LaurentSeries F)).comp (PowerSeries.rescale c) :=
  IsLocalization.lift_comp _

theorem ratScale_alg (c : F) (hc : c ≠ 0) (p : F[X]) :
    ratScale c hc (algebraMap F[X] (RatFunc F) p) = algebraMap F[X] (RatFunc F) (polyScale c p) :=
  IsLocalization.lift_eq _ _

theorem ratInv_alg (p : F[X]) :
    ratInv (algebraMap F[X] (RatFunc F) p) = Polynomial.aeval (RatFunc.X : RatFunc F)⁻¹ p :=
  IsLocalization.lift_eq _ _

theorem ext_rat {A : Type} [CommRing A] {f g : RatFunc F →+* A}
    (hC : ∀ a, f (RatFunc.C a) = g (RatFunc.C a)) (hX : f RatFunc.X = g RatFunc.X) : f = g := by
  apply IsLocalization.ringHom_ext (nonZeroDivisors F[X])
  apply Polynomial.ringHom_ext
  · intro a; simpa [RatFunc.algebraMap_C] using hC a
  · simpa [RatFunc.algebraMap_X] using hX

theorem ratScale_C (c : F) (hc : c ≠ 0) (a : F) : ratScale c hc (RatFunc.C a) = RatFunc.C a := by
  rw [← RatFunc.algebraMap_C, ratScale_alg]; simp [polyScale]

theorem ratScale_X (c : F) (hc : c ≠ 0) :
    ratScale c hc RatFunc.X = RatFunc.C c * RatFunc.X := by
  rw [← RatFunc.algebraMap_X, ratScale_alg]; simp [polyScale, RatFunc.algebraMap_C, RatFunc.algebraMap_X]

theorem ratInv_C (a : F) : ratInv (RatFunc.C a) = RatFunc.C a := by
  rw [← RatFunc.algebraMap_C, ratInv_alg]; simp

theorem ratInv_X : ratInv (RatFunc.X : RatFunc F) = RatFunc.X⁻¹ := by
  rw [← RatFunc.algebraMap_X, ratInv_alg]; simp

end GlobalTheory.Nef.InfScale

namespace GlobalTheory.Nef.InfScale

variable {F : Type} [Field F]

theorem alg_C (a : F) : algebraMap (RatFunc F) (LaurentSeries F) (RatFunc.C a) =
    algebraMap (PowerSeries F) (LaurentSeries F) (PowerSeries.C a) := by
  have h := (RatFunc.coe_coe (Polynomial.C a)).symm
  rw [Polynomial.coe_C] at h
  exact h

theorem alg_X : algebraMap (RatFunc F) (LaurentSeries F) RatFunc.X =
    algebraMap (PowerSeries F) (LaurentSeries F) PowerSeries.X := by
  simp [RatFunc.coe_X]

theorem rescale_C' (c a : F) : PowerSeries.rescale c (PowerSeries.C a) = PowerSeries.C a := by
  ext n
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_C]
  rcases n with _ | n <;> simp

theorem lsScale_rat (c : F) (hc : c ≠ 0) :
    (lsScale c hc).comp (algebraMap (RatFunc F) (LaurentSeries F)) =
      (algebraMap (RatFunc F) (LaurentSeries F)).comp (ratScale c hc) := by
  have hl : ∀ p, lsScale c hc (algebraMap (PowerSeries F) (LaurentSeries F) p) =
      algebraMap (PowerSeries F) (LaurentSeries F) (PowerSeries.rescale c p) :=
    fun p => RingHom.congr_fun (lsScale_comp c hc) p
  apply ext_rat
  · intro a
    simp only [RingHom.comp_apply, ratScale_C, alg_C, hl, rescale_C']
  · simp only [RingHom.comp_apply, ratScale_X, map_mul, alg_C, alg_X, hl, PowerSeries.rescale_X,
      rescale_C']

theorem ratInv_ratScale (c : F) (hc : c ≠ 0) :
    ratInv.comp (ratScale c hc) = (ratScale c⁻¹ (inv_ne_zero hc)).comp ratInv := by
  apply ext_rat
  · intro a; simp only [RingHom.comp_apply, ratScale_C, ratInv_C]
  · simp only [RingHom.comp_apply, ratScale_X, ratInv_X, map_mul, ratInv_C, map_inv₀, mul_inv,
      inv_inv]

theorem scaling_expansion_infinity :
    ∀ (F : Type) [Field F] [CharZero F], ∃ (σ : RatFunc F →+* RatFunc F) (j : RatFunc F →+* LaurentSeries F) (r₂ rh : LaurentSeries F →+* LaurentSeries F), r₂.comp (algebraMap (PowerSeries F) (LaurentSeries F)) = (algebraMap (PowerSeries F) (LaurentSeries F)).comp (PowerSeries.rescale 2) ∧ r₂.comp (algebraMap (RatFunc F) (LaurentSeries F)) = (algebraMap (RatFunc F) (LaurentSeries F)).comp σ ∧ rh.comp (algebraMap (PowerSeries F) (LaurentSeries F)) = (algebraMap (PowerSeries F) (LaurentSeries F)).comp (PowerSeries.rescale 2⁻¹) ∧ rh.comp j = j.comp σ ∧ j.comp RatFunc.C = (algebraMap (PowerSeries F) (LaurentSeries F)).comp PowerSeries.C ∧ (algebraMap (RatFunc F) (LaurentSeries F)).comp RatFunc.C = (algebraMap (PowerSeries F) (LaurentSeries F)).comp PowerSeries.C := by
  intro F _ _
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  have h2' : (2 : F)⁻¹ ≠ 0 := inv_ne_zero h2
  refine ⟨ratScale 2 h2, (algebraMap (RatFunc F) (LaurentSeries F)).comp ratInv, lsScale 2 h2,
    lsScale 2⁻¹ h2', lsScale_comp 2 h2, lsScale_rat 2 h2, lsScale_comp 2⁻¹ h2', ?_, ?_, ?_⟩
  · rw [← RingHom.comp_assoc, lsScale_rat, RingHom.comp_assoc, RingHom.comp_assoc,
      ratInv_ratScale 2 h2]
  · ext a; simp only [RingHom.comp_apply, ratInv_C, alg_C]
  · ext a; simp only [RingHom.comp_apply, alg_C]

end GlobalTheory.Nef.InfScale
end

section

open IsLocalRing

theorem _root_.GlobalTheory.T.exists_prime_not_mem_forall_gt_eq_maximalIdeal' : ∀ (C : Type) [CommRing C] [IsDomain C] [IsLocalRing C] [IsNoetherianRing C] (x : C), x ≠ 0 → x ∈ maximalIdeal C → ∃ q : Ideal C, q.IsPrime ∧ x ∉ q ∧ ∀ P : Ideal C, P.IsPrime → q < P → P = maximalIdeal C := by
  first | exact @GlobalTheory.exists_prime_not_mem_forall_gt_eq_maximalIdeal | exact GlobalTheory.exists_prime_not_mem_forall_gt_eq_maximalIdeal | (intros; apply GlobalTheory.exists_prime_not_mem_forall_gt_eq_maximalIdeal <;> assumption)
end

section

open IsDedekindDomain

namespace GlobalTheory

theorem finite_quotient_jacobson_of_finite_residueField (O : Type) [CommRing O] [IsLocalRing O]
    [Finite (IsLocalRing.ResidueField O)] (A : Type) [CommRing A] [Algebra O A]
    [Module.Finite O A] : Finite (A ⧸ (⊥ : Ideal A).jacobson) := by
  set J : Ideal A := (⊥ : Ideal A).jacobson with hJ

  have hm : ∀ m ∈ IsLocalRing.maximalIdeal O, algebraMap O A m ∈ J := by
    intro m hm
    rw [hJ, Ideal.jacobson, Ideal.mem_sInf]
    rintro M ⟨-, hM⟩
    have : (M.comap (algebraMap O A)).IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := O) M
    have h := IsLocalRing.eq_maximalIdeal this
    have : m ∈ M.comap (algebraMap O A) := h ▸ hm
    exact this
  have hfin : Module.Finite O (A ⧸ J) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ O J).toLinearMap Ideal.Quotient.mk_surjective
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := O) (M := A ⧸ J)
  have hsurj : Function.Surjective (IsLocalRing.residue O) := Ideal.Quotient.mk_surjective
  let f : (Fin n → IsLocalRing.ResidueField O) → A ⧸ J :=
    fun y ↦ ∑ i, Function.surjInv hsurj (y i) • s i
  have : Function.Surjective f := by
    intro q
    have hq : q ∈ Submodule.span O (Set.range s) := hs ▸ Submodule.mem_top
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 hq
    refine ⟨fun i ↦ IsLocalRing.residue O (c i), ?_⟩
    simp only [f]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hd : Function.surjInv hsurj (IsLocalRing.residue O (c i)) - c i ∈
        IsLocalRing.maximalIdeal O := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, Function.surjInv_eq hsurj, sub_self]
    rw [← sub_eq_zero, ← sub_smul, Algebra.smul_def]
    have h0 : algebraMap O (A ⧸ J) (Function.surjInv hsurj (IsLocalRing.residue O (c i)) - c i)
        = 0 := by
      rw [IsScalarTower.algebraMap_apply O A (A ⧸ J), Ideal.Quotient.algebraMap_eq,
        Ideal.Quotient.eq_zero_iff_mem]
      exact hm _ hd
    rw [h0, zero_mul]
  exact Finite.of_surjective f this

theorem exists_isUnit_mul_sub_mem_jacobson_of_finite_residueField :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [Finite (IsLocalRing.ResidueField O)] (A : Type)
      [CommRing A] [Algebra O A] [Module.Finite O A] (τ : A →+* A), (∀ a, τ (τ a) = a) →
      ∀ θ : A, IsUnit (θ - τ θ) → ∀ a : A, IsUnit a → τ a = a →
      ∃ t : A, IsUnit t ∧ t * τ t - a ∈ (⊥ : Ideal A).jacobson := by
  intro O _ _ _ A _ _ _ τ hτ θ hθ a ha hτa
  set J : Ideal A := (⊥ : Ideal A).jacobson with hJ
  have : Finite (A ⧸ J) := finite_quotient_jacobson_of_finite_residueField O A
  have : IsReduced (A ⧸ J) := by
    refine ⟨fun x ⟨k, hk⟩ ↦ ?_⟩
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem] at hk
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.isRadical_jacobson ⊥ ⟨k, hk⟩)
  have hτJ : J ≤ J.comap τ := by
    intro x hx
    rw [Ideal.mem_comap, hJ, Ideal.mem_jacobson_bot] at *
    intro b
    have h := (hx (τ b)).map τ
    simpa [hτ] using h
  let τ' : A ⧸ J →+* A ⧸ J := Ideal.quotientMap J τ hτJ
  have hτ' : ∀ x, τ' (Ideal.Quotient.mk J x) = Ideal.Quotient.mk J (τ x) := fun x ↦
    Ideal.quotientMap_mk
  have hinv : ∀ x, τ' (τ' x) = x := by
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hτ', hτ', hτ]
  obtain ⟨c, hc⟩ := norm_surj_of_finite_reduced_involution (A ⧸ J) τ' hinv
    (Ideal.Quotient.mk J θ) (by rw [hτ', ← map_sub]; exact hθ.map _)
    (Ideal.Quotient.mk J a) (ha.map _) (by rw [hτ', hτa])
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective c
  refine ⟨t, isUnit_of_isUnit_mk_of_le_jacobson le_rfl ?_, ?_⟩
  · have : IsUnit (τ' (Ideal.Quotient.mk J t) * Ideal.Quotient.mk J t) := hc ▸ ha.map _
    exact isUnit_of_mul_isUnit_right this
  · rw [← Ideal.Quotient.eq, map_mul, ← hτ', mul_comm, hc]

end GlobalTheory
end

section


theorem _root_.GlobalTheory.T.localization_preserves_ring_pullback_square : ∀ {A R₀ A' B₀ : Type} [CommRing A] [CommRing R₀] [CommRing A'] [CommRing B₀]
    (φ : A →+* R₀) (ψ : A →+* A') (α : R₀ →+* B₀) (κ : A' →+* B₀), α.comp φ = κ.comp ψ →
    (∀ a, φ a = 0 → ψ a = 0 → a = 0) → (∀ r c, α r = κ c → ∃ a, φ a = r ∧ ψ a = c) →
    ∀ (s : A) (LA LR LA' LB : Type) [CommRing LA] [CommRing LR] [CommRing LA'] [CommRing LB]
    [Algebra A LA] [Algebra R₀ LR] [Algebra A' LA'] [Algebra B₀ LB]
    [IsLocalization.Away s LA] [IsLocalization.Away (φ s) LR] [IsLocalization.Away (ψ s) LA']
    [IsLocalization.Away (α (φ s)) LB]
    (Φ : LA →+* LR) (Ψ : LA →+* LA') (Aα : LR →+* LB) (Kκ : LA' →+* LB),
    Φ.comp (algebraMap A LA) = (algebraMap R₀ LR).comp φ →
    Ψ.comp (algebraMap A LA) = (algebraMap A' LA').comp ψ →
    Aα.comp (algebraMap R₀ LR) = (algebraMap B₀ LB).comp α →
    Kκ.comp (algebraMap A' LA') = (algebraMap B₀ LB).comp κ →
    (∀ t, Φ t = 0 → Ψ t = 0 → t = 0) ∧ ∀ a b, Aα a = Kκ b → ∃ t, Φ t = a ∧ Ψ t = b := by
  first | exact @GlobalTheory.locPullback | exact GlobalTheory.locPullback | (intros; apply GlobalTheory.locPullback <;> assumption)
end

section


theorem _root_.GlobalTheory.T.finsum_ord_mul_inertiaDeg_eq_finrank_mul_ord' : ∀ (A B : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B], Function.Injective (algebraMap A B) → ringKrullDim A = 1 → ∀ a : A, a ≠ 0 → ∑ᶠ Q ∈ {Q : PrimeSpectrum B | Q.asIdeal.comap (algebraMap A B) = IsLocalRing.maximalIdeal A}, ((Ring.ord (Localization.AtPrime Q.asIdeal) (algebraMap B _ (algebraMap A B a))).toNat : ℤ) * (Q.asIdeal.inertiaDeg A : ℤ) = (Module.finrank A B : ℤ) * ((Ring.ord A a).toNat : ℤ) := by
  first | exact @GlobalTheory.finsum_ord_mul_inertiaDeg_eq_finrank_mul_ord | exact GlobalTheory.finsum_ord_mul_inertiaDeg_eq_finrank_mul_ord | (intros; apply GlobalTheory.finsum_ord_mul_inertiaDeg_eq_finrank_mul_ord <;> assumption)
end

section

open IsLocalRing TensorProduct

theorem _root_.GlobalTheory.T.exists_regular_near_of_regular_quotient_prime : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (p : Ideal B) [p.IsPrime], IsRegularLocalRing (Localization.AtPrime p) → ∃ g, g ∉ p ∧ ∀ (q : Ideal B) [q.IsPrime], p ≤ q → g ∉ q → IsRegularLocalRing (Localization.AtPrime q ⧸ p.map (algebraMap B (Localization.AtPrime q))) → IsRegularLocalRing (Localization.AtPrime q) := by
  first | exact @GlobalTheory.RegularAscent.exists_regular_near_of_regular_quotient | exact GlobalTheory.RegularAscent.exists_regular_near_of_regular_quotient | (intros; apply GlobalTheory.RegularAscent.exists_regular_near_of_regular_quotient <;> assumption)
end

section

namespace GlobalTheory

theorem prime_algebraMap_localization_of_isRegularRing_quotient :
    ∀ (A : Type) [CommRing A] [IsDomain A] (P : Ideal A) [P.IsPrime] (x : A), x ≠ 0 → x ∈ P →
      IsRegularRing (A ⧸ Ideal.span {x}) → Prime (algebraMap A (Localization.AtPrime P) x) := by
  intro A _ _ P _ x hx hxP hreg
  set R := Localization.AtPrime P
  set J : Ideal A := Ideal.span {x} with hJdef
  have hJP : RingHom.ker (Ideal.Quotient.mk J) ≤ P := by
    rw [Ideal.mk_ker, hJdef, Ideal.span_le, Set.singleton_subset_iff]; exact hxP
  have hle : J ≤ (J.map (algebraMap A R)).comap (algebraMap A R) := Ideal.le_comap_map
  letI : Algebra (A ⧸ J) (R ⧸ J.map (algebraMap A R)) := (Ideal.quotientMap _ _ hle).toAlgebra
  have hl := IsLocalization.of_surjective P.primeCompl R (S' := R ⧸ J.map (algebraMap A R))
    (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective rfl
    (by rw [Ideal.mk_ker, Ideal.mk_ker])
  have hm : (P.map (Ideal.Quotient.mk J)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hJP
  have e : P.primeCompl.map (Ideal.Quotient.mk J) = (P.map (Ideal.Quotient.mk J)).primeCompl := by
    have hc : (P.map (Ideal.Quotient.mk J)).comap (Ideal.Quotient.mk J) = P := by
      rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, sup_eq_left.2 hJP]
    ext y
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    constructor
    · rintro ⟨z', hz', e⟩ hz
      exact hz' (hc.le (show Ideal.Quotient.mk J z' ∈ _ from e ▸ hz))
    · exact fun hz => ⟨z, fun h => hz (Ideal.mem_map_of_mem _ h), rfl⟩
  rw [e] at hl
  have := IsRegularRing.isRegularLocalRing_localization (P.map (Ideal.Quotient.mk J))
  haveI : IsRegularLocalRing (R ⧸ J.map (algebraMap A R)) :=
    IsRegularLocalRing.of_ringEquiv (IsLocalization.algEquiv (P.map (Ideal.Quotient.mk J)).primeCompl
      (Localization.AtPrime (P.map (Ideal.Quotient.mk J))) _).toRingEquiv
  have hdom : IsDomain (R ⧸ J.map (algebraMap A R)) :=
    (isDomain_and_isIntegrallyClosed_of_isRegularLocalRing _).1
  have hmap : J.map (algebraMap A R) = Ideal.span {algebraMap A R x} := by
    rw [hJdef, Ideal.map_span, Set.image_singleton]
  rw [hmap] at hdom
  have hprime : (Ideal.span {algebraMap A R x}).IsPrime := (Ideal.Quotient.isDomain_iff_prime _).1 hdom
  have hne : algebraMap A R x ≠ 0 := by
    intro h0
    apply hx
    exact IsLocalization.injective R (P.primeCompl_le_nonZeroDivisors) (by simpa using h0)
  exact (Ideal.span_singleton_prime hne).1 hprime

end GlobalTheory
end
