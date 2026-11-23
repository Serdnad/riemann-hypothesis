module

public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle381
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle372
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle382
public import Mathlib.RingTheory.Bialgebra.Hom
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle090
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle128
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle383
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle240
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle236
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle182
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle384
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle385
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle314
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle228
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus

@[expose] public section

section

open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology

theorem _root_.GlobalTheory.T.infinitePlace_completion_nhdsNE_zero_neBot : ∀ (F : Type) [Field F] [NumberField F] (w : InfinitePlace F), (𝓝[≠] (0 : w.Completion)).NeBot := by
  first | exact @GlobalTheory.QSA.infinitePlace_completion_nhdsNE_neBot | exact GlobalTheory.QSA.infinitePlace_completion_nhdsNE_neBot | (intros; apply GlobalTheory.QSA.infinitePlace_completion_nhdsNE_neBot <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

theorem _root_.GlobalTheory.T.norm_cm_type_product_sq : ∀ (E : Type) [Field E] [NumberField E] (Ψ : Finset (E →+* ℂ)), (∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) → ∀ d : E, ‖∏ τ : Ψ, τ.1 d‖ ^ 2 = |((Algebra.norm ℚ d : ℚ) : ℝ)| := by
  first | exact @GlobalTheory.cm_type_normSq_prod_eq_abs_norm | exact GlobalTheory.cm_type_normSq_prod_eq_abs_norm | (intros; apply GlobalTheory.cm_type_normSq_prod_eq_abs_norm <;> assumption)
end

section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem _root_.GlobalTheory.T.polynomial_ring_irreducible_prime_reduction : ∀ (k F : Type) [Field k] [Field F] [Algebra k F] (d : ℕ) (u : Fin d → F), AlgebraicIndependent k u → ∀ (A : Subalgebra k F), A = Algebra.adjoin k (Set.range u) → ∀ t : A, Irreducible t → Prime t ∧ ∃ m : ℕ, d = m + 1 ∧ ∃ y : Fin m → A, IsTranscendenceBasis k (fun j => Ideal.Quotient.mk (Ideal.span {t}) (y j)) := by
  first | (exact @GlobalTheory.TrBasisQuot.trBasis_mod_irreducible) | (exact GlobalTheory.TrBasisQuot.trBasis_mod_irreducible) | (intros; apply GlobalTheory.TrBasisQuot.trBasis_mod_irreducible  <;> assumption)
end

section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem _root_.GlobalTheory.T.isTranscendenceBasis_quotient_integralClosure' : ∀ (k F K : Type) [Field k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (A : Subalgebra k F) (B : Subalgebra k K), B = (integralClosure A K).restrictScalars k → ∀ (Q : Ideal B), Q.IsPrime → ∀ (t : A), (∀ (a : A) (b : B), (b : K) = algebraMap F K a → (b ∈ Q ↔ t ∣ a)) → ∀ (m : ℕ) (y : Fin m → A), IsTranscendenceBasis k (fun j => Ideal.Quotient.mk (Ideal.span {t}) (y j)) → ∀ y' : Fin m → B, (∀ j, (y' j : K) = algebraMap F K (y j)) → IsTranscendenceBasis k (fun j => Ideal.Quotient.mk Q (y' j)) := by
  first | (exact @GlobalTheory.isTranscendenceBasis_quotient_integralClosure) | (exact GlobalTheory.isTranscendenceBasis_quotient_integralClosure) | (intros; apply GlobalTheory.isTranscendenceBasis_quotient_integralClosure <;> assumption)
end

section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential



theorem GlobalTheory.span_D_lift_clear_denominators : ∀ (k K L : Type) [Field k] [CharZero k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L] (B : Subalgebra k K) [Algebra.FiniteType k B] (Q : Ideal B), Q.IsPrime → ∀ s : B, s ∈ Q → s ≠ 0 → (∀ y ∈ Q, ∃ c r : B, r ∉ Q ∧ r * y = c * s) → ∀ (m : ℕ) (y : Fin m → B), IsTranscendenceBasis k (fun j => Ideal.Quotient.mk Q (y j)) → ∀ v : B, ∃ r : B, r ∉ Q ∧ ∃ c : Fin (m + 1) → B, algebraMap K L (r : K) • D k L (algebraMap K L (v : K)) = ∑ l, algebraMap K L (c l : K) • (Fin.cons (D k L (algebraMap K L (s : K))) (fun j => D k L (algebraMap K L (y j : K))) : Fin (m + 1) → Ω[L⁄k]) l := by
  intro k K L _ _ _ _ _ _ _ _ B _ Q hQ s hsQ hs0 hgen m y hy v
  classical
  let R := Localization.AtPrime Q
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  haveI : IsNoetherianRing R := IsLocalization.isNoetherianRing Q.primeCompl R inferInstance
  have hinj : Function.Injective (algebraMap B R) :=
    IsLocalization.injective R Q.primeCompl_le_nonZeroDivisors
  have hmax : IsLocalRing.maximalIdeal R = Ideal.span {algebraMap B R s} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro z hz
      obtain ⟨c, r, hr, hrc⟩ := hgen z hz
      rw [Ideal.mem_comap, Ideal.mem_span_singleton']
      refine ⟨IsLocalization.mk' R c (⟨r, hr⟩ : Q.primeCompl), ?_⟩
      have hu := IsLocalization.map_units R (⟨r, hr⟩ : Q.primeCompl)
      apply hu.mul_left_cancel
      rw [← mul_assoc, IsLocalization.mk'_spec', ← map_mul, ← map_mul]
      exact congrArg _ hrc.symm
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.mem_map_of_mem _ hsQ
  have hs0' : algebraMap B R s ≠ 0 := fun h => hs0 (hinj (by rw [h, map_zero]))
  have hnf : ¬ IsField R := by
    intro hf
    have h1 := IsLocalRing.isField_iff_maximalIdeal_eq.1 hf
    rw [hmax, Ideal.span_singleton_eq_bot] at h1
    exact hs0' h1
  have hprin : Submodule.IsPrincipal (IsLocalRing.maximalIdeal R) := ⟨⟨_, hmax⟩⟩
  haveI : IsDiscreteValuationRing R := ((IsDiscreteValuationRing.TFAE R hnf).out 1 5).2 hprin
  have hirr : Irreducible (algebraMap B R s) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 hmax
  haveI : IsDomain (B ⧸ Q) := Ideal.Quotient.isDomain Q
  haveI : Nontrivial (B ⧸ Q) := IsDomain.toNontrivial
  haveI : Algebra.IsAlgebraic (B ⧸ Q) Q.ResidueField :=
    IsLocalization.isAlgebraic (R := B ⧸ Q) (S := Q.ResidueField) (M := nonZeroDivisors (B ⧸ Q))
  haveI : FaithfulSMul (B ⧸ Q) Q.ResidueField :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (IsFractionRing.injective _ _)
  have htb : IsTranscendenceBasis k (fun j => IsLocalRing.residue R (algebraMap B R (y j))) := by
    have h2 := hy.algebraMap_comp (A := Q.ResidueField)
    convert h2 using 1
    rfl
  have hspan := GlobalTheory.span_D_uniformizer_transcendenceBasis k R (algebraMap B R s) hirr m
    (fun j => algebraMap B R (y j)) htb
  have hunit : ∀ z : Q.primeCompl, IsUnit (algebraMap B K z) := fun z => by
    refine isUnit_iff_ne_zero.2 fun h => z.2 ?_
    have hz : (z : B) = 0 := Subtype.ext h
    rw [hz]; exact Q.zero_mem
  let ψ : R →+* K := IsLocalization.lift hunit
  letI : Algebra R L := ((algebraMap K L).comp ψ).toAlgebra
  have hRL : ∀ x : B, algebraMap R L (algebraMap B R x) = algebraMap K L (x : K) := fun x => by
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, IsLocalization.lift_eq]
    rfl
  haveI : IsScalarTower k R L := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply k B R, hRL, IsScalarTower.algebraMap_apply k K L]
    rfl
  haveI : SMulCommClass k R L := inferInstance
  let Φ := KaehlerDifferential.map k k R L
  let g : Fin (m + 1) → Ω[R⁄k] := Fin.cons (D k R (algebraMap B R s)) (fun j => D k R (algebraMap B R (y j)))
  have hDv : D k R (algebraMap B R v) ∈ Submodule.span R (Set.range g) := by
    rw [Fin.range_cons, hspan]; exact Submodule.mem_top
  obtain ⟨c', hc'⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hDv
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples Q.primeCompl (Finset.univ : Finset (Fin (m + 1))) c'
  have hb' : ∀ l, ∃ x : B, algebraMap B R x = algebraMap B R (b : B) * c' l := fun l => by
    obtain ⟨x, hx⟩ := hb l (Finset.mem_univ l)
    exact ⟨x, by rw [hx, Algebra.smul_def]⟩
  choose c hc using hb'
  have hΦD : ∀ x : B, Φ (D k R (algebraMap B R x)) = D k L (algebraMap K L (x : K)) := fun x => by
    rw [KaehlerDifferential.map_D, hRL]
  have hΦg : ∀ l, Φ (g l) = (Fin.cons (D k L (algebraMap K L (s : K))) (fun j => D k L (algebraMap K L (y j : K))) : Fin (m + 1) → Ω[L⁄k]) l := by
    intro l
    refine Fin.cases ?_ (fun j => ?_) l
    · simp only [g, Fin.cons_zero]; exact hΦD s
    · simp only [g, Fin.cons_succ]; exact hΦD (y j)
  refine ⟨b, b.2, c, ?_⟩

  rw [← hRL, ← hΦD, algebraMap_smul, ← map_smul, ← hc', Finset.smul_sum, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← hRL, ← hΦg, algebraMap_smul L (algebraMap B R (c l)) (Φ (g l)), ← map_smul Φ]
  congr 1
  rw [hc, mul_smul]
end

section

open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup Coalgebra Bialgebra

namespace GlobalTheory.PDiv

theorem faithfullyFlat_range_of_hopf_finite (k A B : Type) [Field k] [CommRing A] [CommRing B]
    [HopfAlgebra k A] [HopfAlgebra k B] [Module.Finite k A] (f : B →ₐc[k] A) :
    Module.FaithfullyFlat (AlgHom.range (f : B →ₐ[k] A)) A := by
  obtain ⟨e⟩ := GlobalTheory.HopfShear.shear k A B f
  haveI : Module.Finite k (AlgHom.range (f : B →ₐ[k] A)) :=
    Module.Finite.of_injective (AlgHom.range (f : B →ₐ[k] A)).val.toLinearMap
      Subtype.val_injective
  haveI : Module.Finite (AlgHom.range (f : B →ₐ[k] A)) A :=
    Module.Finite.of_restrictScalars_finite k _ A
  haveI : IsArtinianRing (AlgHom.range (f : B →ₐ[k] A)) := IsArtinianRing.of_finite k _
  obtain ⟨b⟩ := GlobalTheory.nonempty_basis_of_basis_baseChange (B := AlgHom.range (f : B →ₐ[k] A))
    (A := A) (M := A) Subtype.val_injective (((Module.finBasis k _).baseChange A).map e.symm)
  haveI := Module.Free.of_basis b
  haveI : Nontrivial A := (counitAlgHom k A).domain_nontrivial
  infer_instance

theorem comap_map_eq_self_of_hopf_injective : ∀ (k A B : Type) [Field k] [CommRing A] [CommRing B] [HopfAlgebra k A] [HopfAlgebra k B] [Module.Finite k A] (f : B →ₐc[k] A), Function.Injective f → ∀ J : Ideal B, Ideal.comap (f : B →ₐ[k] A) (Ideal.map (f : B →ₐ[k] A) J) = J := by
  intro k A B _ _ _ _ _ _ f hf J
  haveI := faithfullyFlat_range_of_hopf_finite k A B f
  let g : B →+* AlgHom.range (f : B →ₐ[k] A) := (f : B →ₐ[k] A).rangeRestrict.toRingHom
  have hg : Function.Bijective g :=
    ⟨fun x y h => hf (congrArg Subtype.val h), (f : B →ₐ[k] A).rangeRestrict_surjective⟩
  have h := Ideal.comap_map_eq_self_of_faithfullyFlat (B := A) (Ideal.map g J)
  rw [Ideal.map_map] at h
  have h2 := congrArg (Ideal.comap g) h
  rw [Ideal.comap_comap, Ideal.comap_map_of_bijective g hg] at h2
  exact h2

end GlobalTheory.PDiv
end

section

open IsLocalRing GlobalTheory.FormalOrigin GlobalTheory.FormalOrigin.Extend

theorem _root_.GlobalTheory.T.exists_coeffwise_derivation_mvPowerSeries : ∀ (σ R : Type) [CommRing R] (D : Derivation ℤ R R), ∃ E : Derivation ℤ (MvPowerSeries σ R) (MvPowerSeries σ R), ∀ F α, MvPowerSeries.coeff α (E F) = D (MvPowerSeries.coeff α F) := by
  first | exact @GlobalTheory.mvPowerSeries_derivation_coeffwise | exact GlobalTheory.mvPowerSeries_derivation_coeffwise | (intros; apply GlobalTheory.mvPowerSeries_derivation_coeffwise <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out


theorem _root_.GlobalTheory.T.exists_complete_dvr_integralClosure_finite_fractionRing : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ (K' : Type) [Field K'] (σ : FractionRing V →+* K'), σ.Finite → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : CharZero V') (f : V →+* V') (τ : K' →+* FractionRing V'), IsAdicComplete (maximalIdeal V') V' ∧ Function.Injective f ∧ IsLocalHom f ∧ f.Finite ∧ ∀ a, τ (σ (algebraMap V _ a)) = algebraMap V' _ (f a) := by
  first | exact @GlobalTheory.exists_complete_dvr_of_finite_fractionRing_hom | exact GlobalTheory.exists_complete_dvr_of_finite_fractionRing_hom | (intros; apply GlobalTheory.exists_complete_dvr_of_finite_fractionRing_hom <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out


theorem _root_.GlobalTheory.T.ideal_map_eq_span_pow_uniformizer_dvr : ∀ (V W : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (f : V →+* W), Function.Injective f → ∀ (ϖ : V) (w : W) (e a : ℕ) (I : Ideal V), Irreducible ϖ → Irreducible w → Associated (f ϖ) (w ^ e) → I.map f = Ideal.span {w ^ a} → ∃ b : ℕ, e * b = a ∧ I = Ideal.span {ϖ ^ b} := by
  first | exact @GlobalTheory.ideal_map_eq_span_pow_uniformizer | exact GlobalTheory.ideal_map_eq_span_pow_uniformizer | (intros; apply GlobalTheory.ideal_map_eq_span_pow_uniformizer <;> assumption)
end

section

open IsLocalRing TensorProduct

namespace GlobalTheory.EtaleCoker

theorem main : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R] (A B : Type) [CommRing A] [Algebra R A] [Module.Finite R A] [CommRing B] [Algebra R B] [Module.Finite R B], (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) → (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) B)) → ∀ ψ : A →ₐ[R] B, Function.Injective ψ → (∃ s : R, s ≠ 0 ∧ ∀ b : B, s • b ∈ ψ.range) → ∃ k : ℕ, ∀ x ∈ maximalIdeal R ^ k, ∀ b : B, x • b ∈ ψ.range := by
  intro R _ _ _ _ A B _ _ _ _ _ _ hA hB ψ hψ ⟨s, hs, hsb⟩
  obtain ⟨k, hk⟩ := GlobalTheory.T.smul_mem_of_maximalIdeal_pow_of_locally_surjective R B (ψ.range.toSubmodule.restrictScalars R) (fun p hp hpm => by
    haveI := hp
    haveI := hA p hpm
    haveI := hB p hpm
    let S := Localization.AtPrime p
    haveI : Module.Free S (S ⊗[R] A) := Module.free_of_flat_of_isLocalRing
    haveI : Module.Free S (S ⊗[R] B) := Module.free_of_flat_of_isLocalRing
    obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.localization_tensor_map_injective_coker_killed R A B p ψ hψ s hs hsb
    have htr := GlobalTheory.T.algebra_trace_map_of_cokernel_killed_by_scalar S _ _ _ h1 _ h2 h3
    exact GlobalTheory.T.exists_smul_mem_range_of_surjective_localized_map R A B p ψ (GlobalTheory.T.surjective_of_injective_of_trace_eq_of_smul_mem_range S _ _ _ h1 _ h2 h3 htr))
  exact ⟨k, fun x hx b => hk x hx b⟩

end GlobalTheory.EtaleCoker
end

section

open IsLocalRing

theorem _root_.GlobalTheory.T.flat_of_essentiallyEtale_local_algebras : ∀ (R L₁ L₂ : Type) [CommRing R] [CommRing L₁] [CommRing L₂] [Algebra R L₁] [Algebra R L₂] [Algebra L₁ L₂] [IsScalarTower R L₁ L₂], (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] L₁)) → (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] L₂)) → Module.Flat L₁ L₂ := by
  first | exact @GlobalTheory.flat_of_essEtale | exact GlobalTheory.flat_of_essEtale | (intros; apply GlobalTheory.flat_of_essEtale <;> assumption)
end

section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.divisor_descent_flat_normal_domains : ∀ (A' B' : Type) [CommRing A'] [IsDomain A'] [IsNoetherianRing A'] [IsIntegrallyClosed A']
    [CommRing B'] [IsDomain B'] [IsNoetherianRing B'] [IsIntegrallyClosed B'] [Algebra A' B']
    [Module.Flat A' B'] (s : A'), s ≠ 0 →
    (∀ 𝔭 : Ideal A', 𝔭.IsPrime → 𝔭.height = 1 → s ∈ 𝔭 → (𝔭.map (algebraMap A' B')).IsPrime) →
    ∀ b c : B', b * c = algebraMap A' B' s →
    b ∈ ((Ideal.span {b}).comap (algebraMap A' B')).map (algebraMap A' B') := by
  first | (exact @GlobalTheory.DivDescent.divisor_descent) | (exact GlobalTheory.DivDescent.divisor_descent) | (intros; apply GlobalTheory.DivDescent.divisor_descent <;> assumption)
end
