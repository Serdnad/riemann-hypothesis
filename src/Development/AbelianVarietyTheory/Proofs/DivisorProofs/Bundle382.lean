module

public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle008
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle036
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedOfIsIntegral
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle320
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle239
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle315
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle317
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
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure

@[expose] public section

section

open IsLocalRing

namespace GlobalTheory.CompletionEmbed

variable (p : ℕ) [Fact p.Prime] (C : Type) [CommRing C] [IsLocalRing C]

noncomputable def levelMap (hpm : (p : C) ∈ maximalIdeal C) (n : ℕ) :
    ℤ_[p] →+* C ⧸ maximalIdeal C ^ n :=
  have h : ((p ^ n : ℕ) : C ⧸ maximalIdeal C ^ n) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (maximalIdeal C ^ n)), Ideal.Quotient.eq_zero_iff_mem,
      Nat.cast_pow]
    exact Ideal.pow_mem_pow hpm n
  (ZMod.castHom (ringChar.dvd h) (C ⧸ maximalIdeal C ^ n)).comp (PadicInt.toZModPow n)

theorem levelMap_compat (hpm : (p : C) ∈ maximalIdeal C) {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (maximalIdeal C) hle).comp (levelMap p C hpm n) =
      levelMap p C hpm m := by
  unfold levelMap
  rw [← PadicInt.zmod_cast_comp_toZModPow m n hle, ← RingHom.comp_assoc, ← RingHom.comp_assoc]
  congr 1
  exact Subsingleton.elim _ _

noncomputable def toCompletion (hpm : (p : C) ∈ maximalIdeal C) :
    ℤ_[p] →+* AdicCompletion (maximalIdeal C) C :=
  AdicCompletion.liftRingHom (maximalIdeal C) (levelMap p C hpm)
    (fun hle => levelMap_compat p C hpm hle)

theorem algebraMap_injective [IsNoetherianRing C] :
    Function.Injective (algebraMap C (AdicCompletion (maximalIdeal C) C)) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  have hmem : x ∈ ⨅ n : ℕ, maximalIdeal C ^ n := by
    rw [Submodule.mem_iInf]
    intro n
    have := congrArg (AdicCompletion.evalₐ (maximalIdeal C) n) hx
    rw [map_zero] at this
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simpa using this
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal C).ne_top] at hmem
  exact hmem

theorem exists_pow_le_span [IsNoetherianRing C] (hp0 : (p : C) ≠ 0)
    (hprime : ∀ P : Ideal C, P.IsPrime → P ≠ ⊥ → P = maximalIdeal C) :
    ∃ N : ℕ, maximalIdeal C ^ N ≤ Ideal.span {(p : C)} := by
  refine Ideal.exists_pow_le_of_le_radical_of_fg ?_ (IsNoetherian.noetherian _)
  rw [Ideal.radical_eq_sInf]
  refine le_sInf fun Q ⟨hle, hQ⟩ => ?_
  have hQ0 : Q ≠ ⊥ := fun h => hp0 (by
    have := hle (Ideal.mem_span_singleton_self _)
    rw [h] at this
    exact (Ideal.mem_bot).mp this)
  rw [hprime Q hQ hQ0]

theorem finite_quot_span [IsNoetherianRing C] [Finite (ResidueField C)] (hp0 : (p : C) ≠ 0)
    (hprime : ∀ P : Ideal C, P.IsPrime → P ≠ ⊥ → P = maximalIdeal C) :
    Finite (AdicCompletion (maximalIdeal C) C ⧸
      Ideal.span {(p : AdicCompletion (maximalIdeal C) C)}) := by
  set A := AdicCompletion (maximalIdeal C) C
  have fg : (maximalIdeal C).FG := IsNoetherian.noetherian _
  haveI : Finite (C ⧸ maximalIdeal C) := ‹Finite (ResidueField C)›
  haveI : Finite (A ⧸ (maximalIdeal C).map (algebraMap C A)) := by
    have h := Finite.of_injective _
      (RingHom.kerLift_injective (AdicCompletion.evalOneₐ (maximalIdeal C)).toRingHom)
    rw [AdicCompletion.ker_evalOneₐ_eq_map _ fg] at h
    exact h
  obtain ⟨N, hN⟩ := exists_pow_le_span p C hp0 hprime
  haveI : Finite (A ⧸ ((maximalIdeal C).map (algebraMap C A)) ^ N) :=
    Ideal.finite_quotient_pow (fg.map _) N
  have hle : ((maximalIdeal C).map (algebraMap C A)) ^ N ≤ Ideal.span {(p : A)} := by
    rw [← Ideal.map_pow]
    calc _ ≤ (Ideal.span {(p : C)}).map (algebraMap C A) := Ideal.map_mono hN
      _ = _ := by rw [Ideal.map_span, Set.image_singleton, map_natCast]
  exact Finite.of_surjective _ (Ideal.Quotient.factor_surjective hle)

end GlobalTheory.CompletionEmbed


open IsLocalRing GlobalTheory.CompletionEmbed in
theorem GlobalTheory.CompletionEmbed.exists_finite_padicInt_domain :
    ∀ (p : ℕ) [Fact p.Prime] (C : Type) [CommRing C] [IsDomain C] [IsLocalRing C]
      [IsNoetherianRing C], Finite (ResidueField C) → (p : C) ≠ 0 → (p : C) ∈ maximalIdeal C →
      (∀ P : Ideal C, P.IsPrime → P ≠ ⊥ → P = maximalIdeal C) →
      ∃ (D : Type) (_ : CommRing D) (_ : IsDomain D) (_ : Algebra ℤ_[p] D),
        Module.Finite ℤ_[p] D ∧ ∃ ι : C →+* D, Function.Injective ι := by
  intro p _ C _ _ _ _ hfin hp0 hpm hprime
  set A := AdicCompletion (maximalIdeal C) C
  haveI : IsNoetherianRing A := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion C _
  letI : Algebra ℤ_[p] A := (toCompletion p C hpm).toAlgebra
  have hJ : (maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] A) = Ideal.span {(p : A)} := by
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton, map_natCast]
  haveI : Finite (A ⧸ Ideal.span {(p : A)}) := finite_quot_span p C hp0 hprime
  have hne : Ideal.span {(p : A)} ≠ ⊤ := by
    intro h
    have hu : IsUnit (p : A) := Ideal.span_singleton_eq_top.mp h
    have hu' := hu.map (AdicCompletion.evalOneₐ (maximalIdeal C))
    rw [map_natCast, ← map_natCast (Ideal.Quotient.mk (maximalIdeal C)),
      Ideal.Quotient.eq_zero_iff_mem.mpr hpm] at hu'
    exact not_isUnit_zero hu'
  haveI : Module.Finite ℤ_[p] A := by
    refine GlobalTheory.finite_of_finite_quot_map_of_isPrecomplete ℤ_[p] A (maximalIdeal ℤ_[p]) ?_ ?_
    · rw [hJ]; exact hne
    · rw [hJ]; exact Module.Finite.of_finite
  have hnil : ¬ IsNilpotent (p : A) := by
    rintro ⟨n, hn⟩
    have h : algebraMap C A ((p : C) ^ n) = 0 := by rw [map_pow, map_natCast]; exact hn
    have h3 := (injective_iff_map_eq_zero _).mp (algebraMap_injective C) _ h
    exact hp0 (IsNilpotent.eq_zero ⟨n, h3⟩)
  obtain ⟨Q, hQ, hpQ⟩ : ∃ Q : Ideal A, Q.IsPrime ∧ (p : A) ∉ Q := by
    by_contra h
    push_neg at h
    exact hnil (nilpotent_iff_mem_prime.mpr h)
  haveI := hQ
  refine ⟨A ⧸ Q, inferInstance, inferInstance, inferInstance, ?_,
    (Ideal.Quotient.mk Q).comp (algebraMap C A), ?_⟩
  · exact Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℤ_[p] Q).toLinearMap
      (Ideal.Quotient.mkₐ_surjective ℤ_[p] Q)
  · set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    have hbot : Q.comap (algebraMap C A) = ⊥ := by
      by_contra hb
      have h1 := hprime _ (Ideal.comap_isPrime _ _) hb
      apply hpQ
      have h2 : (p : C) ∈ Q.comap (algebraMap C A) := by
        rw [h1]; exact hpm
      rw [Ideal.mem_comap, map_natCast] at h2
      exact h2
    have hx' : x ∈ Q.comap (algebraMap C A) := by
      rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
      exact hx
    rw [hbot] at hx'
    exact (Ideal.mem_bot).mp hx'
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

theorem GlobalTheory.closure_generic_fibre_clopen_split : ∀ (R A : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing A] [Algebra R A], Algebra.Smooth R A → ∀ C C' : Set (PrimeSpectrum A), C ∪ C' = {r | r.asIdeal.comap (algebraMap R A) = ⊥} → Disjoint C (closure C') → Disjoint (closure C) C' → Disjoint (closure C) (closure C') ∧ closure C ∪ closure C' = Set.univ := by
  intro R A _ _ _ _ _ hsm C C' hU hd1 hd2
  let K := FractionRing R
  let f : A →+* A ⊗[R] K := (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] K).toRingHom
  let φ := PrimeSpectrum.comap f
  have hφc : Continuous φ := PrimeSpectrum.continuous_comap f

  have hF : {r : PrimeSpectrum A | r.asIdeal.comap (algebraMap R A) = ⊥} = Set.range φ := by
    have h1 := GlobalTheory.T.range_comap_includeRight_eq_comap_eq_ker R A K
    have hker : RingHom.ker (algebraMap R K) = ⊥ :=
      (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R K)
    rw [hker] at h1
    rw [← h1]
    let e := (Algebra.TensorProduct.comm R A K).toRingEquiv
    have hg : (Algebra.TensorProduct.includeRight : A →ₐ[R] K ⊗[R] A).toRingHom = e.toRingHom.comp f := by
      ext a
      simp [f, e]
    rw [hg, PrimeSpectrum.comap_comp, Set.range_comp]
    have hsurj : Set.range (PrimeSpectrum.comap e.toRingHom) = Set.univ := by
      refine Set.eq_univ_of_forall fun y => ⟨PrimeSpectrum.comap e.symm.toRingHom y, ?_⟩
      rw [← PrimeSpectrum.comap_comp_apply, RingEquiv.symm_toRingHom_comp_toRingHom]
      rfl
    rw [hsurj, Set.image_univ]

  have hinj : Function.Injective f := by
    have hl := Module.Flat.lTensor_preserves_injective_linearMap (M := A) (Algebra.linearMap R K)
      (IsFractionRing.injective R K)
    intro x y hxy
    have : (LinearMap.lTensor A (Algebra.linearMap R K)) ((TensorProduct.rid R A).symm x) =
        (LinearMap.lTensor A (Algebra.linearMap R K)) ((TensorProduct.rid R A).symm y) := by
      simpa [f] using hxy
    exact (TensorProduct.rid R A).symm.injective (hl this)
  have hdense : DenseRange φ :=
    (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical f).2
      (by rw [(RingHom.injective_iff_ker_eq_bot f).1 hinj]; exact bot_le)
  have hCC' : Disjoint C C' := hd1.mono_right subset_closure
  have hunion : φ ⁻¹' C ∪ φ ⁻¹' C' = Set.univ := by
    rw [← Set.preimage_union, hU, hF, Set.preimage_range]
  have hcompl : IsCompl (φ ⁻¹' C) (φ ⁻¹' C') :=
    ⟨hCC'.preimage φ, codisjoint_iff.2 hunion⟩
  have hS1 : φ ⁻¹' closure C = φ ⁻¹' C := by
    refine Set.Subset.antisymm (fun x hx => ?_) (Set.preimage_mono subset_closure)
    have hx' : x ∈ φ ⁻¹' C ∪ φ ⁻¹' C' := hunion ▸ Set.mem_univ x
    rcases hx' with h | h
    · exact h
    · exact absurd h (Set.disjoint_left.1 hd2 hx)
  have hclosed : IsClosed (φ ⁻¹' C) := hS1 ▸ isClosed_closure.preimage hφc
  have hS2 : φ ⁻¹' closure C' = φ ⁻¹' C' := by
    refine Set.Subset.antisymm (fun x hx => ?_) (Set.preimage_mono subset_closure)
    have hx' : x ∈ φ ⁻¹' C ∪ φ ⁻¹' C' := hunion ▸ Set.mem_univ x
    rcases hx' with h | h
    · exact absurd hx (Set.disjoint_left.1 hd1 h)
    · exact h
  have hclosed' : IsClosed (φ ⁻¹' C') := hS2 ▸ isClosed_closure.preimage hφc
  have hopen : IsOpen (φ ⁻¹' C) := by
    rw [← isClosed_compl_iff, hcompl.compl_eq]; exact hclosed'
  obtain ⟨ε, hε, hεS⟩ := PrimeSpectrum.isClopen_iff.1 ⟨hclosed, hopen⟩
  obtain ⟨a, ha, haε⟩ := GlobalTheory.T.exists_idempotent_tmul_one_eq_of_smooth_algebra R A hsm ε hε
  have hfa : f a = ε := by simp [f, haε]
  have hpre : φ ⁻¹' (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A)) = φ ⁻¹' C := by
    rw [hεS, ← hfa]
    ext x
    simp [φ, PrimeSpectrum.mem_basicOpen]
  have hCa : C ⊆ (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A)) := by
    intro x hx
    have hxF : x ∈ Set.range φ := hF ▸ hU ▸ Or.inl hx
    obtain ⟨y, rfl⟩ := hxF
    have hy : y ∈ φ ⁻¹' C := hx
    rw [← hpre] at hy
    exact hy
  have hC'a : C' ⊆ (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A))ᶜ := by
    intro x hx
    have hxF : x ∈ Set.range φ := hF ▸ hU ▸ Or.inr hx
    obtain ⟨y, rfl⟩ := hxF
    have hy : y ∈ (φ ⁻¹' C)ᶜ := hcompl.compl_eq ▸ hx
    rw [← hpre] at hy
    exact hy
  have hclo : IsClopen (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A)) :=
    PrimeSpectrum.isClopen_iff.2 ⟨a, ha, rfl⟩
  refine ⟨?_, ?_⟩
  · exact (disjoint_compl_right (a := (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A)))).mono
      (closure_minimal hCa hclo.isClosed) (closure_minimal hC'a hclo.isOpen.isClosed_compl)
  · rw [← closure_union, hU, hF]
    exact hdense.closure_range
end

section

namespace GlobalTheory.AdicPackage

theorem adicCompletion_package : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (I : Ideal B),
    ∃ (C : Type) (_ : CommRing C) (φ : B →+* C), IsNoetherianRing C ∧ φ.Flat ∧
      IsAdicComplete (I.map φ) C ∧ ∀ (m : ℕ) (a : Ideal B), I ^ m ≤ a → (a.map φ).comap φ = a := by
  intro B _ _ I
  have fg : I.FG := IsNoetherian.noetherian I
  refine ⟨AdicCompletion I B, inferInstance, algebraMap B (AdicCompletion I B),
    GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion B I,
    RingHom.flat_algebraMap_iff.2 (AdicCompletion.flat_of_isNoetherian I),
    AdicCompletion.isAdicComplete_self I fg, ?_⟩
  intro m a h
  refine le_antisymm ?_ Ideal.le_comap_map
  have key : ∀ y : B, (AdicCompletion.evalₐ I m) (algebraMap B (AdicCompletion I B) y) =
      Ideal.Quotient.mk (I ^ m) y := fun y => (AdicCompletion.evalₐ I m).commutes y
  have hle : a.map (algebraMap B (AdicCompletion I B)) ≤
      (a.map (Ideal.Quotient.mk (I ^ m))).comap (AdicCompletion.evalₐ I m) := by
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    simp only [Ideal.mem_comap]
    rw [key]
    exact Ideal.mem_map_of_mem _ hy
  intro x hx
  rw [Ideal.mem_comap] at hx
  have h2 := hle hx
  rw [Ideal.mem_comap, key] at h2
  exact (Ideal.mem_quotient_iff_mem h).1 h2

end GlobalTheory.AdicPackage
end

section

set_option autoImplicit false

noncomputable section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential IsLocalRing TensorProduct

namespace GlobalTheory

theorem span_D_uniformizer_transcendenceBasis : ∀ (k R : Type) [Field k] [CharZero k] [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R] [Algebra k R] [Algebra.EssFiniteType k R] (s : R),
    Irreducible s → ∀ (m : ℕ) (y : Fin m → R),
    IsTranscendenceBasis k (fun j => IsLocalRing.residue R (y j)) →
    Submodule.span R (insert (D k R s) (Set.range fun j => D k R (y j))) = ⊤ := by
  intro k R _ _ _ _ _ _ _ s hs m y hy
  have hsurj : Function.Surjective (algebraMap R (ResidueField R)) := residue_surjective
  haveI := hy.isAlgebraic_field
  haveI : Algebra.IsSeparable (IntermediateField.adjoin k (Set.range fun j => residue R (y j)))
      (ResidueField R) := Algebra.IsAlgebraic.isSeparable_of_perfectField
  obtain ⟨b, hb⟩ := exists_basis_kaehler_of_algebraicIndependent hy.1
  have hmax : maximalIdeal R = Ideal.span {s} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer s).1 hs
  have hker : RingHom.ker (algebraMap R (ResidueField R)) = maximalIdeal R := ker_residue
  have hs0 : algebraMap R (ResidueField R) s = 0 := by
    rw [← RingHom.mem_ker, hker, hmax]; exact Ideal.mem_span_singleton_self s
  haveI : Module.Finite R Ω[R⁄k] := inferInstance
  set N := Submodule.span R (insert (D k R s) (Set.range fun j => D k R (y j))) with hN
  have hmb : ∀ x : R, mapBaseChange k R (ResidueField R) ((1 : ResidueField R) ⊗ₜ[R] D k R x) =
      D k (ResidueField R) (algebraMap R (ResidueField R) x) :=
    fun x => by rw [mapBaseChange_tmul, one_smul, map_D]
  have key : ∀ ω : Ω[R⁄k], ∃ n ∈ N, (1 : ResidueField R) ⊗ₜ[R] ω = (1 : ResidueField R) ⊗ₜ[R] n := by
    intro ω
    let c := b.repr (mapBaseChange k R (ResidueField R) ((1 : ResidueField R) ⊗ₜ[R] ω))
    let c' : Fin m → R := fun i => Function.surjInv hsurj (c i)
    have hc' : ∀ i, algebraMap R (ResidueField R) (c' i) = c i := fun i => Function.surjInv_eq hsurj _
    have h0 : mapBaseChange k R (ResidueField R)
        ((1 : ResidueField R) ⊗ₜ[R] (ω - ∑ i, c' i • D k R (y i))) = 0 := by

      rw [tmul_sub, map_sub, tmul_sum, map_sum, sub_eq_zero]
      conv_lhs => rw [← b.sum_repr (mapBaseChange k R (ResidueField R) ((1 : ResidueField R) ⊗ₜ[R] ω))]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hb, tmul_smul, ← algebraMap_smul (ResidueField R) (c' i), map_smul, hmb, hc']
      rfl
    obtain ⟨t, ht⟩ := (exact_kerCotangentToTensor_mapBaseChange k R (ResidueField R) hsurj _).mp h0
    obtain ⟨⟨a, ha⟩, rfl⟩ := Ideal.toCotangent_surjective _ t
    have ha' := ha
    rw [hker, hmax, Ideal.mem_span_singleton'] at ha'
    obtain ⟨r, rfl⟩ := ha'
    rw [kerCotangentToTensor_toCotangent] at ht
    have e1 : (1 : ResidueField R) ⊗ₜ[R] D k R (r * s) = (1 : ResidueField R) ⊗ₜ[R] (r • D k R s) := by
      rw [Derivation.leibniz, tmul_add, add_eq_left]
      have : (1 : ResidueField R) ⊗ₜ[R] (s • D k R r) = (algebraMap R (ResidueField R) s) • ((1 : ResidueField R) ⊗ₜ[R] D k R r) := by
        rw [algebraMap_smul, tmul_smul]
      rw [this, hs0, zero_smul]
    refine ⟨r • D k R s + ∑ i, c' i • D k R (y i), ?_, ?_⟩
    · exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _)))
        (Submodule.sum_mem _ fun i _ =>
          Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert_of_mem _ ⟨i, rfl⟩)))
    · have e2 : ω = (ω - ∑ i, c' i • D k R (y i)) + ∑ i, c' i • D k R (y i) := (sub_add_cancel _ _).symm
      rw [e2, tmul_add, ← ht, e1, ← tmul_add]
  rw [← IsLocalRing.map_tensorProduct_mk_eq_top, eq_top_iff]
  intro z _
  induction z using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | tmul c ω =>
    obtain ⟨c₀, rfl⟩ := hsurj c
    obtain ⟨n, hn, hω⟩ := key ω
    refine ⟨c₀ • n, N.smul_mem _ hn, ?_⟩
    rw [LinearMap.map_smul, TensorProduct.mk_apply, ← hω, ← algebraMap_smul (ResidueField R) c₀,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  | add x z hx hz => exact add_mem (hx trivial) (hz trivial)

end GlobalTheory
end
end

section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory

theorem integralClosure_finiteType_of_charZero :
    ∀ (k F K : Type) [Field k] [CharZero k] [Field F] [Field K] [Algebra k F] [Algebra k K]
      [Algebra F K] [IsScalarTower k F K] [FiniteDimensional F K] (d : ℕ) (u : Fin d → F),
      AlgebraicIndependent k u → ∀ (A : Subalgebra k F) [IsFractionRing A F],
      A = Algebra.adjoin k (Set.range u) → ∀ (B : Subalgebra k K),
      B = (integralClosure A K).restrictScalars k → Algebra.FiniteType k B := by
  intro k F K _ _ _ _ _ _ _ _ _ d u hu A _ hA B hB
  subst hB

  have e : MvPolynomial (Fin d) k ≃ₐ[k] A := by
    subst hA; exact hu.aevalEquiv
  have hAft : Algebra.FiniteType k A := Algebra.FiniteType.equiv inferInstance e
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have : IsIntegrallyClosed A := IsIntegrallyClosed.of_equiv e.toRingEquiv
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap k F).injective
  have : Algebra.IsSeparable F K := inferInstance
  set_option synthInstance.maxHeartbeats 200000 in
  have : Module.Finite A (integralClosure A K) := IsIntegralClosure.finite A F K (integralClosure A K)
  have : Algebra.FiniteType A (integralClosure A K) := inferInstance
  have : Algebra.FiniteType k (integralClosure A K) := Algebra.FiniteType.trans hAft this
  exact this

end GlobalTheory
end

section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.exists_valuation_bound_of_isIntegral_mem_adjoin : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (N : Matrix (Fin n) (Fin n) (w.adicCompletion E)), N.charpoly.Separable → ∃ c : WithZero (Multiplicative ℤ), ∀ g ∈ Algebra.adjoin (w.adicCompletion E) {N}, IsIntegral (w.adicCompletionIntegers E) g → ∀ i j, Valued.v (g i j) ≤ c := by
  first | exact @GlobalTheory.LocBounded.bounded_of_isIntegral | exact GlobalTheory.LocBounded.bounded_of_isIntegral | (intros; apply GlobalTheory.LocBounded.bounded_of_isIntegral <;> assumption)
end

section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.isCompact_GL_bounded_entries_completion_finitePlace : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (c : WithZero (Multiplicative ℤ)), IsCompact {g : GL (Fin n) (w.adicCompletion E) | ∀ i j, Valued.v ((g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ c ∧ Valued.v (((g⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ c} := by
  first | exact @GlobalTheory.BoundedGL.isCompact_bounded | exact GlobalTheory.BoundedGL.isCompact_bounded | (intros; apply GlobalTheory.BoundedGL.isCompact_bounded <;> assumption)
end

section


theorem _root_.GlobalTheory.T.away_quotient_span_eq_localization : ∀ (B D : Type) [CommRing B] [IsDedekindDomain B] [CommRing D] [Algebra B D] [Algebra.Etale B D] (f : B), f ≠ 0 → ∀ (P : Ideal B), P.IsMaximal → f ∈ P → ∀ (Q : Ideal D), Q.IsPrime → Q.comap (algebraMap B D) = P → (∀ d : D, ∃ b : B, d - algebraMap B D b ∈ Q) → ∃ g : D, (∀ a : Localization.Away g, ∃ b : B, a - algebraMap B (Localization.Away g) b ∈ Ideal.span {algebraMap B (Localization.Away g) f}) ∧ ∀ b : B, algebraMap B (Localization.Away g) b ∈ Ideal.span {algebraMap B (Localization.Away g) f} ↔ ∃ s : B, s ∉ P ∧ s * b ∈ Ideal.span {f} := by
  first | (exact @GlobalTheory.etale_away_quotient_eq_localization) | (exact GlobalTheory.etale_away_quotient_eq_localization) | (intros; apply GlobalTheory.etale_away_quotient_eq_localization  <;> assumption)
end

section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.exists_continuous_finiteAdele_equiv_rat_int : ∃ e : FiniteAdeleRing (𝓞 ℚ) ℚ ≃ₐ[ℚ] FiniteAdeleRing ℤ ℚ, Continuous e := by
  first | (exact @GlobalTheory.AdeleZ.exists_continuous_adele_equiv) | (exact GlobalTheory.AdeleZ.exists_continuous_adele_equiv) | (intros; apply GlobalTheory.AdeleZ.exists_continuous_adele_equiv <;> assumption)
end

section

open IsLocalRing Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.isDomain_tensor_atPrime_of_isLocalRing_of_etale : ∀ (P R E : Type) [CommRing P] [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Algebra P R] [CommRing E] [Algebra P E] [Algebra.Etale P E] (Q : Ideal E) [Q.IsPrime],
    IsLocalRing (TensorProduct P R (Localization.AtPrime Q)) → IsDomain (TensorProduct P R (Localization.AtPrime Q)) := by
  first | (exact @GlobalTheory.tensor_localization_atPrime_isDomain_of_isLocalRing_etale) | (exact GlobalTheory.tensor_localization_atPrime_isDomain_of_isLocalRing_etale) | (intros; apply GlobalTheory.tensor_localization_atPrime_isDomain_of_isLocalRing_etale <;> assumption)
end
