module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ConjStableShaFam
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Bundle002
public import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
public import Mathlib.Topology.Algebra.Module.Basic
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
public import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Valuation.LocalSubring
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
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import ReciprocityTheory.GroupCohomology.Bundle009
public import ReciprocityTheory.GroupCohomology.Bundle006
public import ReciprocityTheory.GroupCohomology.Bundle004
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.GaloisCohomology.Statement
public import ReciprocityTheory.GroupCohomology.Bundle002

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

theorem UpperTheory.V.Base.galEmbFam :
    ∀ (k E Ω : Type) [Field k] [NumberField k] [Field E] [NumberField E] [Field Ω] [Algebra k E] [Algebra k Ω] [Algebra E Ω]
      [IsScalarTower k E Ω] [IsAlgClosure k Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime],
      (∀ A : ValuationSubring Ω, (Dec (F := k) A).comap (galEmb k E Ω) = Dec (F := E) A ∧ (Ine (F := k) A).comap (galEmb k E Ω) = Ine (F := E) A) ∧
      Subgroup.comap (galEmb k E Ω) '' shaFam k Ω l = shaFam E Ω l ∧ (cycZ k Ω l).comp (galEmb k E Ω) = cycZ E Ω l ∧
      ∀ e : ℤ, (LDataCardLeFinrank.qzG k Ω l e).comp (galEmb k E Ω) = LDataCardLeFinrank.qzG E Ω l e := by
  intro k E Ω _ _ _ _ _ _ _ _ _ _ _ l _
  have hD : ∀ A : ValuationSubring Ω, (Dec (F := k) A).comap (galEmb k E Ω) = Dec (F := E) A := fun A => by
    ext σ
    rw [Subgroup.mem_comap, mem_Dec, mem_Dec]
    exact Iff.rfl
  have hI : ∀ A : ValuationSubring Ω, (Ine (F := k) A).comap (galEmb k E Ω) = Ine (F := E) A := fun A => by
    ext σ
    rw [Subgroup.mem_comap]
    exact and_congr (SetLike.ext_iff.1 (hD A) σ) Iff.rfl
  refine ⟨fun A => ⟨hD A, hI A⟩, ?_, ?_, fun e => ?_⟩
  · ext D
    constructor
    · rintro ⟨D', ⟨A, hl, rfl⟩ | ⟨A, rfl⟩, rfl⟩
      · exact Or.inl ⟨A, hl, hD A⟩
      · exact Or.inr ⟨A, hI A⟩
    · rintro (⟨A, hl, rfl⟩ | ⟨A, rfl⟩)
      · exact ⟨_, Or.inl ⟨A, hl, rfl⟩, hD A⟩
      · exact ⟨_, Or.inr ⟨A, rfl⟩, hI A⟩
  · exact MonoidHom.ext fun _ => rfl
  · exact MonoidHom.ext fun _ => rfl
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

section Alg

variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]

private theorem algebraMap_inj : Function.Injective (algebraMap ℤ_[l] O) := by
  rw [RingHom.injective_iff_ker_eq_bot]
  by_contra hne
  have hp : (RingHom.ker (algebraMap ℤ_[l] O)).IsPrime := RingHom.ker_isPrime _
  have hmax : (RingHom.ker (algebraMap ℤ_[l] O)).IsMaximal := hp.isMaximal hne
  have hbot : (⊥ : Ideal O).IsMaximal := by
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := ℤ_[l])
    rw [Ideal.under_def, ← RingHom.ker_eq_comap_bot]
    exact hmax
  exact IsDiscreteValuationRing.not_a_field O (IsLocalRing.eq_maximalIdeal hbot).symm

private theorem length_quot [Module.Free ℤ_[l] O] : Module.length ℤ_[l] (O ⧸ Ideal.span {(l : O)}) = Module.finrank ℤ_[l] O := by
  have hspan : Ideal.span {(l : O)} = (IsLocalRing.maximalIdeal ℤ_[l]).map (algebraMap ℤ_[l] O) := by
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton, map_natCast]
  rw [hspan, ← IsLocalRing.finrank_quotient_map (R := ℤ_[l]) (S := O)]
  letI : Field (ℤ_[l] ⧸ IsLocalRing.maximalIdeal ℤ_[l]) := Ideal.Quotient.field _
  haveI : Module.Finite (ℤ_[l] ⧸ IsLocalRing.maximalIdeal ℤ_[l])
      (O ⧸ (IsLocalRing.maximalIdeal ℤ_[l]).map (algebraMap ℤ_[l] O)) :=
    Module.Finite.of_restrictScalars_finite ℤ_[l] _ _
  rw [← Module.length_eq_finrank]
  exact Module.length_eq_of_surjective Ideal.Quotient.mk_surjective

end Alg

theorem UpperTheory.V.Base.dvrFacts :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O],
      Function.Injective (algebraMap ℤ_[l] O) ∧ Module.Free ℤ_[l] O ∧ IsLocalHom (algebraMap ℤ_[l] O) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal O) O ∧
      eO l O = Module.length O (O ⧸ (IsLocalRing.maximalIdeal ℤ_[l]).map (algebraMap ℤ_[l] O)) ∧ eO l O ≠ 0 ∧
      eO l O ≤ (Module.finrank ℤ_[l] O : ℕ∞) ∧ eO l O = IsDiscreteValuationRing.addVal O (l : O) ∧
      ∀ n : ℕ, ¬ l ∣ n → IsUnit (n : O) := by
  intro l _ O _ _ _ _ _
  have hinj : Function.Injective (algebraMap ℤ_[l] O) := algebraMap_inj O
  haveI : CharZero O := charZero_of_injective_algebraMap hinj
  obtain ⟨hcomp, -, hlm, -, hfree, hloc⟩ := UpperTheory.V.abelian₂.dvr_finite l O
  haveI := hfree
  haveI := hloc
  have hspan : Ideal.span {(l : O)} =
      (IsLocalRing.maximalIdeal ℤ_[l]).map (algebraMap ℤ_[l] O) := by
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton, map_natCast]
  have hl0 : (l : O) ≠ 0 := by
    intro h
    have h' : algebraMap ℤ_[l] O (l : ℤ_[l]) = algebraMap ℤ_[l] O 0 := by
      rw [map_natCast, h, map_zero]
    have h'' : ((l : ℕ) : ℤ_[l]) = 0 := hinj h'
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast h'')
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ
  have hval : IsDiscreteValuationRing.addVal O (l : O) = n :=
    IsDiscreteValuationRing.addVal_def _ u hϖ n hu
  have he : eO l O = n := by
    show Module.length O (O ⧸ Ideal.span {(l : O)}) = n
    rw [hu, Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow,
      ← hϖ.maximalIdeal_eq]
    exact IsDiscreteValuationRing.length_quotient_pow_maximalIdeal (R := O) n
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero, mul_one] at hu
    exact (IsLocalRing.mem_maximalIdeal _).1 hlm (hu ▸ u.isUnit)
  refine ⟨hinj, hfree, hloc, hcomp, ?_, ?_, ?_, ?_, ?_⟩
  · show Module.length O (O ⧸ Ideal.span {(l : O)}) = _
    rw [hspan]
  · rw [he]
    exact_mod_cast hn0
  · rw [← length_quot (l := l) O]
    show Module.length O (O ⧸ Ideal.span {(l : O)}) ≤ _
    rw [IsLocalRing.length_restrictScalars ℤ_[l] O (O ⧸ Ideal.span {(l : O)})]
    exact le_mul_of_one_le_right' (Order.one_le_iff_pos.2 Module.length_pos)
  · rw [he, hval]
  · intro m hm
    have hcop : IsCoprime (l : ℤ) (m : ℤ) :=
      Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hm)
    obtain ⟨a, b, hab⟩ := hcop
    by_contra hmu
    have hmm : (m : O) ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 hmu
    have h1 : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
      have hab' : (a : O) * (l : O) + (b : O) * (m : O) = 1 := by
        exact_mod_cast congrArg (Int.cast : ℤ → O) hab
      rw [← hab']
      exact add_mem (Ideal.mul_mem_left _ _ hlm) (Ideal.mul_mem_left _ _ hmm)
    exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h1)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

private theorem mem_of_int {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {y : Ω} (hy : IsIntegral ℤ y) : y ∈ A := by
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral (R := A) (K := Ω) (hy.tower_top (A := A))
  exact hz ▸ z.2

open Polynomial in
private theorem key {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (f : ℤ[X]) {a b : Ω} (ha : a ∈ A) (hb : b ∈ A)
    (fa : aeval a f = 0) (fb : aeval b f = 0) (hab : A.valuation (b - a) < 1)
    (hd : ¬ A.valuation (aeval a (derivative f)) < 1) : b = a := by
  by_contra hne
  apply hd
  obtain ⟨c, hc⟩ := (f.map (algebraMap ℤ A)).binomExpansion ⟨a, ha⟩ (⟨b, hb⟩ - ⟨a, ha⟩)
  have e : ∀ (g : ℤ[X]) (x : A), ((eval x (g.map (algebraMap ℤ A)) : A) : Ω) = aeval (x : Ω) g := fun g x => by
    rw [eval_map_algebraMap]
    exact (aeval_algHom_apply (A.subtype.toIntAlgHom) x g).symm
  rw [add_sub_cancel, derivative_map] at hc
  have h2 := congrArg (fun x : A => (x : Ω)) hc
  push_cast at h2
  simp only [e, fa, fb] at h2
  have h3 : aeval a (derivative f) = -(c : Ω) * (b - a) := by
    apply mul_right_cancel₀ (sub_ne_zero.2 hne)
    linear_combination -h2
  rw [h3, map_mul, Valuation.map_neg]
  exact lt_of_le_of_lt (mul_le_of_le_one_left' (A.valuation_le_one c)) hab

open Polynomial in
private theorem fix_int {k E' Ω : Type} [Field k] [NumberField k] [Field E'] [NumberField E'] [Field Ω] [Algebra k Ω]
    [Algebra E' Ω] (α : 𝓞 E') : ∃ d : ℤ, d ≠ 0 ∧ ∀ A : ValuationSubring Ω, ¬ A.valuation (d : Ω) < 1 →
      ∀ σ ∈ Ine (F := k) A, σ (algebraMap E' Ω α) = algebraMap E' Ω α := by
  have hi : IsIntegral ℤ α := Algebra.IsIntegral.isIntegral α
  have hne : aeval α (derivative (minpoly ℤ α)) ≠ 0 := by
    intro h
    have h1 := minpoly.isIntegrallyClosed_dvd hi h
    have h2 := minpoly.natDegree_pos hi
    have h3 : derivative (minpoly ℤ α) ≠ 0 := fun h0 => by
      have := natDegree_eq_zero_of_derivative_eq_zero h0
      omega
    have h4 := natDegree_le_of_dvd h1 h3
    have h5 := natDegree_derivative_lt (p := minpoly ℤ α) (by omega)
    omega
  set δ := aeval α (derivative (minpoly ℤ α)) with hδ
  have hm : (Algebra.norm ℤ δ : 𝓞 E') ∈ Ideal.span {δ} := by
    have := Ideal.absNorm_mem (Ideal.span {δ})
    rw [Ideal.absNorm_span_singleton] at this
    rcases Int.natAbs_eq (Algebra.norm ℤ δ) with h | h
    · rw [h]; simpa using this
    · rw [h]; simpa using this
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hm
  refine ⟨Algebra.norm ℤ δ, Algebra.norm_ne_zero_iff.2 hne, fun A hA σ hσ => ?_⟩
  let φ : 𝓞 E' →ₐ[ℤ] Ω := ((algebraMap E' Ω).comp (algebraMap (𝓞 E') E')).toIntAlgHom
  have hφ : ∀ x, φ x ∈ A := fun x => mem_of_int A ((Algebra.IsIntegral.isIntegral x).map φ)
  let ψ : Ω →ₐ[ℤ] Ω := σ.toRingEquiv.toRingHom.toIntAlgHom
  have fa : aeval (φ α) (minpoly ℤ α) = 0 := by rw [aeval_algHom_apply, minpoly.aeval, map_zero]
  change ψ (φ α) = φ α
  refine key A (minpoly ℤ α) (hφ α) (mem_of_int A ((hi.map φ).map ψ)) fa
    (by rw [aeval_algHom_apply, fa, map_zero]) (hσ.2 _ ((A.valuation_le_one_iff _).2 (hφ α))) fun h => hA ?_
  rw [aeval_algHom_apply, ← hδ] at h
  have e : ((Algebra.norm ℤ δ : ℤ) : Ω) = φ t * φ δ := by rw [← map_mul, ht, map_intCast]
  rw [e, map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_left' ((A.valuation_le_one_iff _).2 (hφ t))) h

open Polynomial in
private theorem fix_root {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] {N : ℕ} (hN : N ≠ 0)
    (A : ValuationSubring Ω) (hA : ¬ A.valuation (N : Ω) < 1) {σ : G k Ω} (hσ : σ ∈ Ine (F := k) A) {z : Ω}
    (hz : z ^ N = 1) : σ z = z := by
  have hm : ∀ {y : Ω}, y ^ N = 1 → y ∈ A := fun {y} hy =>
    mem_of_int A (IsIntegral.of_pow (Nat.pos_of_ne_zero hN) (hy ▸ isIntegral_one))
  have hz' : (σ z) ^ N = 1 := by rw [← map_pow, hz, map_one]
  refine key A (X ^ N - 1) (hm hz) (hm hz') (by simp [hz]) (by simp [hz'])
    (hσ.2 _ ((A.valuation_le_one_iff _).2 (hm hz))) fun h => hA ?_
  have e : (N : Ω) = z * aeval z (derivative (X ^ N - 1 : ℤ[X])) := by
    simp only [derivative_sub, derivative_X_pow, derivative_one, sub_zero, map_mul, map_natCast, map_pow, aeval_X]
    rw [mul_left_comm, ← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hN), hz, mul_one]
  rw [e, map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_left' ((A.valuation_le_one_iff _).2 (hm hz))) h

theorem UpperTheory.V.Base.ramFinite :
    ∀ (k E E' Ω : Type) [Field k] [NumberField k] [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω]
      [Algebra k Ω] [Algebra E E'] [Algebra E Ω] [Algebra E' Ω] [Algebra k E] [IsScalarTower k E Ω] [IsScalarTower E E' Ω]
      [IsAlgClosure k Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω],
      (∃ T : Finset (HeightOneSpectrum (𝓞 E)), ∀ v, v ∉ T → ∀ A : ValuationSubring Ω, IsPlaceOver A v →
        galOf k E Ω ⊓ Ine (F := k) A ≤ galOf k E' Ω) ∧
      ∀ (N : ℕ) [NeZero N] [IsCyclotomicExtension {N} E E'] (A : ValuationSubring Ω), ¬ A.valuation (N : Ω) < 1 →
        galOf k E Ω ⊓ Ine (F := k) A ≤ galOf k E' Ω := by
  intro k E E' Ω _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
  refine ⟨?_, fun N _ hc A hA σ hσ x => ?_⟩
  · choose d hd0 hd using fun α : 𝓞 E' => fix_int (k := k) (Ω := Ω) α
    have hfin : ∀ i, {v : HeightOneSpectrum (𝓞 E) |
        v.asIdeal ∣ Ideal.span {((d (RingOfIntegers.basis E' i) : ℤ) : 𝓞 E)}}.Finite := fun i =>
      Ideal.finite_factors (by simpa using hd0 _)
    refine ⟨(Set.finite_iUnion hfin).toFinset, fun v hv A hA σ hσ x => ?_⟩
    simp only [Set.Finite.mem_toFinset, Set.mem_iUnion, Set.mem_setOf_eq, not_exists, Ideal.dvd_span_singleton] at hv
    have h : (σ.toRingEquiv.toRingHom.comp (algebraMap E' Ω)).toRatAlgHom.toLinearMap =
        (algebraMap E' Ω).toRatAlgHom.toLinearMap := (integralBasis E').ext fun i => by
      rw [integralBasis_apply]
      refine hd _ A (fun h => hv i ((hA _).1 ?_)) σ hσ.2
      simpa using h
    exact LinearMap.congr_fun h x
  · have hx := hc.adjoin_roots x
    induction hx using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨n, hn, h0, hy⟩ := hy
      obtain rfl : n = N := hn
      exact fix_root h0 A hA hσ.2 (by rw [← map_pow, hy, map_one])
    | algebraMap r => rw [← IsScalarTower.algebraMap_apply]; exact hσ.1 r
    | add a b _ _ ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
    | mul a b _ _ ha hb => rw [map_mul, map_mul, ha, hb]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

namespace UpperTheory.V.Base

open ReciprocityTheory.Coh

section

variable {R Γ M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [AddCommGroup M]
  [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]

private theorem transg_cont (σ : Representation R Γ M) (hσ : ContAction σ) (N : Subgroup Γ) [N.Normal] :
    ContAction (σ.quotientToInvariants N) := by
  unfold ReciprocityTheory.Gal.ContAction
  have hq := (QuotientGroup.isOpenQuotientMap_mk (N := N)).prodMap
    (IsOpenQuotientMap.id (X := Representation.invariants (σ.comp N.subtype)))
  rw [← hq.continuous_comp_iff]
  refine continuous_induced_rng.2 ?_
  exact hσ.comp (f := fun p : Γ × Representation.invariants (σ.comp N.subtype) => (p.1, (p.2 : M)))
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

private theorem transg_top [DiscreteTopology M] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ]
    (σ : Representation R Γ M) (hσ : ContAction σ) (N : Subgroup Γ) [N.Normal] (hN : IsClosed (N : Set Γ)) :
    ∃ tg : (conjRep σ N).invariants →ₗ[R] H2 (σ.quotientToInvariants N),
      ∀ x, tg x = 0 ↔ x.1 ∈ LinearMap.range (resH1 σ N.subtype continuous_subtype_val) := by
  let A : TRep R Γ := { V := M, rho := σ, cont := hσ }
  let Q : TRep R (Γ ⧸ N) :=
    { V := Representation.invariants (σ.comp N.subtype), rho := σ.quotientToInvariants N, cont := transg_cont σ hσ N }
  let P : Pair Q A := ⟨QuotientGroup.mk' N, Submodule.subtype _, QuotientGroup.continuous_mk,
    continuous_subtype_val, fun _ _ => rfl⟩
  have hP : IsInvRep A N Q P := by
    refine ⟨rfl, Topology.IsEmbedding.subtypeVal, fun m => ?_⟩
    show m ∈ LinearMap.range (Submodule.subtype _) ↔ _
    rw [Submodule.range_subtype]
    exact ⟨fun h g hg => h ⟨g, hg⟩, fun h g => h g.1 g.2⟩
  obtain ⟨a₀, a₁, a₂, ha⟩ := exists_isLow A
  obtain ⟨n₀, n₁, n₂, hn⟩ := exists_isLow (A.resSub N)
  obtain ⟨q₀, q₁, q₂, hq⟩ := exists_isLow Q
  haveI : DiscreteTopology A.V := ‹DiscreteTopology M›
  let I : Submodule R ((A.resSub N).H 1) := (conjRep σ N).invariants.comap n₁.toLinearMap
  obtain ⟨tg, htg, -⟩ := fiveTerm_holds R Γ A N hN Q P hP I (by
    intro x
    constructor
    · intro hx s c h1 h2
      apply n₁.injective
      rw [(lowNat_holds R N N _ _ c _ _ _ _ _ _ hn hn).2.1]
      obtain ⟨φ, u, hφ, hu, he⟩ := c
      obtain rfl : φ = conjHom N s := MonoidHom.ext fun g => Subtype.ext (h1 g)
      obtain rfl : u = σ s := LinearMap.ext h2
      exact hx s
    · intro hx s
      let c : Pair (A.resSub N) (A.resSub N) := ⟨conjHom N s, σ s, continuous_conjHom N s,
        continuous_of_discreteTopology (α := M), fun u (m : M) => by
          show σ s (σ (s⁻¹ * u * s) m) = σ u (σ s m)
          rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
          simp [mul_assoc]⟩
      have e := congrArg n₁ (hx s c (fun _ => rfl) fun _ => rfl)
      rw [(lowNat_holds R N N _ _ c _ _ _ _ _ _ hn hn).2.1] at e
      exact e)
  let k : (conjRep σ N).invariants →ₗ[R] I :=
    { toFun := fun x => ⟨n₁.symm x.1, fun s => by
        have e := n₁.apply_symm_apply x.1
        exact (congrArg (conjRep σ N s) e).trans ((x.2 s).trans e.symm)⟩
      map_add' := fun x y => Subtype.ext (n₁.symm.map_add x.1 y.1)
      map_smul' := fun r x => Subtype.ext (n₁.symm.map_smul r x.1) }
  refine ⟨q₂.toLinearMap.comp (tg.comp k), fun x => ?_⟩
  have hr := (lowNat_holds R Γ N _ _ (Pair.res A N.subtype continuous_subtype_val) _ _ _ _ _ _ ha hn).2.1
  refine (q₂.map_eq_zero_iff.trans (htg (k x))).trans ⟨?_, ?_⟩
  · rintro ⟨y, hy⟩
    refine ⟨a₁ y, ?_⟩
    have e := congrArg n₁ hy
    rw [hr] at e
    exact e.trans (n₁.apply_symm_apply x.1)
  · rintro ⟨y, hy⟩
    refine ⟨a₁.symm y, n₁.injective ?_⟩
    rw [hr, LinearEquiv.apply_symm_apply]
    exact hy.trans (n₁.apply_symm_apply x.1).symm

end

end UpperTheory.V.Base

theorem UpperTheory.V.Base.transg :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
      [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M) [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G], ContAction ρ → ∀ (U' U : Subgroup G) [U'.Normal] (h : U' ≤ U), IsClosed (U : Set G) → IsClosed (U' : Set G) →
      ∃ tg : resCoker ρ h →ₗ[R] H2 (quotRep ρ U U'), Function.Injective tg := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ _ _ _ hρ U' U _ h hU hU'
  haveI : CompactSpace U := isCompact_iff_compactSpace.1 hU.isCompact
  let σ : Representation R U M := ρ.comp U.subtype
  have hσ : ContAction σ := hρ.comp (f := fun p : U × M => ((p.1 : G), p.2))
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  obtain ⟨tg, htg⟩ := transg_top σ hσ (U'.subgroupOf U) (hU'.preimage continuous_subtype_val)
  let j : H1U ρ U' →ₗ[R] H1U σ (U'.subgroupOf U) :=
    pairH1DecompositionMap _ _ (Subgroup.subgroupOfEquivOfLe h).toMonoidHom
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _) LinearMap.id continuous_id fun _ _ => rfl
  let j' : H1U σ (U'.subgroupOf U) →ₗ[R] H1U ρ U' :=
    pairH1DecompositionMap _ _ (Subgroup.subgroupOfEquivOfLe h).symm.toMonoidHom
      ((continuous_subtype_val.subtype_mk _).subtype_mk _) LinearMap.id continuous_id fun _ _ => rfl
  have h1 : ∀ x, j' (j x) = x := fun x => by
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl
  have h2 : ∀ y, j (resU ρ h y) = resH1 σ (U'.subgroupOf U).subtype continuous_subtype_val y := fun x => by
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl
  have h3 : ∀ (g : U) x, conjRep σ (U'.subgroupOf U) g (j x) = j (conjRep ρ U' g x) := fun g x => by
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl
  let k : invariantsUnderSubgroupH1 ρ U U' →ₗ[R] (conjRep σ (U'.subgroupOf U)).invariants :=
    (j.comp (Submodule.subtype _)).codRestrict _ fun x g => (h3 g x.1).trans (congrArg j (x.2 g))
  have hk : ∀ x : invariantsUnderSubgroupH1 ρ U U', tg (k x) = 0 ↔ x.1 ∈ LinearMap.range (resU ρ h) := fun x => by
    refine (htg (k x)).trans ⟨?_, ?_⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, by rw [← h1 (resU ρ h y), h2, hy]; exact h1 x.1⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, (h2 y).symm.trans (congrArg j hy)⟩
  refine ⟨Submodule.liftQ _ (tg.comp k) fun x hx => (hk x).2 hx, ?_⟩
  rw [← LinearMap.ker_eq_bot]
  exact Submodule.ker_liftQ_eq_bot _ _ _ fun x hx => (hk x).1 hx
end
