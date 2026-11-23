module

public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
public import Mathlib.RingTheory.Trace.Quotient
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.NumberTheory.NumberField.Norm
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.LocalRing.Module

@[expose] public section

section

open NumberField NumberField.ComplexEmbedding

namespace GlobalTheory.CMFieldCriterion

theorem isTotallyReal_fixedField (K : Type) [Field K] [NumberField K] {σ : Gal(K/ℚ)}
    (hσ : ∀ φ : K →+* ℂ, IsConj φ σ) :
    IsTotallyReal (IntermediateField.fixedField (Subgroup.zpowers σ)) := by
  refine ⟨fun w => ?_⟩
  obtain ⟨W, rfl⟩ := w.comap_surjective (K := K)
  dsimp only
  rw [← InfinitePlace.mk_embedding W, InfinitePlace.comap_mk, InfinitePlace.isReal_mk_iff,
    ComplexEmbedding.isReal_iff]
  ext x
  have hx : σ (x : K) = x :=
    (IntermediateField.mem_fixedField_iff _ _).mp x.2 σ (Subgroup.mem_zpowers σ)
  have h := (hσ W.embedding).eq (x : K)
  rw [hx] at h
  rw [conjugate_coe_eq]
  exact h.symm

theorem isCMField_of_forall_isConj (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K]
    {σ : Gal(K/ℚ)} (hσ : ∀ φ : K →+* ℂ, IsConj φ σ) : IsCMField K := by
  obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have hne : σ ≠ 1 :=
    (isConj_ne_one_iff (hσ φ)).mpr (IsTotallyComplex.complexEmbedding_not_isReal φ)
  have hcard : Nat.card (Subgroup.zpowers σ) = 2 := by
    rw [Nat.card_zpowers]
    refine orderOf_eq_prime ?_ hne
    ext x
    rw [pow_two, AlgEquiv.mul_apply, AlgEquiv.one_apply]
    exact isConj_apply_apply (hσ φ) x
  have hreal := isTotallyReal_fixedField K hσ
  have hquad :
      Algebra.IsQuadraticExtension (IntermediateField.fixedField (Subgroup.zpowers σ)) K :=
    { finrank_eq_two' := by rw [IntermediateField.finrank_fixedField_eq_card, hcard] }
  exact IsCMField.ofCMExtension (IntermediateField.fixedField (Subgroup.zpowers σ)) K

end GlobalTheory.CMFieldCriterion
end

section

open NumberField

namespace GlobalTheory

theorem cm_eq_or_conj_of_comp_eq (E : Type) [Field E] [NumberField E] [IsCMField E]
    (τ τ' : E →+* ℂ)
    (h : τ'.comp (algebraMap (maximalRealSubfield E) E) =
      τ.comp (algebraMap (maximalRealSubfield E) E)) :
    τ' = τ ∨ τ' = ComplexEmbedding.conjugate τ := by
  have h1 : InfinitePlace.mk τ = InfinitePlace.mk τ' := by
    apply (IsCMField.equivInfinitePlace E).injective
    rw [IsCMField.equivInfinitePlace_apply, IsCMField.equivInfinitePlace_apply,
      InfinitePlace.comap_mk, InfinitePlace.comap_mk, h]
  rcases InfinitePlace.mk_eq_iff.1 h1 with h2 | h2
  · exact Or.inl h2.symm
  · exact Or.inr h2.symm

theorem cm_conj_comp_eq (E : Type) [Field E] [NumberField E] (τ : E →+* ℂ) :
    (ComplexEmbedding.conjugate τ).comp (algebraMap (maximalRealSubfield E) E) =
      τ.comp (algebraMap (maximalRealSubfield E) E) := by
  have h := IsTotallyReal.complexEmbedding_isReal (τ.comp (algebraMap (maximalRealSubfield E) E))
  rw [ComplexEmbedding.isReal_iff] at h
  exact h

theorem cm_prod_regroup_maximalReal (E : Type) [Field E] [NumberField E] [IsCMField E]
    (k : (E →+* ℂ) → ℤ) (hk : ∀ τ, k (ComplexEmbedding.conjugate τ) = k τ) :
    ∃ n : (maximalRealSubfield E →+* ℂ) → ℤ, ∀ g : (maximalRealSubfield E →+* ℂ) → ℂ,
      ∏ τ : E →+* ℂ, g (τ.comp (algebraMap (maximalRealSubfield E) E)) ^ k τ =
        ∏ φ, g φ ^ (2 * n φ) := by
  classical
  refine ⟨fun φ => k (ComplexEmbedding.lift E φ), fun g => ?_⟩
  rw [← Finset.prod_fiberwise Finset.univ
    (fun τ : E →+* ℂ => τ.comp (algebraMap (maximalRealSubfield E) E))]
  refine Finset.prod_congr rfl fun φ _ => ?_
  set τ₀ := ComplexEmbedding.lift E φ with hτ₀
  have h0 : τ₀.comp (algebraMap (maximalRealSubfield E) E) = φ :=
    ComplexEmbedding.lift_comp_algebraMap E φ
  have h1 : (ComplexEmbedding.conjugate τ₀).comp (algebraMap (maximalRealSubfield E) E) = φ := by
    rw [cm_conj_comp_eq, h0]
  have hne : τ₀ ≠ ComplexEmbedding.conjugate τ₀ := fun h =>
    IsTotallyComplex.complexEmbedding_not_isReal τ₀ (ComplexEmbedding.isReal_iff.2 h.symm)
  have hfib : Finset.univ.filter
      (fun τ : E →+* ℂ => τ.comp (algebraMap (maximalRealSubfield E) E) = φ) =
      {τ₀, ComplexEmbedding.conjugate τ₀} := by
    ext τ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro h
      exact cm_eq_or_conj_of_comp_eq E τ₀ τ (h.trans h0.symm)
    · rintro (rfl | rfl)
      · exact h0
      · exact h1
  rw [hfib, Finset.prod_pair hne, h0, h1, hk, mul_comm (2 : ℤ), zpow_mul, zpow_two]

end GlobalTheory
end

section

open NumberField IsDedekindDomain

namespace GlobalTheory

theorem abs_norm_eq_prod_embeddings_closeOne {E : Type} [Field E] [NumberField E] (x : E) :
    |((Algebra.norm ℚ x : ℚ) : ℝ)| = ∏ σ : E →+* ℂ, ‖σ x‖ := by
  have h : ((Algebra.norm ℚ x : ℚ) : ℂ) = ∏ σ : E →+* ℂ, σ x := by
    rw [Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ) (fun f => f x) (fun φ => φ x)
      (fun _ => rfl), ← Algebra.norm_eq_prod_embeddings ℚ ℂ x]
    simp
  rw [← norm_prod, ← h, Complex.norm_ratCast]

theorem eq_one_of_norm_one_of_valuation_sub_one_le (E : Type) [Field E] [NumberField E] (ε : E)
    (w : HeightOneSpectrum (𝓞 E)) (K : ℕ) (hK : Module.finrank ℚ E < K)
    (hint : ∀ v : HeightOneSpectrum (𝓞 E), v.valuation E ε ≤ 1)
    (habs : ∀ φ : E →+* ℂ, ‖φ ε‖ = 1)
    (hw : w.valuation E (ε - 1) ≤ WithZero.exp (-(K : ℤ))) : ε = 1 := by
  obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one E ε hint
  by_contra hne
  have hxE : algebraMap (𝓞 E) E (r - 1) = ε - 1 := by simp [hr]
  have hx0 : r - 1 ≠ 0 := by
    intro h
    rw [h, map_zero] at hxE
    exact hne (sub_eq_zero.mp hxE.symm)
  have hmem : r - 1 ∈ w.asIdeal ^ K := by
    rw [← HeightOneSpectrum.intValuation_le_pow_iff_mem, ← HeightOneSpectrum.valuation_of_algebraMap (K := E)]
    convert hw using 2
  have hdvd : w.asIdeal ^ K ∣ Ideal.span {r - 1} := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact hmem
  have hN := map_dvd Ideal.absNorm hdvd
  rw [map_pow, Ideal.absNorm_span_singleton] at hN
  have hnz : (Algebra.norm ℤ (r - 1)).natAbs ≠ 0 := by
    rw [← Ideal.absNorm_span_singleton, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hx0
  have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hnz) hN
  have h2 : 2 ≤ Ideal.absNorm w.asIdeal := by
    have h0 : Ideal.absNorm w.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact w.ne_bot
    have h1 : Ideal.absNorm w.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]; exact w.isPrime.ne_top
    omega
  have hlow : 2 ^ K ≤ (Algebra.norm ℤ (r - 1)).natAbs :=
    le_trans (Nat.pow_le_pow_left h2 K) hle
  have hup : ((Algebra.norm ℤ (r - 1)).natAbs : ℝ) ≤ 2 ^ Module.finrank ℚ E := by
    have h1 : ((Algebra.norm ℤ (r - 1)).natAbs : ℝ) = |((Algebra.norm ℚ (ε - 1) : ℚ) : ℝ)| := by
      rw [← hxE, ← Algebra.coe_norm_int (r - 1), Nat.cast_natAbs]
      push_cast
      rfl
    rw [h1, abs_norm_eq_prod_embeddings_closeOne]
    calc ∏ φ : E →+* ℂ, ‖φ (ε - 1)‖ ≤ ∏ _φ : E →+* ℂ, (2 : ℝ) := by
          refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun φ _ => ?_)
          rw [map_sub, map_one]
          calc ‖φ ε - 1‖ ≤ ‖φ ε‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
            _ = 2 := by rw [habs φ, norm_one]; norm_num
      _ = 2 ^ Module.finrank ℚ E := by
          rw [Finset.prod_const, Finset.card_univ, NumberField.Embeddings.card]
  have hlowR : (2 : ℝ) ^ K ≤ 2 ^ Module.finrank ℚ E := by
    have : ((2 ^ K : ℕ) : ℝ) ≤ ((Algebra.norm ℤ (r - 1)).natAbs : ℝ) := by exact_mod_cast hlow
    push_cast at this
    linarith
  have := (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hlowR
  omega

end GlobalTheory
end

section

namespace GlobalTheory

open WittVector

theorem isPrecomplete_pi {R : Type*} [CommRing R] (I : Ideal R) [IsPrecomplete I R]
    (ι : Type*) [Finite ι] : IsPrecomplete I (ι → R) := by
  classical
  cases nonempty_fintype ι
  have coord : ∀ (J : Ideal R) (x : ι → R),
      x ∈ (J • ⊤ : Submodule R (ι → R)) ↔ ∀ i, x i ∈ (J • ⊤ : Submodule R R) := by
    intro J x
    constructor
    · intro hx i
      have h1 := Submodule.mem_map_of_mem (f := (LinearMap.proj i : (ι → R) →ₗ[R] R)) hx
      rw [Submodule.map_smul''] at h1
      exact Submodule.smul_mono le_rfl le_top h1
    · intro hx
      have hsum : x = ∑ i, (x i) • (Pi.single i (1 : R) : ι → R) := by
        ext j
        simp [Finset.sum_apply, Pi.single_apply]
      rw [hsum]
      refine Submodule.sum_mem _ fun i _ => ?_
      have hi : x i ∈ J := by simpa using hx i
      exact Submodule.smul_mem_smul hi Submodule.mem_top
  refine ⟨fun f hf => ?_⟩
  have hc : ∀ i, ∃ L : R, ∀ n, f n i ≡ L [SMOD (I ^ n • ⊤ : Submodule R R)] := by
    intro i
    refine IsPrecomplete.prec inferInstance (f := fun n => f n i) ?_
    intro m n hmn
    have := hf hmn
    rw [SModEq.sub_mem, coord] at this
    rw [SModEq.sub_mem]
    exact this i
  choose L hL using hc
  refine ⟨L, fun n => ?_⟩
  rw [SModEq.sub_mem, coord]
  intro i
  have := hL i n
  rwa [SModEq.sub_mem] at this

section

variable {p : ℕ} [Fact p.Prime] {k k' : Type} [Field k] [CharP k p] [PerfectRing k p]
  [Field k'] [CharP k' p] [PerfectRing k' p]

end

end GlobalTheory
end

section

open IsDedekindDomain Topology

namespace GlobalTheory.ValuationExtensionContinuous

theorem continuous_of_valuation_eq {A B Γ : Type} [Ring A] [Ring B]
    [LinearOrderedCommGroupWithZero Γ] [Valued A Γ] [Valued B Γ]
    (hs : Function.Surjective (Valued.v : A → Γ)) (g : A →+* B)
    (hg : ∀ a, Valued.v (g a) = (Valued.v a : Γ)) : Continuous g := by
  refine continuous_of_continuousAt_zero g ?_
  rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero A Γ).tendsto_iff
    (Valued.hasBasis_nhds_zero B Γ)]
  intro γ _
  obtain ⟨k, hk⟩ := hs (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)
  have hk0 : (Valued.v k : Γ) ≠ 0 := by
    rw [hk]
    exact (map_ne_zero _).mpr γ.ne_zero
  have hk1 : (Valued.v : Valuation A Γ).restrict k ≠ 0 := by simpa using hk0
  refine ⟨Units.mk0 _ hk1, trivial, fun x hx => ?_⟩
  simp only [Set.mem_setOf_eq, Units.val_mk0, Valuation.restrict_lt_iff] at hx
  simp only [Set.mem_setOf_eq]
  rw [Valuation.restrict_lt_iff_lt_embedding, hg, ← hk]
  exact hx

theorem exists_extension {K : Type} [Field K] [NumberField K] {R L : Type} [CommRing R]
    [IsDedekindDomain R] [Field L] [Algebra R L] [IsFractionRing R L]
    (w : HeightOneSpectrum (NumberField.RingOfIntegers K)) (u : HeightOneSpectrum R)
    (f : K →+* u.adicCompletion L)
    (hf : ∀ x : K, Valued.v (f x) = w.valuation K x) :
    ∃ φ : w.adicCompletion K →+* u.adicCompletion L, Continuous φ ∧
      (∀ x : K, φ (algebraMap K (w.adicCompletion K) x) = f x) ∧
      ∀ y : w.adicCompletion K, Valued.v (φ y) = Valued.v y := by
  let g : WithVal (w.valuation K) →+* u.adicCompletion L :=
    f.comp (WithVal.equiv (w.valuation K)).toRingHom
  have hg : Continuous g := by
    refine continuous_of_valuation_eq (fun c => ?_) g (fun a => hf _)
    obtain ⟨k, hk⟩ := w.valuation_surjective K c
    exact ⟨WithVal.toVal _ k, hk⟩
  let ψ := UniformSpace.Completion.extensionHom g hg
  let φ : w.adicCompletion K →+* u.adicCompletion L :=
    ψ.comp (HeightOneSpectrum.adicCompletion.equiv K w).toRingHom
  have hψ : Continuous ψ := UniformSpace.Completion.continuous_extension
  have hφ : Continuous φ :=
    hψ.comp (HeightOneSpectrum.adicCompletion.continuous_toCompletion K w)
  have hφa : ∀ a : WithVal (w.valuation K),
      φ (HeightOneSpectrum.adicCompletion.ofCompletion (a : (w.valuation K).Completion))
        = f a.ofVal := fun a => UniformSpace.Completion.extensionHom_coe g hg a
  refine ⟨φ, hφ, fun x => hφa (WithVal.toVal _ x), fun y => ?_⟩
  by_cases hy : y = 0
  · subst hy
    rw [map_zero, map_zero, map_zero]
  have h1 : (Valued.v y : WithZero (Multiplicative ℤ)) ≠ 0 := by simpa using hy
  have h2 : (Valued.v (φ y) : WithZero (Multiplicative ℤ)) ≠ 0 := by simpa using hy
  have hU := Filter.inter_mem (Valued.locally_const h1)
    (hφ.continuousAt.preimage_mem_nhds (Valued.locally_const h2))
  have hV := (HeightOneSpectrum.adicCompletion.continuous_ofCompletion K w).continuousAt
    (x := y.toCompletion) |>.preimage_mem_nhds hU
  obtain ⟨a, ha1, ha2⟩ := UniformSpace.Completion.denseRange_coe.mem_nhds hV
  simp only [Set.mem_preimage, Set.mem_setOf_eq] at ha1 ha2
  rw [← ha1, ← ha2, hφa, hf]
  exact (HeightOneSpectrum.adicCompletion.valued_coe K w a.ofVal).symm

end GlobalTheory.ValuationExtensionContinuous
end

section

namespace GlobalTheory


open IsDedekindDomain in
theorem exists_reps_coprime_outside_modulus : ∀ (A : Type) [CommRing A] [IsDedekindDomain A] (m : Ideal A) (a₀ b₀ : A), m ≠ ⊥ → ∃ a b : A, a - a₀ ∈ m ∧ b - b₀ ∈ m ∧ b ≠ 0 ∧ ∀ p : Ideal A, p.IsMaximal → ¬ m ≤ p → ¬ (a ∈ p ∧ b ∈ p) := by
  classical
  intro A _ _ m a₀ b₀ hm
  obtain ⟨b, hbm, hb0⟩ : ∃ b, b - b₀ ∈ m ∧ b ≠ 0 := by
    by_cases h : b₀ = 0
    · obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
      exact ⟨x, by simpa [h] using hx, hx0⟩
    · exact ⟨b₀, by simp, h⟩
  have hspan : Ideal.span {b} ≠ (0 : Ideal A) := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hb0
  have hfin : {v : HeightOneSpectrum A | v.asIdeal ∣ Ideal.span {b}}.Finite :=
    Ideal.finite_factors hspan
  let S := hfin.toFinset.filter (fun v => ¬ m ≤ v.asIdeal)
  let K : Ideal A := ⨅ v ∈ S, v.asIdeal
  have hK : m ⊔ K = ⊤ := by
    apply Ideal.sup_iInf_eq_top
    intro v hv
    have hv' : ¬ m ≤ v.asIdeal := (Finset.mem_filter.mp hv).2
    have hmax : v.asIdeal.IsMaximal := v.isMaximal
    by_contra hne
    rw [sup_comm] at hne
    have heq := hmax.eq_of_le hne le_sup_left
    exact hv' (heq ▸ le_sup_right)
  have h1 : (1 : A) ∈ m ⊔ K := by rw [hK]; exact Submodule.mem_top
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp h1
  refine ⟨a₀ * y + x, b, ?_, hbm, hb0, ?_⟩
  · have : a₀ * y + x - a₀ = x - a₀ * x := by
      have hy' : y = 1 - x := by rw [← hxy]; ring
      rw [hy']; ring
    rw [this]
    exact m.sub_mem hx (m.mul_mem_left a₀ hx)
  · rintro p hp hmp ⟨hap, hbp⟩
    have hp0 : p ≠ ⊥ := by
      rintro rfl
      exact hb0 ((Submodule.mem_bot A).mp hbp)
    let v : HeightOneSpectrum A := ⟨p, hp.isPrime, hp0⟩
    have hvS : v ∈ S := by
      refine Finset.mem_filter.mpr ⟨?_, hmp⟩
      rw [Set.Finite.mem_toFinset]
      show p ∣ Ideal.span {b}
      rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
      exact hbp
    have hKp : K ≤ p := iInf₂_le v hvS
    have hyp : y ∈ p := hKp hy
    have hxp : x ∈ p := by
      have := p.sub_mem hap (p.mul_mem_left a₀ hyp)
      simpa using this
    exact hp.ne_top ((Ideal.eq_top_iff_one p).mpr (hxy ▸ p.add_mem hxp hyp))

end GlobalTheory
end

section

namespace GlobalTheory

theorem residue_degree_one_of_linear_mem : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (P : Ideal B) [P.IsPrime] (θ : B) (D a b : A), (P.comap (algebraMap A B)).IsMaximal → (∀ y : B, ∃ u v : A, algebraMap A B D * y = algebraMap A B u + algebraMap A B v * θ) → algebraMap A B D ∉ P → algebraMap A B b ∉ P → algebraMap A B a + algebraMap A B b * θ ∈ P → ∀ y : B, ∃ u : A, y - algebraMap A B u ∈ P := by
  intro A B _ _ _ P _ θ D a b hmax hgen hD hb hab y
  obtain ⟨b', i, hi, hbi⟩ := hmax.exists_inv (x := b) (by rwa [Ideal.mem_comap])
  obtain ⟨D', j, hj, hDj⟩ := hmax.exists_inv (x := D) (by rwa [Ideal.mem_comap])
  rw [Ideal.mem_comap] at hi hj
  obtain ⟨u, v, hy⟩ := hgen y
  have hbi' := congrArg (algebraMap A B) hbi
  have hDj' := congrArg (algebraMap A B) hDj
  simp only [map_add (f := _), map_mul, map_one] at hbi' hDj'
  refine ⟨D' * (u - v * a * b'), ?_⟩
  have key : y - algebraMap A B (D' * (u - v * a * b')) =
      algebraMap A B D' * algebraMap A B v * algebraMap A B b' * (algebraMap A B a + algebraMap A B b * θ)
      + (algebraMap A B D' * algebraMap A B v * θ) * algebraMap A B i + y * algebraMap A B j := by
    simp only [map_sub, map_mul]
    linear_combination algebraMap A B D' * hy - y * hDj' - algebraMap A B D' * algebraMap A B v * θ * hbi'
  rw [key]
  exact P.add_mem (P.add_mem (P.mul_mem_left _ hab) (P.mul_mem_left _ hi)) (P.mul_mem_left _ hj)

end GlobalTheory
end

section

namespace GlobalTheory

open IsLocalRing Module nonZeroDivisors IsLocalization.AtPrime

attribute [local instance] Ideal.Quotient.field

theorem trace_quotient_eq_of_projective (R S : Type) [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [CommRing S] [IsDomain S] [IsIntegrallyClosed S] [Algebra R S]
    [Module.IsTorsionFree R S] [Module.Finite R S] [Module.Projective R S] (p : Ideal R)
    [p.IsMaximal] (x : S) :
    Algebra.trace (R ⧸ p) (S ⧸ p.map (algebraMap R S)) (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk p (Algebra.intTrace R S x) := by
  let Rₚ := Localization.AtPrime p
  let Sₚ := Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
  let : Algebra Rₚ Sₚ := localizationAlgebra p.primeCompl S
  have hp0 : p.primeCompl ≤ R⁰ := p.primeCompl_le_nonZeroDivisors
  have : IsDomain Rₚ := IsLocalization.isDomain_of_le_nonZeroDivisors _ hp0
  have : IsIntegrallyClosed Rₚ := isIntegrallyClosed_of_isLocalization _ _ hp0
  have : IsScalarTower R Rₚ Sₚ := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, ← IsScalarTower.algebraMap_eq])
  have : IsLocalization (Submonoid.map (algebraMap R S) (Ideal.primeCompl p)) Sₚ :=
    inferInstanceAs (IsLocalization (Algebra.algebraMapSubmonoid S p.primeCompl) Sₚ)
  have e : Algebra.algebraMapSubmonoid S p.primeCompl ≤ S⁰ :=
    Submonoid.map_le_of_le_comap _ <| p.primeCompl_le_nonZeroDivisors.trans
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (FaithfulSMul.algebraMap_injective _ _))
  have : IsDomain Sₚ := IsLocalization.isDomain_of_le_nonZeroDivisors _ e
  have : IsTorsionFree Rₚ Sₚ := by
    rw [isTorsionFree_iff_algebraMap_injective]
    exact IsLocalization.map_injective_of_injective p.primeCompl Rₚ Sₚ
      (FaithfulSMul.algebraMap_injective R S)
  have : Module.Finite Rₚ Sₚ := .of_isLocalization R S p.primeCompl
  have : IsIntegrallyClosed Sₚ := isIntegrallyClosed_of_isLocalization _ _ e
  have : Module.Flat Rₚ Sₚ :=
    Module.Flat.of_isLocalizedModule Rₚ p.primeCompl (IsScalarTower.toAlgHom R S Sₚ).toLinearMap
  have : Module.Free Rₚ Sₚ := Module.free_of_flat_of_isLocalRing
  apply (equivQuotMaximalIdeal p Rₚ).injective
  rw [trace_quotient_eq_trace_localization_quotient S p Rₚ Sₚ, IsScalarTower.algebraMap_eq S Sₚ,
    RingHom.comp_apply, Ideal.Quotient.algebraMap_eq, Algebra.trace_quotient_mk,
    ← Algebra.intTrace_eq_trace,
    ← Algebra.intTrace_eq_of_isLocalization R S p.primeCompl (Aₘ := Rₚ) (Bₘ := Sₚ) x]
  simp

end GlobalTheory
end
