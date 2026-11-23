module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.Padics.LocalField
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.Norm.Transitivity

@[expose] public section

section

open NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.UnramSimpleGen

theorem not_mem_sq_of_derivative : ∀ (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E']
    (p : HeightOneSpectrum (𝓞 E)) (P : HeightOneSpectrum (𝓞 E')) (β : 𝓞 E') (f : Polynomial ℤ),
    f.Monic → Polynomial.aeval β f = 0 → Algebra.adjoin E {(β : E')} = ⊤ →
    (∀ x : 𝓞 E, algebraMap (𝓞 E) (𝓞 E') x ∈ P.asIdeal ↔ x ∈ p.asIdeal) →
    Polynomial.aeval β (Polynomial.derivative f) ∉ P.asIdeal →
    ∀ c : 𝓞 E, c ∉ p.asIdeal ^ 2 → algebraMap (𝓞 E) (𝓞 E') c ∉ P.asIdeal ^ 2 := by
  intro E E' _ _ _ _ _ p P β f _ hβ hadj hPp hder c hc

  have hmem := aeval_derivative_mem_differentIdeal (𝓞 E) E E' β hadj
  have hint : IsIntegral (𝓞 E) β := Algebra.IsIntegral.isIntegral β
  have hdvd : minpoly (𝓞 E) β ∣ f.map (algebraMap ℤ (𝓞 E)) :=
    minpoly.isIntegrallyClosed_dvd hint (by rw [aeval_map_algebraMap]; exact hβ)
  obtain ⟨k, hk⟩ := hdvd
  have hfd : aeval β (derivative f) = aeval β (derivative (minpoly (𝓞 E) β)) * aeval β k := by
    have h := congrArg (fun q => aeval β (derivative q)) hk
    simp only [derivative_mul, map_add (f := _), map_mul, minpoly.aeval, zero_mul, add_zero] at h
    rw [← h, derivative_map, aeval_map_algebraMap]
  have hnd : ¬ P.asIdeal ∣ differentIdeal (𝓞 E) (𝓞 E') := by
    intro h
    apply hder
    rw [hfd]
    exact Ideal.mul_mem_right _ _ ((Ideal.dvd_iff_le.1 h) hmem)

  haveI := p.isMaximal
  have hnle : ¬ p.asIdeal.map (algebraMap (𝓞 E) (𝓞 E')) ≤ P.asIdeal ^ 2 := by
    intro hle
    have h := pow_sub_one_dvd_differentIdeal (𝓞 E) (p := p.asIdeal) P.asIdeal 2 p.ne_bot
      (Ideal.dvd_iff_le.2 hle)
    exact hnd (by simpa using h)

  by_cases hcp : c ∈ p.asIdeal
  swap
  · intro h
    exact hcp ((hPp c).1 (Ideal.pow_le_self two_ne_zero h))

  obtain ⟨J, hJ⟩ : p.asIdeal ∣ Ideal.span {c} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hcp)
  have hJp : ¬ J ≤ p.asIdeal := by
    intro h
    apply hc
    have h1 : Ideal.span {c} ≤ p.asIdeal ^ 2 := by
      rw [hJ, pow_two]; exact Ideal.mul_mono_right h
    exact h1 (Ideal.mem_span_singleton_self c)
  obtain ⟨s, hsJ, hsp⟩ := Set.not_subset.1 hJp
  have hps : p.asIdeal * Ideal.span {s} ≤ Ideal.span {c} := by
    rw [hJ]; exact Ideal.mul_mono_right ((Ideal.span_singleton_le_iff_mem _).2 hsJ)
  intro hcP
  apply hnle
  have hs' : algebraMap (𝓞 E) (𝓞 E') s ∉ P.asIdeal := fun h => hsp ((hPp s).1 h)
  have hcop : IsCoprime P.asIdeal (Ideal.span {algebraMap (𝓞 E) (𝓞 E') s}) := by
    rw [Ideal.isCoprime_iff_sup_eq]
    refine P.isMaximal.1.2 _ (lt_of_le_of_ne le_sup_left fun h => hs' ?_)
    rw [h]; exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  have hdiv : P.asIdeal ^ 2 ∣ p.asIdeal.map (algebraMap (𝓞 E) (𝓞 E')) *
      Ideal.span {algebraMap (𝓞 E) (𝓞 E') s} := by
    rw [Ideal.dvd_iff_le]
    calc p.asIdeal.map (algebraMap (𝓞 E) (𝓞 E')) * Ideal.span {algebraMap (𝓞 E) (𝓞 E') s}
        = (p.asIdeal * Ideal.span {s}).map (algebraMap (𝓞 E) (𝓞 E')) := by
          rw [Ideal.map_mul, Ideal.map_span, Set.image_singleton]
      _ ≤ (Ideal.span {c}).map (algebraMap (𝓞 E) (𝓞 E')) := Ideal.map_mono hps
      _ = Ideal.span {algebraMap (𝓞 E) (𝓞 E') c} := by rw [Ideal.map_span, Set.image_singleton]
      _ ≤ P.asIdeal ^ 2 := (Ideal.span_singleton_le_iff_mem _).2 hcP
  exact Ideal.dvd_iff_le.1 ((hcop.pow_left).dvd_of_dvd_mul_right hdiv)

end GlobalTheory.UnramSimpleGen
end

section

open NumberField IsDedekindDomain Polynomial

namespace GlobalTheory

theorem natCard_le_of_forall_pow_eq_self (F : Type*) [CommRing F] [IsDomain F] [Finite F]
    (q : ℕ) (hq : 1 < q) (h : ∀ x : F, x ^ q = x) : Nat.card F ≤ q := by
  classical
  haveI := Fintype.ofFinite F
  have hne : (X ^ q - X : F[X]) ≠ 0 := by
    intro h0
    have h1 := congrArg Polynomial.natDegree (sub_eq_zero.1 h0)
    rw [natDegree_X_pow, natDegree_X] at h1
    omega
  have hdeg : (X ^ q - X : F[X]).natDegree ≤ q := by
    refine (natDegree_sub_le _ _).trans ?_
    rw [natDegree_X_pow, natDegree_X]
    omega
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
  refine le_trans ?_ hdeg
  refine Polynomial.card_le_degree_of_subset_roots ?_
  intro x _
  rw [mem_roots hne]
  simp [h x]

theorem exists_finite_ncard_primesOver_eq_finrank_of_pow_absNorm_sub_mem :
    ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
      [IsGalois K M], ∃ T : Set (HeightOneSpectrum (𝓞 K)), T.Finite ∧
      ∀ v : HeightOneSpectrum (𝓞 K), v ∉ T →
        (∀ P ∈ v.asIdeal.primesOver (𝓞 M), ∀ x : 𝓞 M, x ^ Ideal.absNorm v.asIdeal - x ∈ P) →
        (v.asIdeal.primesOver (𝓞 M)).ncard = Module.finrank K M ∧
          ∀ P ∈ v.asIdeal.primesOver (𝓞 M), Ideal.absNorm P = Ideal.absNorm v.asIdeal := by
  intro K M _ _ _ _ _ _
  have hD : differentIdeal (𝓞 K) (𝓞 M) ≠ ⊥ := differentIdeal_ne_bot
  refine ⟨(fun P : HeightOneSpectrum (𝓞 M) => P.under (𝓞 K)) ''
    {P | P.asIdeal ∣ differentIdeal (𝓞 K) (𝓞 M)}, (Ideal.finite_factors hD).image _, ?_⟩
  intro v hv hx
  haveI := v.isPrime
  have hq : 1 < Ideal.absNorm v.asIdeal := by
    have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
    have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
    omega
  have hf : ∀ P ∈ v.asIdeal.primesOver (𝓞 M), P.inertiaDeg (𝓞 K) = 1 := by
    intro P hP
    haveI := hP.1
    haveI := hP.2
    have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P
    haveI : Finite (𝓞 M ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hP0
    have hle : Nat.card (𝓞 M ⧸ P) ≤ Ideal.absNorm v.asIdeal := by
      refine natCard_le_of_forall_pow_eq_self _ _ hq fun y => ?_
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [← map_pow, Ideal.Quotient.eq]
      exact hx P hP x
    have hN : Ideal.absNorm P = Nat.card (𝓞 M ⧸ P) := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    have h := Ideal.absNorm_pow_inertiaDeg v.asIdeal P
    rw [← hN, ← h] at hle
    have hpos : 0 < P.inertiaDeg (𝓞 K) := P.inertiaDeg_pos (𝓞 K)
    have h2 : P.inertiaDeg (𝓞 K) ≤ 1 := by
      rw [← Nat.pow_le_pow_iff_right hq, pow_one]; exact hle
    omega
  have he : ∀ P ∈ v.asIdeal.primesOver (𝓞 M), P.ramificationIdx (𝓞 K) = 1 := by
    intro P hP
    haveI := hP.1
    haveI := hP.2
    have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P
    have hn : ¬ P ∣ differentIdeal (𝓞 K) (𝓞 M) := by
      intro hd
      refine hv ⟨⟨P, hP.1, hP0⟩, hd, ?_⟩
      ext1
      exact (Ideal.over_def P v.asIdeal).symm
    haveI : Algebra.IsUnramifiedAt (𝓞 K) P := not_dvd_differentIdeal_iff.1 hn
    exact Ideal.ramificationIdx_eq_one P (𝓞 K)
  refine ⟨?_, fun P hP => ?_⟩
  · obtain ⟨P⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 M)))
    haveI := P.2.1
    haveI := P.2.2
    have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn v.asIdeal (𝓞 M)
      Gal(M/K)
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal P.1 Gal(M/K),
      Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal P.1 Gal(M/K), he P.1 P.2, hf P.1 P.2,
      IsGalois.card_aut_eq_finrank] at h
    simpa using h
  · haveI := hP.1
    haveI := hP.2
    rw [← Ideal.absNorm_pow_inertiaDeg v.asIdeal P, hf P hP, pow_one]

end GlobalTheory
end

section

open NumberField IsDedekindDomain

namespace GlobalTheory

theorem norm_pos_of_totallyPositive (E E' : Type) [Field E] [NumberField E] [Field E']
    [NumberField E'] [Algebra E E'] (a : E') (ha : a ≠ 0) (hpos : ∀ φ : E' →+* ℝ, 0 < φ a)
    (φ : E →+* ℝ) : 0 < φ (Algebra.norm E a) := by
  letI : Algebra E ℂ := (Complex.ofRealHom.comp φ).toAlgebra
  have hmap : ∀ x, algebraMap E ℂ x = ((φ x : ℝ) : ℂ) := fun x => rfl
  have key := Algebra.norm_eq_prod_embeddings E ℂ a
  let g : (E' →ₐ[E] ℂ) → (E' →ₐ[E] ℂ) := fun σ =>
    { (starRingEnd ℂ).comp σ.toRingHom with
      commutes' := fun x => by
        show (starRingEnd ℂ) (σ (algebraMap E E' x)) = algebraMap E ℂ x
        rw [σ.commutes, hmap, Complex.conj_ofReal] }
  have hg : ∀ σ x, g σ x = (starRingEnd ℂ) (σ x) := fun σ x => rfl
  have hne : ∀ σ : E' →ₐ[E] ℂ, σ a ≠ 0 := fun σ => (map_ne_zero σ).2 ha
  have hnorm : ∀ σ : E' →ₐ[E] ℂ, ((‖σ a‖ : ℝ) : ℂ) ≠ 0 := fun σ => by
    exact_mod_cast (norm_ne_zero_iff.2 (hne σ))
  have h1 : ∏ σ : E' →ₐ[E] ℂ, σ a / ((‖σ a‖ : ℝ) : ℂ) = 1 := by
    refine Finset.prod_involution (fun σ _ => g σ) ?_ ?_ (fun _ _ => Finset.mem_univ _) ?_
    · intro σ _
      rw [hg, Complex.norm_conj, div_mul_div_comm, Complex.mul_conj, div_eq_one_iff_eq
        (mul_ne_zero (hnorm σ) (hnorm σ)), Complex.normSq_eq_norm_sq]
      push_cast; ring
    · intro σ _ hf hgs
      apply hf
      have hreal : ComplexEmbedding.IsReal σ.toRingHom := by
        rw [ComplexEmbedding.isReal_iff]
        ext x
        rw [ComplexEmbedding.conjugate_coe_eq]
        exact congrArg (fun τ : E' →ₐ[E] ℂ => τ x) hgs
      have hc : σ a = ((hreal.embedding a : ℝ) : ℂ) := (hreal.coe_embedding_apply a).symm
      have hp := hpos hreal.embedding
      rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
      exact div_self (by exact_mod_cast hp.ne')
    · intro σ _
      ext x
      simp [hg]
  rw [Finset.prod_div_distrib, div_eq_one_iff_eq (Finset.prod_ne_zero_iff.2 fun σ _ => hnorm σ)]
    at h1
  rw [h1, hmap] at key
  have hr : φ (Algebra.norm E a) = ∏ σ : E' →ₐ[E] ℂ, ‖σ a‖ := by
    apply Complex.ofReal_injective
    rw [key]; push_cast; rfl
  rw [hr]
  exact Finset.prod_pos fun σ _ => norm_pos_iff.2 (hne σ)

end GlobalTheory
end

section

open NumberField IsDedekindDomain Polynomial

namespace GlobalTheory

theorem isTotallyComplex_of_primitiveRoot (K : Type) [Field K] [NumberField K] (ζ : K) (m : ℕ)
    (hζ : IsPrimitiveRoot ζ m) (hm : 3 ≤ m) : NumberField.IsTotallyComplex K := by
  rw [NumberField.isTotallyComplex_iff]
  intro v
  by_contra hc
  have hr : v.IsReal := InfinitePlace.not_isComplex_iff_isReal.mp hc
  set ψ : K →+* ℝ := InfinitePlace.embedding_of_isReal hr
  have hψ : IsPrimitiveRoot (ψ ζ) m := hζ.map_of_injective ψ.injective
  have hm0 : m ≠ 0 := by omega
  have h1 : ψ ζ ^ m = 1 := hψ.pow_eq_one
  have h2 : ψ ζ ^ 2 = 1 := by
    rcases (pow_eq_one_iff_of_ne_zero hm0).mp h1 with h | ⟨h, _⟩ <;> rw [h] <;> norm_num
  have h3 : ψ (ζ ^ 2) = ψ 1 := by rw [map_pow, h2, map_one]
  have h4 : ζ ^ 2 = 1 := ψ.injective h3
  have h5 : m ∣ 2 := hζ.pow_eq_one_iff_dvd 2 |>.mp h4
  have := Nat.le_of_dvd (by norm_num) h5
  omega

theorem tcroot : ∀ (K : Type) [Field K] [NumberField K] (ζ : K) (m : ℕ), IsPrimitiveRoot ζ m → 3 ≤ m →
    NumberField.IsTotallyComplex K :=
  fun K _ _ ζ m hζ hm => isTotallyComplex_of_primitiveRoot K ζ m hζ hm

end GlobalTheory
end

section

open NumberField NumberField.InfinitePlace NumberField.Units NumberField.Units.dirichletUnitTheorem

namespace GlobalTheory.IntegerUnitBound


open scoped Classical in
theorem exists_unit_norm_add_le (E : Type) [Field E] [NumberField E] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : logSpace E, ∃ u : (𝓞 E)ˣ,
      ∀ w, |v w + logEmbedding E (Additive.ofMul u) w| ≤ C := by
  classical
  let B := (basisUnitLattice E).ofZLatticeBasis (E := logSpace E) ℝ (unitLattice E)
  refine ⟨∑ i, ‖B i‖, Finset.sum_nonneg fun i _ => norm_nonneg _, fun v => ?_⟩

  have hmem : -((ZSpan.floor B v : logSpace E)) ∈ unitLattice E := by
    rw [← Module.Basis.ofZLatticeBasis_span ℝ (unitLattice E) (basisUnitLattice E)]
    exact neg_mem (ZSpan.floor B v).2
  obtain ⟨x, -, hx⟩ := Submodule.mem_map.1 hmem
  refine ⟨Additive.toMul x, fun w => ?_⟩
  have hsum : v + logEmbedding E (Additive.ofMul (Additive.toMul x)) = ZSpan.fract B v := by
    have hx' : logEmbedding E x = -((ZSpan.floor B v : logSpace E)) := hx
    rw [ofMul_toMul, hx', ZSpan.fract_apply, sub_eq_add_neg]
  calc |v w + logEmbedding E (Additive.ofMul (Additive.toMul x)) w|
      = ‖(v + logEmbedding E (Additive.ofMul (Additive.toMul x))) w‖ := by
        rw [Real.norm_eq_abs, Pi.add_apply]
    _ ≤ ‖v + logEmbedding E (Additive.ofMul (Additive.toMul x))‖ := norm_le_pi_norm _ w
    _ = ‖ZSpan.fract B v‖ := by rw [hsum]
    _ ≤ ∑ i, ‖B i‖ := ZSpan.norm_fract_le B v


open scoped Classical in
theorem exists_unit_of_sum_eq_zero (E : Type) [Field E] [NumberField E] :
    ∃ C : ℝ, ∀ t : InfinitePlace E → ℝ, ∑ w, (mult w : ℝ) * t w = 0 → ∃ u : (𝓞 E)ˣ,
      ∀ w : InfinitePlace E, |t w + Real.log (w (u : E))| ≤ C := by
  classical
  obtain ⟨C₁, hC₁, hC⟩ := exists_unit_norm_add_le E
  refine ⟨Fintype.card (InfinitePlace E) * C₁, fun t ht => ?_⟩
  obtain ⟨u, hu⟩ := hC (fun w => (mult w.1 : ℝ) * t w.1)
  refine ⟨u, ?_⟩

  have hoff : ∀ w : {w : InfinitePlace E // w ≠ w₀},
      |(mult w.1 : ℝ) * (t w.1 + Real.log (w.1 (u : E)))| ≤ C₁ := by
    intro w
    have h := hu w
    rw [logEmbedding_component] at h
    rwa [mul_add]

  have hone : ∀ w : InfinitePlace E,
      |t w + Real.log (w (u : E))| ≤ |(mult w : ℝ) * (t w + Real.log (w (u : E)))| := by
    intro w
    rw [abs_mul, abs_of_pos (Nat.cast_pos.2 mult_pos : (0 : ℝ) < mult w)]
    exact le_mul_of_one_le_left (abs_nonneg _) one_le_mult
  have hcard : C₁ ≤ Fintype.card (InfinitePlace E) * C₁ := by
    have h : (1 : ℝ) ≤ Fintype.card (InfinitePlace E) := by exact_mod_cast Fintype.card_pos
    nlinarith
  intro w
  by_cases hw : w = w₀
  ·
    subst hw
    have htot : ∑ w : InfinitePlace E, (mult w : ℝ) * (t w + Real.log (w (u : E))) = 0 := by
      simp only [mul_add, Finset.sum_add_distrib, ht, sum_mult_mul_log, add_zero]
    rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀] at htot
    calc |t w₀ + Real.log (w₀ (u : E))|
        ≤ |(mult w₀ : ℝ) * (t w₀ + Real.log (w₀ (u : E)))| := hone w₀
      _ = |∑ w : {w : InfinitePlace E // w ≠ w₀}, (mult w.1 : ℝ) * (t w.1 + Real.log (w.1 (u : E)))| := by
        rw [eq_neg_of_add_eq_zero_left htot, abs_neg]
      _ ≤ ∑ w : {w : InfinitePlace E // w ≠ w₀}, |(mult w.1 : ℝ) * (t w.1 + Real.log (w.1 (u : E)))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _w : {w : InfinitePlace E // w ≠ w₀}, C₁ := Finset.sum_le_sum fun w _ => hoff w
      _ = Fintype.card {w : InfinitePlace E // w ≠ w₀} * C₁ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ Fintype.card (InfinitePlace E) * C₁ := by
        gcongr
        exact_mod_cast Fintype.card_subtype_le _
  · exact (hone w).trans ((hoff ⟨w, hw⟩).trans hcard)

theorem exists_unit_int_abs_le (E : Type) [Field E] [NumberField E] :
    ∃ R : ℝ, ∀ t : InfinitePlace E → ℝ, ∃ (u : (𝓞 E)ˣ) (n : ℤ), ∀ w : InfinitePlace E,
      |t w + Real.log (w (algebraMap (𝓞 E) E (u : 𝓞 E))) + (n : ℝ)| ≤ R := by
  classical
  obtain ⟨C, hC⟩ := exists_unit_of_sum_eq_zero E
  refine ⟨C + 1, fun t => ?_⟩

  have hmpos : 0 < ∑ w : InfinitePlace E, (mult w : ℝ) :=
    Finset.sum_pos (fun w _ => Nat.cast_pos.2 mult_pos) Finset.univ_nonempty
  set s : ℝ := (∑ w : InfinitePlace E, (mult w : ℝ) * t w) / ∑ w : InfinitePlace E, (mult w : ℝ) with hs
  have hms : (∑ w : InfinitePlace E, (mult w : ℝ)) * s = ∑ w : InfinitePlace E, (mult w : ℝ) * t w := by
    rw [hs]
    field_simp
  have hsum : ∑ w : InfinitePlace E, (mult w : ℝ) * (t w - s) = 0 := by
    rw [Finset.sum_congr rfl fun w _ => mul_sub (mult w : ℝ) (t w) s, Finset.sum_sub_distrib,
      ← Finset.sum_mul, hms, sub_self]
  obtain ⟨u, hu⟩ := hC (fun w => t w - s) hsum

  refine ⟨u, -⌊s⌋, fun w => ?_⟩
  have h1 := abs_le.1 (hu w)
  have h2 := Int.fract_nonneg s
  have h3 := Int.fract_lt_one s
  have hcoe : algebraMap (𝓞 E) E (u : 𝓞 E) = (u : E) := rfl
  have heq : t w + Real.log (w (algebraMap (𝓞 E) E (u : 𝓞 E))) + ((-⌊s⌋ : ℤ) : ℝ) =
      (t w - s + Real.log (w (u : E))) + Int.fract s := by
    rw [hcoe, Int.fract]
    push_cast
    ring
  rw [heq, abs_le]
  constructor <;> linarith [h1.1, h1.2]

end GlobalTheory.IntegerUnitBound
end

section

namespace GlobalTheory

theorem padicInt_hom_normalize : ∀ {G : Type} [Group G] [TopologicalSpace G] (p : ℕ) [Fact p.Prime] (χ : G → ℤ_[p]), Continuous χ → (∀ g h, χ (g * h) = χ g + χ h) → ∀ (g₀ : G), χ g₀ ≠ 0 → ∃ ψ : G → ℤ_[p], Continuous ψ ∧ (∀ g h, ψ (g * h) = ψ g + ψ h) ∧ (∀ g, χ g = 0 → ψ g = 0) ∧ ∃ g, ψ g = 1 := by
  intro G _ _ p _ χ hχ hadd g₀ hg₀
  classical
  have hex : ∃ n : ℕ, ∃ g, χ g ≠ 0 ∧ (χ g).valuation = n := ⟨_, g₀, hg₀, rfl⟩
  obtain ⟨g₁, hg₁, hv₁⟩ := Nat.find_spec hex
  have hmin : ∀ g, χ g ≠ 0 → (χ g₁).valuation ≤ (χ g).valuation := by
    intro g hg
    rw [hv₁]
    exact Nat.find_min' hex ⟨g, hg, rfl⟩
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hle : ∀ g, ‖χ g‖ ≤ ‖χ g₁‖ := by
    intro g
    by_cases hg : χ g = 0
    · rw [hg, norm_zero]; exact norm_nonneg _
    rw [PadicInt.norm_eq_zpow_neg_valuation hg, PadicInt.norm_eq_zpow_neg_valuation hg₁]
    apply zpow_le_zpow_right₀ hp1
    have := hmin g hg
    omega
  have hn₁ : (χ g₁ : ℚ_[p]) ≠ 0 := fun h => hg₁ (PadicInt.coe_eq_zero.1 h)
  have hbd : ∀ g, ‖(χ g : ℚ_[p]) / (χ g₁ : ℚ_[p])‖ ≤ 1 := by
    intro g
    rw [norm_div, div_le_one (norm_pos_iff.2 hn₁)]
    exact hle g
  refine ⟨fun g => ⟨(χ g : ℚ_[p]) / (χ g₁ : ℚ_[p]), hbd g⟩, ?_, ?_, ?_, g₁, ?_⟩
  · apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp hχ).div_const _
  · intro g h
    apply Subtype.ext
    show ((χ (g * h) : ℚ_[p])) / (χ g₁ : ℚ_[p]) = (χ g : ℚ_[p]) / (χ g₁ : ℚ_[p]) + (χ h : ℚ_[p]) / (χ g₁ : ℚ_[p])
    rw [hadd, PadicInt.coe_add, add_div]
  · intro g hg
    apply Subtype.ext
    simp [hg]
  · apply Subtype.ext
    simp [div_self hn₁]

end GlobalTheory
end
