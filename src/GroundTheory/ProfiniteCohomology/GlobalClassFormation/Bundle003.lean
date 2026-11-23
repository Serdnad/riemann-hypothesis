module

public import GroundTheory.GlobalFields.NormResidueSymbol.Infinite
public import GroundTheory.GlobalFields.NormResidueSymbol.RangeFiniteLocalNormLeKerLocalSymbol
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalRestriction
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalDegrees.Layers
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalDegrees.Decomposition
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IntermediateField GroundTheory.Global GroundTheory.Global.SemiLocal FiniteSubfield IsDedekindDomain

open scoped NumberField.LiesOver

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

attribute [local instance] FiniteSubfield.isGalois_of_normal

section Reciprocity

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]

theorem mk_eq_localReciprocityLimit_of_forall {x : kˣ} {g : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k}
    (hg : ∀ (y : AlgebraicClosure k)
      (hy : y ∈ GroundTheory.LocalField.maximalAbelianExtension k (AlgebraicClosure k)),
      g y = (GroundTheory.LocalField.localArtinMap k (AlgebraicClosure k) x ⟨y, hy⟩ : AlgebraicClosure k)) :
    (g : TopologicalAbelianization (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)) =
      GroundTheory.LocalField.localReciprocityLimit k (AlgebraicClosure k) x := by
  apply (GroundTheory.LocalField.topologicalAbelianizationEquiv k (AlgebraicClosure k)).injective
  rw [GroundTheory.LocalField.topologicalAbelianizationEquiv_mk, ← GroundTheory.LocalField.localArtinMap_apply]
  refine AlgEquiv.ext fun y ↦ Subtype.ext ?_
  rw [AlgEquiv.restrictNormalHom_apply]
  exact hg y y.2

end Reciprocity

variable {K : FiniteSubfield} (E : FiniteSubfield) [Fact (K ≤ E)]
  [(E.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).Normal] [IsMulCommutative (E.1 ≃ₐ[K.1] E.1)]

section Finite

variable {v : HeightOneSpectrum (𝓞 K.1)} (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure (v.adicCompletion K.1))

theorem completionEmbedding_normResidueSymbol {b : (v.adicCompletion K.1)ˣ}
    {g : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1)}
    (hg : ∀ (y : AlgebraicClosure (v.adicCompletion K.1))
      (hy : y ∈ GroundTheory.LocalField.maximalAbelianExtension (v.adicCompletion K.1)
        (AlgebraicClosure (v.adicCompletion K.1))),
      g y = (GroundTheory.LocalField.localArtinMap (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1)) b
        ⟨y, hy⟩ : AlgebraicClosure (v.adicCompletion K.1)))
    (y : (placeOfEmbedding ι E).1.adicCompletion E.1) :
    completionEmbedding ι E (normResidueSymbol (v.adicCompletion K.1) _ b y) =
      g (completionEmbedding ι E y) :=
  normResidueSymbol_spec _ (mk_eq_localReciprocityLimit_of_forall hg) y

theorem restrictHom_globalDecomp_of_finite {b : (v.adicCompletion K.1)ˣ}
    {g : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1)}
    (hg : ∀ (y : AlgebraicClosure (v.adicCompletion K.1))
      (hy : y ∈ GroundTheory.LocalField.maximalAbelianExtension (v.adicCompletion K.1)
        (AlgebraicClosure (v.adicCompletion K.1))),
      g y = (GroundTheory.LocalField.localArtinMap (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1)) b
        ⟨y, hy⟩ : AlgebraicClosure (v.adicCompletion K.1))) :
    restrictHom (E := E) (globalDecomp (v.adicCompletion K.1) ι g) = localSymbol E.1 v b := by
  refine AlgEquiv.ext fun l ↦ Subtype.val_injective (ι.injective ?_)
  change ι _ = ι _
  rw [coe_restrictHom_apply, globalDecomp_apply, ← completionEmbedding_algebraMap ι E (localSymbol E.1 v b l),
    algebraMap_localSymbol_apply E.1 v (placeOfEmbedding ι E), completionEmbedding_normResidueSymbol E ι hg,
    completionEmbedding_algebraMap]

end Finite

section Infinite

variable {v : InfinitePlace K.1} (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure v.Completion)


omit [(E.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).Normal] [IsMulCommutative (E.1 ≃ₐ[K.1] E.1)] in
theorem infCompletionEmbedding_localSymbol {b : v.Completionˣ}
    {g : Gal(AlgebraicClosure v.Completion/v.Completion)}
    (hg : g = 1 ↔ (b : v.Completion) ∈
      Set.range (Algebra.norm v.Completion : AlgebraicClosure v.Completion → v.Completion))
    (y : (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion) :
    infCompletionEmbedding ι E (InfinitePlace.localSymbol v (infPlaceOfEmbedding ι E : InfinitePlace E.1) b y) =
      g (infCompletionEmbedding ι E y) := by
  set w : InfinitePlace E.1 := (infPlaceOfEmbedding ι E : InfinitePlace E.1) with hw_def
  set j := infCompletionEmbedding ι E with hj_def
  set d := decompHom v.Completion j g with hd_def
  suffices h : InfinitePlace.localSymbol v w b = d by
    rw [h, hd_def]
    exact decompHom_apply j g _
  by_cases h2 : v.IsReal ∧ w.IsComplex
  · obtain ⟨hv, hw⟩ := h2
    have hfin : Module.finrank v.Completion w.Completion = 2 :=
      (InfinitePlace.finrank_completion_eq_two_iff w).2 ⟨hv, hw⟩
    have hinj : Function.Injective j.toLinearMap := j.injective
    have hsurj : Function.Surjective j := by
      have hle := LinearMap.finrank_le_finrank_of_injective hinj
      have heq : Module.finrank v.Completion w.Completion =
          Module.finrank v.Completion (AlgebraicClosure v.Completion) :=
        le_antisymm hle (hfin ▸ infAlgClosure_finrank_le_two v)
      exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).1 hinj
    let e : w.Completion ≃ₐ[v.Completion] AlgebraicClosure v.Completion :=
      AlgEquiv.ofBijective j ⟨j.injective, hsurj⟩
    have he : ∀ y, e y = j y := fun _ ↦ rfl
    have hd : d = 1 ↔ g = 1 := by
      constructor
      · intro hd1
        refine AlgEquiv.ext fun z ↦ ?_
        obtain ⟨y, rfl⟩ := hsurj z
        rw [← decompHom_apply, ← hd_def, hd1]
        rfl
      · rintro rfl
        exact map_one _
    have hs : InfinitePlace.localSymbol v w b = 1 ↔ d = 1 := by
      rw [hd, hg, ← MonoidHom.mem_ker, InfinitePlace.ker_localSymbol, InfinitePlace.normSubgroup,
        MonoidHom.mem_range]
      constructor
      · rintro ⟨y, hy⟩
        refine ⟨e y, ?_⟩
        rw [Algebra.norm_eq_of_algEquiv]
        exact congrArg Units.val hy
      · rintro ⟨z, hz⟩
        have hz0 : z ≠ 0 := by
          rintro rfl
          rw [Algebra.norm_zero] at hz
          exact b.ne_zero hz.symm
        refine ⟨Units.mk0 (e.symm z) ((map_ne_zero _).2 hz0), Units.ext ?_⟩
        rw [Units.coe_map, Units.val_mk0, ← Algebra.norm_eq_of_algEquiv e,
          e.apply_symm_apply, hz]
    have hc := InfinitePlace.completionConj_ne_one (w := w) hv hw
    rcases InfinitePlace.eq_one_or_eq_completionConj hv hw (InfinitePlace.localSymbol v w b) with h1 | h1 <;>
      rcases InfinitePlace.eq_one_or_eq_completionConj hv hw d with h3 | h3
    · rw [h1, h3]
    · exact absurd (h3 ▸ hs.1 h1) hc
    · exact absurd (h1 ▸ hs.2 h3) hc
    · rw [h1, h3]
  · have := InfinitePlace.subsingleton_gal w h2
    exact Subsingleton.elim _ _

theorem restrictHom_globalDecomp_of_infinite {b : v.Completionˣ}
    {g : Gal(AlgebraicClosure v.Completion/v.Completion)}
    (hg : g = 1 ↔ (b : v.Completion) ∈
      Set.range (Algebra.norm v.Completion : AlgebraicClosure v.Completion → v.Completion)) :
    restrictHom (E := E) (globalDecomp v.Completion ι g) = infiniteLocalSymbol E.1 v b := by
  refine AlgEquiv.ext fun l ↦ Subtype.val_injective (ι.injective ?_)
  change ι _ = ι _
  rw [coe_restrictHom_apply, globalDecomp_apply,
    ← infCompletionEmbedding_algebraMap ι E (infiniteLocalSymbol E.1 v b l),
    algebraMap_infiniteLocalSymbol_apply E.1 v (infPlaceOfEmbedding ι E),
    infCompletionEmbedding_localSymbol E ι hg, infCompletionEmbedding_algebraMap]

end Infinite

end

end GroundTheory.ProfCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IntermediateField GroundTheory.Global GroundTheory.Global.Cyclotomic GroundTheory.LocalField.Abstract
  FiniteSubfield IsDedekindDomain

open scoped GroundTheory.LocalField.Abstract Pointwise GroundTheory.Global.SemiLocal

noncomputable section

namespace CyclotomicLayer

local notation "ℚ̄" => AlgebraicClosure ℚ

section TotallyReal

end TotallyReal

section Order

theorem pow_dvd_addOrderOf_toZModPow {q : ℕ} [hq : Fact q.Prime] {n e a : ℕ} (hna : n + e ≤ a)
    {x : ℤ_[q]} (hx : PadicInt.toZModPow n x ≠ 0) :
    q ^ e ∣ addOrderOf (PadicInt.toZModPow a x) := by
  have hdvd : addOrderOf (PadicInt.toZModPow a x) ∣ q ^ a := by
    have := addOrderOf_dvd_natCard (PadicInt.toZModPow a x)
    rwa [Nat.card_zmod] at this
  obtain ⟨i, -, hieq⟩ := (Nat.dvd_prime_pow hq.out).1 hdvd
  rw [hieq]
  refine Nat.pow_dvd_pow q (not_lt.1 fun hie => hx ?_)
  have h0 : (q ^ (a - n)) • PadicInt.toZModPow a x = 0 :=
    addOrderOf_dvd_iff_nsmul_eq_zero.1 (hieq ▸ Nat.pow_dvd_pow q (by omega))
  have h1 : PadicInt.toZModPow a ((q : ℤ_[q]) ^ (a - n) * x) = 0 := by
    rw [nsmul_eq_mul, Nat.cast_pow] at h0
    rw [map_mul, map_pow, map_natCast]
    exact h0
  have h2 : (q : ℤ_[q]) ^ a ∣ (q : ℤ_[q]) ^ (a - n) * x := by
    rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker]
    exact h1
  have hsplit : (q : ℤ_[q]) ^ a = (q : ℤ_[q]) ^ (a - n) * (q : ℤ_[q]) ^ n := by
    rw [← pow_add]
    congr 1
    omega
  rw [hsplit] at h2
  have h3 : (q : ℤ_[q]) ^ n ∣ x :=
    (mul_dvd_mul_iff_left (pow_ne_zero _ (Nat.cast_ne_zero.2 hq.out.ne_zero))).1 h2
  rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton]
  exact h3

theorem pow_dvd_orderOf_degreeMod (r : ℕ+) (q : Nat.Primes) {n e a : ℕ} (hqr : (q : ℕ) ^ a ∣ (r : ℕ))
    (hna : n + e ≤ a) {σ : Gal(ℚ̄/ℚ)}
    (hσ : PadicInt.toZModPow n (Multiplicative.toAdd (degreeComponent q σ)) ≠ 0) :
    (q : ℕ) ^ e ∣ orderOf (degreeMod r σ) := by
  let f : Multiplicative (ZMod r) →* Multiplicative (ZMod ((q : ℕ) ^ a)) :=
    AddMonoidHom.toMultiplicative (ZMod.castHom hqr (ZMod ((q : ℕ) ^ a))).toAddMonoidHom
  refine dvd_trans ?_ (orderOf_map_dvd f _)
  have hf : f (degreeMod r σ) = Multiplicative.ofAdd
      (PadicInt.toZModPow a (Multiplicative.toAdd (degreeComponent q σ))) := by
    rw [← toPadicInt_degree, toZModPow_toPadicInt]
    exact congrArg Multiplicative.ofAdd
      (ProfiniteInteger.castHom_proj (m := primePowPNat (q : ℕ) a) hqr (Multiplicative.toAdd (degree σ)))
  rw [hf, orderOf_ofAdd_eq_addOrderOf]
  exact pow_dvd_addOrderOf_toZModPow hna hσ

theorem dvd_natCard_of_forall_pow_dvd_orderOf {G : Type*} [Group G] [Finite G] (A : Subgroup G)
    {m : ℕ} (hm : m ≠ 0)
    (h : ∀ q : ℕ, q.Prime → q ∣ m → ∃ y ∈ A, q ^ m.factorization q ∣ orderOf y) :
    m ∣ Nat.card A := by
  have hA : Nat.card A ≠ 0 := Nat.card_pos.ne'
  refine (Nat.factorization_prime_le_iff_dvd hm hA).1 fun q hq => ?_
  by_cases hqm : q ∣ m
  · obtain ⟨y, hy, hdvd⟩ := h q hq hqm
    have h1 : orderOf y ∣ Nat.card A := by
      have := orderOf_dvd_natCard (⟨y, hy⟩ : A)
      rwa [Subgroup.orderOf_mk] at this
    exact (hq.pow_dvd_iff_le_factorization hA).1 (hdvd.trans h1)
  · rw [Nat.factorization_eq_zero_of_not_dvd hqm]
    exact Nat.zero_le _

end Order

section Primes

theorem exists_prime_comap_eq (E : FiniteSubfield) (w : HeightOneSpectrum (𝓞 E.1)) :
    ∃ P : Ideal (𝓞 ℚ̄), P.IsPrime ∧ P.comap (ringOfIntegersIncl E.1) = w.asIdeal := by
  let _ : Algebra (𝓞 E.1) (𝓞 ℚ̄) := (ringOfIntegersIncl E.1).toAlgebra
  have : IsScalarTower ℤ (𝓞 E.1) (𝓞 ℚ̄) := IsScalarTower.of_algebraMap_eq fun x => by simp
  have : Algebra.IsIntegral ℤ (𝓞 ℚ̄) := ⟨fun b => RingOfIntegers.isIntegral b⟩
  have : Algebra.IsIntegral (𝓞 E.1) (𝓞 ℚ̄) := Algebra.IsIntegral.tower_top ℤ
  have hinj : Function.Injective (ringOfIntegersIncl E.1) := fun a b h =>
    RingOfIntegers.ext (Subtype.ext (congrArg (fun y : 𝓞 ℚ̄ => (y : ℚ̄)) h))
  have hker : (⊥ : Ideal (𝓞 ℚ̄)).comap (ringOfIntegersIncl E.1) = ⊥ := by
    rw [← RingHom.ker_eq_comap_bot]
    exact (RingHom.injective_iff_ker_eq_bot _).1 hinj
  have := w.isPrime
  obtain ⟨P, -, hP, hPw⟩ := Ideal.exists_ideal_over_prime_of_isIntegral w.asIdeal (⊥ : Ideal (𝓞 ℚ̄))
    (hker.le.trans bot_le)
  exact ⟨P, hP, hPw⟩

theorem comap_eq_of_liesOver {K E : FiniteSubfield} [Fact (K ≤ E)] {v : HeightOneSpectrum (𝓞 K.1)}
    (w : HeightOneSpectrum (𝓞 E.1)) [w.asIdeal.LiesOver v.asIdeal] {P : Ideal (𝓞 ℚ̄)}
    (hP : P.comap (ringOfIntegersIncl E.1) = w.asIdeal) :
    P.comap (ringOfIntegersIncl K.1) = v.asIdeal := by
  have h : ringOfIntegersIncl K.1 = (ringOfIntegersIncl E.1).comp (algebraMap (𝓞 K.1) (𝓞 E.1)) :=
    RingHom.ext fun _ => rfl
  rw [h, ← Ideal.comap_comap, hP, Ideal.over_def w.asIdeal v.asIdeal]

variable (K : FiniteSubfield) (r : ℕ+)

theorem restrictHom_mem_stabilizer (P : Ideal (𝓞 ℚ̄)) (g : K.1.fixingSubgroup)
    (hg : (g : Gal(ℚ̄/ℚ)) ∈ MulAction.stabilizer Gal(ℚ̄/ℚ) P) :
    restrictHom (E := cyclotomicLayer K r) g ∈ MulAction.stabilizer Gal((cyclotomicLayer K r).1/K.1)
      (P.comap (ringOfIntegersIncl (cyclotomicLayer K r).1)) := by
  rw [MulAction.mem_stabilizer_iff] at hg ⊢
  ext x
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, Ideal.mem_comap, Ideal.mem_comap, ← map_inv]
  have hx : ringOfIntegersIncl (cyclotomicLayer K r).1 (restrictHom (E := cyclotomicLayer K r) g⁻¹ • x) =
      ((g : Gal(ℚ̄/ℚ)))⁻¹ • ringOfIntegersIncl (cyclotomicLayer K r).1 x :=
    RingOfIntegers.ext rfl
  rw [hx, ← Ideal.mem_pointwise_smul_iff_inv_smul_mem, hg]

end Primes

section Main

theorem exists_dvd_finrank_cyclotomicLayer (K : FiniteSubfield) (S : Finset (HeightOneSpectrum (𝓞 K.1)))
    {m : ℕ} (hm : m ≠ 0) :
    ∃ r : ℕ+, ∀ v ∈ S, ∀ w : SemiLocal.PlacesOver (cyclotomicLayer K r).1 v,
      m ∣ Module.finrank (v.adicCompletion K.1) (w.1.adicCompletion (cyclotomicLayer K r).1) := by
  have h (v : HeightOneSpectrum (𝓞 K.1)) (q : Nat.Primes) :=
    exists_mem_stabilizer_toZModPow_degreeComponent_ne_zero (K := K) v q
  choose n hn using h
  let N : ℕ := S.sup fun v =>
    m.primeFactors.attach.sup fun q => n v ⟨q.1, Nat.prime_of_mem_primeFactors q.2⟩
  obtain ⟨r, hr⟩ : ∃ r : ℕ+, (r : ℕ) = m ^ (N + 1) :=
    ⟨⟨m ^ (N + 1), pow_pos (Nat.pos_of_ne_zero hm) _⟩, rfl⟩
  refine ⟨r, fun v hv w => ?_⟩
  rw [SemiLocal.finrank_eq_ramificationIdx_mul_inertiaDeg _ v w.1, ← card_decompositionGroup v w.1]
  refine dvd_trans ?_ (Subgroup.card_map_dvd _ (layerDegree K _))
  refine dvd_natCard_of_forall_pow_dvd_orderOf _ hm fun q hq hqm => ?_
  obtain ⟨P, hP, hPw⟩ := exists_prime_comap_eq (cyclotomicLayer K _) w.1
  have hPv : P.comap (ringOfIntegersIncl K.1) = v.asIdeal := comap_eq_of_liesOver w.1 hPw
  obtain ⟨σ, hσP, hσK, hσ⟩ := hn v ⟨q, hq⟩ P hP hPv
  refine ⟨degreeMod _ σ, Subgroup.mem_map.2 ⟨restrictHom (E := cyclotomicLayer K _) ⟨σ, hσK⟩, ?_,
    layerDegree_restrictHom K _ _⟩, ?_⟩
  · rw [← hPw]
    exact restrictHom_mem_stabilizer K _ P ⟨σ, hσK⟩ hσP
  · have hnN : n v ⟨q, hq⟩ ≤ N := by
      have hqmem : q ∈ m.primeFactors := Nat.mem_primeFactors.2 ⟨hq, hqm, hm⟩
      refine le_trans ?_ (Finset.le_sup (f := fun v =>
        m.primeFactors.attach.sup fun q => n v ⟨q.1, Nat.prime_of_mem_primeFactors q.2⟩) hv)
      exact Finset.le_sup (f := fun q : m.primeFactors => n v ⟨q.1, Nat.prime_of_mem_primeFactors q.2⟩)
        (Finset.mem_attach _ ⟨q, hqmem⟩)
    have he : 1 ≤ m.factorization q := (hq.dvd_iff_one_le_factorization hm).1 hqm
    have hqr : q ^ (N + m.factorization q) ∣ m ^ (N + 1) := by
      calc q ^ (N + m.factorization q) ∣ q ^ (m.factorization q * (N + 1)) :=
            Nat.pow_dvd_pow q (by nlinarith)
        _ = (q ^ m.factorization q) ^ (N + 1) := pow_mul _ _ _
        _ ∣ m ^ (N + 1) := pow_dvd_pow_of_dvd (Nat.ordProj_dvd m q) _
    exact pow_dvd_orderOf_degreeMod r ⟨q, hq⟩ (hr ▸ hqr) (by omega) hσ

theorem exists_cyclic_layer_dvd_localDegree (K : FiniteSubfield)
    (S : Finset (HeightOneSpectrum (𝓞 K.1))) {m : ℕ} (hm : m ≠ 0) :
    ∃ (E : FiniteSubfield) (_ : Fact (K ≤ E)), IsGalois K.1 E.1 ∧ IsCyclic Gal(E.1/K.1) ∧
      E.1 ≤ K.1 ⊔ zhatField ∧
      ∀ v ∈ S, ∀ w : SemiLocal.PlacesOver E.1 v,
        m ∣ Module.finrank (v.adicCompletion K.1) (w.1.adicCompletion E.1) := by
  obtain ⟨r, hr⟩ := exists_dvd_finrank_cyclotomicLayer K S hm
  exact ⟨cyclotomicLayer K r, inferInstance, inferInstance, inferInstance, cyclotomicLayer_le K r, hr⟩

end Main

end CyclotomicLayer

end

end GroundTheory.ProfCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField GroundTheory.Global FiniteSubfield

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield} (Kv : Type) {Ωv : Type} [Field Kv] [Field Ωv] [Algebra K.1 Kv] [Algebra Kv Ωv]
  [Algebra K.1 Ωv] [IsScalarTower K.1 Kv Ωv] [Algebra.IsIntegral Kv Ωv]


omit [Algebra.IsIntegral Kv Ωv] in
theorem globalDecomp_comp (ι : ℚ̄ →ₐ[K.1] Ωv) (g : K.1.fixingSubgroup) (σ : Gal(Ωv/Kv)) :
    globalDecomp Kv (ι.comp (fixingSubgroupEquiv K.1 g : ℚ̄ →ₐ[K.1] ℚ̄)) σ = g⁻¹ * globalDecomp Kv ι σ * g := by
  apply Subtype.ext
  apply AlgEquiv.ext
  intro y
  have h1 : ι ((g : ℚ̄ ≃ₐ[ℚ] ℚ̄) ((globalDecomp Kv (ι.comp (fixingSubgroupEquiv K.1 g : ℚ̄ →ₐ[K.1] ℚ̄)) σ :
      ℚ̄ ≃ₐ[ℚ] ℚ̄) y)) = σ (ι ((g : ℚ̄ ≃ₐ[ℚ] ℚ̄) y)) :=
    globalDecomp_apply Kv (ι.comp (fixingSubgroupEquiv K.1 g : ℚ̄ →ₐ[K.1] ℚ̄)) σ y
  have h2 := globalDecomp_apply Kv ι σ ((g : ℚ̄ ≃ₐ[ℚ] ℚ̄) y)
  have h3 : (g : ℚ̄ ≃ₐ[ℚ] ℚ̄) ((globalDecomp Kv (ι.comp (fixingSubgroupEquiv K.1 g : ℚ̄ →ₐ[K.1] ℚ̄)) σ :
      ℚ̄ ≃ₐ[ℚ] ℚ̄) y) = (globalDecomp Kv ι σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) ((g : ℚ̄ ≃ₐ[ℚ] ℚ̄) y) :=
    ι.injective (h1.trans h2.symm)
  change _ = ((g : ℚ̄ ≃ₐ[ℚ] ℚ̄)⁻¹ * (globalDecomp Kv ι σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) * (g : ℚ̄ ≃ₐ[ℚ] ℚ̄)) y
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, ← h3, ← AlgEquiv.mul_apply, inv_mul_cancel,
    AlgEquiv.one_apply]

instance isDiscreteRep_res_globalDecomp (ι : ℚ̄ →ₐ[K.1] Ωv) :
    IsDiscreteRep (Rep.res (globalDecomp Kv ι) (unitsLimitRep K)) :=
  IsDiscreteRep.res (continuous_globalDecomp Kv ι) _

theorem unitsLocalRes_comp (ι : ℚ̄ →ₐ[K.1] Ωv) (g : K.1.fixingSubgroup) (n : ℕ) :
    unitsLocalRes Kv (ι.comp (fixingSubgroupEquiv K.1 g : ℚ̄ →ₐ[K.1] ℚ̄)) n = unitsLocalRes Kv ι n := by
  have hconj := cohomologyMapAlong_conj (unitsLimitRep K) (continuous_globalDecomp Kv ι)
    (continuous_globalDecomp Kv (ι.comp (fixingSubgroupEquiv K.1 g : ℚ̄ →ₐ[K.1] ℚ̄))) g
    (globalDecomp_comp Kv ι g) n
  have e1 : unitsLocalRes Kv (ι.comp (fixingSubgroupEquiv K.1 g : ℚ̄ →ₐ[K.1] ℚ̄)) n =
      cohomologyMapAlong (globalDecomp Kv (ι.comp (fixingSubgroupEquiv K.1 g : ℚ̄ →ₐ[K.1] ℚ̄)))
        (continuous_globalDecomp Kv _) (𝟙 _) n ≫
      cohomologyMapAlong (MonoidHom.id _) continuous_id
        (unitsLocalMor Kv (ι.comp (fixingSubgroupEquiv K.1 g : ℚ̄ →ₐ[K.1] ℚ̄))) n := by
    rw [unitsLocalRes, ← cohomologyMapAlong_comp]
    rfl
  have e2 : unitsLocalRes Kv ι n =
      cohomologyMapAlong (globalDecomp Kv ι) (continuous_globalDecomp Kv ι) (𝟙 _) n ≫
      cohomologyMapAlong (MonoidHom.id _) continuous_id (unitsLocalMor Kv ι) n := by
    rw [unitsLocalRes, ← cohomologyMapAlong_comp]
    rfl
  rw [e1, hconj, Category.assoc, ← cohomologyMapAlong_comp, e2]
  congr 1
  refine cohomologyMapAlong_congr _ _ _ _ rfl (fun a => ?_) n
  apply Additive.toMul.injective
  apply Units.ext
  change ι ((g : ℚ̄ ≃ₐ[ℚ] ℚ̄) ((g : ℚ̄ ≃ₐ[ℚ] ℚ̄)⁻¹ ((Additive.toMul (a : Additive ℚ̄ˣ) : ℚ̄ˣ) : ℚ̄))) =
    ι ((Additive.toMul (a : Additive ℚ̄ˣ) : ℚ̄ˣ) : ℚ̄)
  rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

theorem unitsLocalRes_eq_of_algHom (ι ι' : ℚ̄ →ₐ[K.1] Ωv) (n : ℕ) :
    unitsLocalRes Kv ι' n = unitsLocalRes Kv ι n := by
  obtain ⟨g, hg⟩ := exists_eq_comp_of_normal ι ι'
  have : ι' = ι.comp (fixingSubgroupEquiv K.1 ((fixingSubgroupEquiv K.1).symm g) : ℚ̄ →ₐ[K.1] ℚ̄) := by
    rw [MulEquiv.apply_symm_apply]
    exact hg
  rw [this, unitsLocalRes_comp]

end

end GroundTheory.ProfCoh
end
