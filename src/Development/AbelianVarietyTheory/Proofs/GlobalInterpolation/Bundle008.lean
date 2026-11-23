module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Unramified.Locus
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.RingTheory.WittVector.Basic
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
public import Mathlib.NumberTheory.RamificationInertia.Basic
public import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.Domain
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
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.RingTheory.FractionalIdeal.Inverse
public import Mathlib.Algebra.Algebra.Hom.Rat
public import Mathlib.RingTheory.Filtration
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.WittVector.Identities

@[expose] public section

section

open scoped TensorProduct
open NumberField IsDedekindDomain

namespace GlobalTheory


open scoped TensorProduct in
open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.quadratic_unramified_iff_inert_or_split (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (h2 : Module.finrank F E = 2) (v : HeightOneSpectrum (𝓞 F)) :
    ((∀ w : HeightOneSpectrum (𝓞 E), w.asIdeal.LiesOver v.asIdeal →
        Algebra.IsUnramifiedAt (𝓞 F) w.asIdeal) ↔
      ((v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E))).IsPrime ∨
        (v.asIdeal.primesOver (𝓞 E)).ncard = 2)) := by
  classical
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  set I := v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) with hIdef
  set M := UniqueFactorizationMonoid.normalizedFactors I with hMdef
  set s := IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 E) with hsdef
  have hv : v.asIdeal ≠ ⊥ := v.ne_bot
  have hI : I ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))).not.mpr hv
  have hs : ∀ P, P ∈ s ↔ P ∈ v.asIdeal.primesOver (𝓞 E) :=
    fun P => IsDedekindDomain.mem_primesOverFinset_iff hv (𝓞 E)
  have hM : ∀ P, P ∈ v.asIdeal.primesOver (𝓞 E) ↔ P ∈ M :=
    fun P => Ideal.mem_primesOver_iff_mem_normalizedFactors (𝓞 E) hv
  have hcount : ∀ P ∈ v.asIdeal.primesOver (𝓞 E), P.ramificationIdx (𝓞 F) = M.count P := by
    intro P hP
    haveI : P.LiesOver v.asIdeal := hP.2
    exact Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count v.asIdeal P hI
  have hsum : ∑ P ∈ s, P.ramificationIdx (𝓞 F) * v.asIdeal.inertiaDeg' P = 2 := by
    rw [← h2, ← Ideal.sum_ramification_inertia (𝓞 E) F E hv]
    refine Finset.sum_congr rfl fun P hP => ?_
    have hP' := (hs P).1 hP
    haveI : P.IsPrime := hP'.1
    haveI : P.LiesOver v.asIdeal := hP'.2
    rw [Ideal.ramificationIdx_eq_ramificationIdx' v.asIdeal P hv]
  have hterm : ∀ P ∈ s, 1 ≤ P.ramificationIdx (𝓞 F) * v.asIdeal.inertiaDeg' P := by
    intro P hP
    have hP' := (hs P).1 hP
    haveI : P.IsPrime := hP'.1
    haveI : P.LiesOver v.asIdeal := hP'.2
    have h1 : 0 < P.ramificationIdx (𝓞 F) := Ideal.ramificationIdx_pos (R := 𝓞 F) P
    have h2 : 0 < v.asIdeal.inertiaDeg' P := Ideal.inertiaDeg'_pos v.asIdeal P
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero h1.ne' h2.ne')
  have hncard : (v.asIdeal.primesOver (𝓞 E)).ncard = s.card := by
    rw [← Set.ncard_coe_finset, hsdef, IsDedekindDomain.coe_primesOverFinset hv]
  have hcard_le : s.card ≤ 2 := by
    have := Finset.card_nsmul_le_sum s _ 1 hterm
    simpa [hsum] using this
  have hcard_pos : 0 < s.card := by
    rw [← hncard]
    exact Nat.pos_of_ne_zero (IsDedekindDomain.primesOver_ncard_ne_zero v.asIdeal (𝓞 E))
  have hU : (∀ w : HeightOneSpectrum (𝓞 E), w.asIdeal.LiesOver v.asIdeal →
      Algebra.IsUnramifiedAt (𝓞 F) w.asIdeal) ↔ ∀ P ∈ s, P.ramificationIdx (𝓞 F) = 1 := by
    constructor
    · intro h P hP
      have hP' := (hs P).1 hP
      haveI : P.IsPrime := hP'.1
      haveI : P.LiesOver v.asIdeal := hP'.2
      have hPb : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hv P
      exact Algebra.isUnramifiedAt_iff_of_isDedekindDomain.1 (h ⟨P, hP'.1, hPb⟩ hP'.2)
    · intro h w hw
      have hmem : w.asIdeal ∈ s := (hs _).2 ⟨w.isPrime, hw⟩
      exact Algebra.isUnramifiedAt_iff_of_isDedekindDomain.2 (h _ hmem)
  rw [hU, hncard]
  have hI0 : I ≠ 0 := hI
  constructor
  · intro he
    by_cases h2c : s.card = 2
    · exact Or.inr h2c
    left
    have h1 : s.card = 1 := by omega
    obtain ⟨P, hsP⟩ := Finset.card_eq_one.1 h1
    have hPs : P ∈ s := by simp [hsP]
    have hallM : ∀ Q ∈ M, Q = P := by
      intro Q hQ
      have : Q ∈ s := (hs Q).2 ((hM Q).2 hQ)
      simpa [hsP] using this
    have hcP : M.count P = 1 := by
      rw [← hcount P ((hs P).1 hPs)]
      exact he P hPs
    have hcardM : M.card = 1 := by
      rw [← hcP]
      exact (Multiset.count_eq_card.2 fun x hx => (hallM x hx).symm).symm
    have hMP : M = {P} := by
      rw [Multiset.eq_replicate_of_mem hallM, hcardM, Multiset.replicate_one]
    have hassoc := UniqueFactorizationMonoid.prod_normalizedFactors hI0
    rw [← hMdef, hMP, Multiset.prod_singleton] at hassoc
    rw [← associated_iff_eq.1 hassoc]
    exact ((hs P).1 hPs).1
  · rintro (hp | h2c)
    · intro P hP
      have hirr : Irreducible I := (Ideal.prime_of_isPrime hI hp).irreducible
      have hMI : M = {I} := by
        rw [hMdef, UniqueFactorizationMonoid.normalizedFactors_irreducible hirr, normalize_eq]
      have hPI : P = I := by
        have := (hM P).1 ((hs P).1 hP)
        rw [hMI] at this
        simpa using this
      rw [hcount P ((hs P).1 hP), hMI, hPI, Multiset.count_singleton_self]
    · intro P hP
      by_contra hne
      have hP' := (hs P).1 hP
      haveI : P.IsPrime := hP'.1
      haveI : P.LiesOver v.asIdeal := hP'.2
      have he : 0 < P.ramificationIdx (𝓞 F) := Ideal.ramificationIdx_pos (R := 𝓞 F) P
      have hf : 0 < v.asIdeal.inertiaDeg' P := Ideal.inertiaDeg'_pos v.asIdeal P
      have hge : 2 * 1 ≤ P.ramificationIdx (𝓞 F) * v.asIdeal.inertiaDeg' P :=
        Nat.mul_le_mul (by omega) hf
      have hrest := Finset.card_nsmul_le_sum (s.erase P) _ 1
        (fun Q hQ => hterm Q (Finset.mem_of_mem_erase hQ))
      rw [← Finset.add_sum_erase s _ hP] at hsum
      rw [Finset.card_erase_of_mem hP, h2c] at hrest
      simp only [smul_eq_mul, mul_one] at hrest
      omega

end GlobalTheory
end

section

universe u_1 u_2

namespace GlobalTheory.UnitDenominatorValuation

open NumberField
open scoped nonZeroDivisors

theorem valuation_integer_le_one {E : Type u_1} {Ω : Type u_2} [Field E] [NumberField E]
    [Field Ω] (ι : E →+* Ω) (A : ValuationSubring Ω) (a : 𝓞 E) :
    A.valuation (ι (a : E)) ≤ 1 := by

  have hZ : IsIntegral ℤ (ι (a : E)) := (NumberField.RingOfIntegers.isIntegral_coe a).map ι.toIntAlgHom
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp (hZ.tower_top (A := A))
  rw [← hy]
  exact A.valuation_le_one y

theorem exists_unit_denominator {E : Type u_1} {Ω : Type u_2} [inst : Field E] [NumberField E]
    [inst_2 : Field Ω] (ι : E →+* Ω) (A : ValuationSubring Ω) {x : E}
    (hx : A.valuation (ι x) ≤ 1) :
    ∃ (s : 𝓞 E) (t : 𝓞 E), A.valuation (ι (s : E)) = 1 ∧ (s : E) * x = (t : E) := by
  classical
  by_contra hne
  push Not at hne

  let P : Submodule (𝓞 E) E :=
    { carrier := {u | A.valuation (ι u) < 1}
      add_mem' := fun {u v} hu hv => by
        simp only [Set.mem_ofPred_eq, map_add (f := _)] at hu hv ⊢
        exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hu hv)
      zero_mem' := by simp
      smul_mem' := fun r u hu => by
        simp only [Set.mem_ofPred_eq, Algebra.smul_def, map_mul] at hu ⊢
        calc A.valuation (ι (algebraMap (𝓞 E) E r)) * A.valuation (ι u)
            ≤ 1 * A.valuation (ι u) := mul_le_mul' (valuation_integer_le_one ι A r) le_rfl
          _ < 1 := by rwa [one_mul] }

  let J : FractionalIdeal (𝓞 E)⁰ E := 1 ⊔ FractionalIdeal.spanSingleton _ x
  have h1J : (1 : E) ∈ J := (le_sup_left : (1 : FractionalIdeal (𝓞 E)⁰ E) ≤ J)
    (FractionalIdeal.one_mem_one _)
  have hxJ : x ∈ J := (le_sup_right : FractionalIdeal.spanSingleton _ x ≤ J)
    (FractionalIdeal.mem_spanSingleton_self _ x)
  have hJ : J ≠ 0 := by
    intro h
    rw [h, FractionalIdeal.mem_zero_iff] at h1J
    exact one_ne_zero h1J

  have hJle : ∀ z ∈ (J : Submodule (𝓞 E) E), A.valuation (ι z) ≤ 1 := by
    intro z hz
    rw [FractionalIdeal.coe_sup, Submodule.mem_sup] at hz
    obtain ⟨a, ha, b, hb, rfl⟩ := hz
    obtain ⟨a', rfl⟩ := (FractionalIdeal.mem_one_iff _).mp ha
    obtain ⟨b', rfl⟩ := (FractionalIdeal.mem_spanSingleton _).mp hb
    rw [map_add (f := _)]
    refine le_trans (Valuation.map_add _ _ _) (max_le (valuation_integer_le_one ι A a') ?_)
    rw [Algebra.smul_def, map_mul, map_mul]
    calc A.valuation (ι (algebraMap (𝓞 E) E b')) * A.valuation (ι x) ≤ 1 * 1 :=
          mul_le_mul' (valuation_integer_le_one ι A b') hx
      _ = 1 := one_mul 1

  have hinv : ∀ y ∈ ((J⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E),
      A.valuation (ι y) < 1 := by
    intro y hy
    have hy1 := (FractionalIdeal.mem_inv_iff hJ).mp hy 1 h1J
    have hyx := (FractionalIdeal.mem_inv_iff hJ).mp hy x hxJ
    rw [mul_one] at hy1
    obtain ⟨s, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp hy1
    obtain ⟨t, ht⟩ := (FractionalIdeal.mem_one_iff _).mp hyx
    refine lt_of_le_of_ne (valuation_integer_le_one ι A s) fun h => hne s t h ?_
    exact ht.symm
  have hle : ((J * J⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) ≤ P := by
    rw [FractionalIdeal.coe_mul]
    refine Submodule.mul_le.mpr fun z hz y hy => ?_
    show A.valuation (ι (z * y)) < 1
    rw [map_mul, map_mul]
    calc A.valuation (ι z) * A.valuation (ι y) ≤ 1 * A.valuation (ι y) :=
          mul_le_mul' (hJle z hz) le_rfl
      _ < 1 := by rw [one_mul]; exact hinv y hy
  rw [mul_inv_cancel₀ hJ] at hle
  have h1 : A.valuation (ι 1) < 1 := hle (FractionalIdeal.one_mem_one _)
  simp at h1

end GlobalTheory.UnitDenominatorValuation
end

section

open NumberField IsDedekindDomain

namespace GlobalTheory.UnramDiscr


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.UnramDiscr.mem_of_isIntegral {Ω : Type*} [Field Ω] (A : ValuationSubring Ω)
    {x : Ω} (hx : IsIntegral ℤ x) : x ∈ A := by
  have h : IsIntegral A x := hx.tower_top
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
  exact y.2


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.UnramDiscr.embedding_eq {K Ω : Type*} [Field K] [NumberField K]
    [Field Ω] [CharZero Ω] [IsAlgClosed Ω] (A : ValuationSubring Ω)
    (hd : ¬ A.valuation ((discr K : ℤ) : Ω) < 1)
    (f g : K →+* Ω) (h : ∀ x : 𝓞 K, A.valuation (f x - g x) < 1) : f = g := by
  classical
  by_contra hfg
  set ι := Module.Free.ChooseBasisIndex ℤ (𝓞 K)
  have hcard : Fintype.card ι = Fintype.card (K →ₐ[ℚ] Ω) := by
    rw [AlgHom.card, ← RingOfIntegers.rank K, Module.finrank_eq_card_chooseBasisIndex]
  let e : ι ≃ (K →ₐ[ℚ] Ω) := Fintype.equivOfCardEq hcard
  let b := integralBasis K
  have hint : ∀ (φ : K →+* Ω) (x : 𝓞 K), φ x ∈ A := fun φ x =>
    _root_.GlobalTheory.UnramDiscr.mem_of_isIntegral A
      ((RingOfIntegers.isIntegral_coe x).map φ.toIntAlgHom)
  let N : Matrix ι ι A := Matrix.of fun i j => ⟨e j (b i), by
    rw [integralBasis_apply]; exact hint (e j).toRingHom _⟩
  have hM : ((discr K : ℤ) : Ω) = ((N.det ^ 2 : A) : Ω) := by
    have hdet := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ Ω b e
    rw [← coe_discr] at hdet
    have hN : A.subtype.mapMatrix N = Algebra.embeddingsMatrixReindex ℚ Ω b e := by
      ext i j
      simp [N, Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix]
    rw [map_intCast, ← hN, ← RingHom.map_det] at hdet
    rw [hdet]
    simp
  have hF : f.toRatAlgHom ≠ g.toRatAlgHom := by
    intro hc
    apply hfg
    ext x
    exact congrArg (fun φ : K →ₐ[ℚ] Ω => φ x) hc
  have hres : ((IsLocalRing.residue A).mapMatrix N).det = 0 := by
    apply Matrix.det_zero_of_column_eq (i := e.symm f.toRatAlgHom) (j := e.symm g.toRatAlgHom)
    · simpa using hF
    · intro k
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, N, Matrix.of_apply]
      rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, A.valuation_lt_one_iff]
      simpa [b, integralBasis_apply] using h (RingOfIntegers.basis K k)
  rw [← RingHom.map_det, IsLocalRing.residue_eq_zero_iff] at hres
  apply hd
  rw [hM, ← A.valuation_lt_one_iff]
  exact Ideal.pow_mem_of_mem _ hres 2 (by norm_num)

end GlobalTheory.UnramDiscr
end

section

open IsLocalRing

namespace GlobalTheory

theorem nak_mem_smul_top_pi {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
    (J : Ideal R) (x : ι → R) :
    x ∈ J • (⊤ : Submodule R (ι → R)) ↔ ∀ i, x i ∈ J := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on (p := fun x => ∀ i, x i ∈ J) hx ?_ ?_
    · intro a ha m _ i; exact J.mul_mem_right _ ha
    · intro a b ha hb i; exact J.add_mem (ha i) (hb i)
  · intro hx
    rw [show x = ∑ i, x i • Pi.single i (1 : R) by
      ext j; simp [Finset.sum_apply, Pi.single_apply]]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hx i) Submodule.mem_top

theorem nak_isPrecomplete_pi {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
    (I : Ideal R) [IsPrecomplete I R] : IsPrecomplete I (ι → R) := by
  have key : ∀ k (x : ι → R), x ∈ I ^ k • (⊤ : Submodule R (ι → R)) ↔
      ∀ i, x i ∈ I ^ k • (⊤ : Submodule R R) := by
    intro k x
    rw [nak_mem_smul_top_pi]
    simp only [smul_eq_mul, Ideal.mul_top]
  refine ⟨fun f hf => ?_⟩
  have hc : ∀ i, ∃ l : R, ∀ n, f n i ≡ l [SMOD (I ^ n • ⊤ : Submodule R R)] := by
    intro i
    refine IsPrecomplete.prec' (fun n => f n i) fun {m n} hmn => ?_
    have := (hf hmn)
    rw [SModEq.sub_mem] at this ⊢
    exact (key m _).1 this i
  choose l hl using hc
  refine ⟨l, fun n => ?_⟩
  rw [SModEq.sub_mem, key]
  intro i
  exact SModEq.sub_mem.1 (hl i n)

theorem finite_of_finite_quot_map_of_isPrecomplete :
    ∀ (O A : Type) [CommRing O] [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Algebra O A]
      (J : Ideal O) [IsPrecomplete J O], J.map (algebraMap O A) ≠ ⊤ →
      Module.Finite O (A ⧸ J.map (algebraMap O A)) → Module.Finite O A := by
  intro O A _ _ _ _ _ J _ hJ hfin
  have hsm : ∀ n : ℕ, (J ^ n • (⊤ : Submodule O A)) =
      Submodule.restrictScalars O ((J.map (algebraMap O A)) ^ n) := by
    intro n
    rw [Ideal.smul_top_eq_map, Ideal.map_pow]
  have hH : IsHausdorff J A := by
    refine ⟨fun x hx => ?_⟩
    have : x ∈ ⨅ n : ℕ, (J.map (algebraMap O A)) ^ n := by
      rw [Submodule.mem_iInf]
      intro n
      have h1 := SModEq.sub_mem.1 (hx n)
      rw [sub_zero, hsm n] at h1
      exact h1
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ hJ] at this
    exact this
  set I := J.map (algebraMap O A) with hI
  obtain ⟨r, s, hs⟩ := Module.Finite.exists_fin (R := O) (M := A ⧸ I)
  choose s' hs' using fun i => Ideal.Quotient.mk_surjective (s i)
  have : IsPrecomplete J (Fin r → O) := nak_isPrecomplete_pi _
  have hsurj : Function.Surjective ((J • (⊤ : Submodule O A)).mkQ ∘ₗ
      Fintype.linearCombination O s') := by
    intro y
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have hx : (Ideal.Quotient.mk I x) ∈ Submodule.span O (Set.range s) := by
      rw [hs]; exact Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 hx
    refine ⟨c, ?_⟩
    have hq : Ideal.Quotient.mk I (Fintype.linearCombination O s' c) = Ideal.Quotient.mk I x := by

      rw [Fintype.linearCombination_apply, map_sum, ← hc]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, map_mul, ← hs' i, Algebra.smul_def]
      rfl
    have hmem : Fintype.linearCombination O s' c - x ∈ I := by
      rw [← Ideal.Quotient.eq]; exact hq
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply]
    rw [Submodule.Quotient.eq]
    have h1 := hsm 1
    simp only [pow_one] at h1
    rw [h1]
    exact hmem
  exact Module.Finite.of_surjective _ (surjective_of_mkQ_comp_surjective hsurj)

end GlobalTheory
end

section

namespace GlobalTheory

theorem exists_isPrimitiveRoot_of_injective_character (K : Type) [Field K] (p : ℕ) (hp : p.Prime)
    (om : (ZMod p)ˣ →* Kˣ) (hom : Function.Injective om) :
    ∃ ζ : K, IsPrimitiveRoot ζ (p - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod p)ˣ)
  rw [Nat.card_eq_fintype_card, ZMod.card_units] at hg
  refine ⟨(om g : K), ?_⟩
  rw [IsPrimitiveRoot.coe_units_iff, ← hg, ← orderOf_injective om hom g]
  exact IsPrimitiveRoot.orderOf _

end GlobalTheory
end

section

namespace GlobalTheory

theorem charZero_wittVector_of_field (p : ℕ) [hp : Fact p.Prime] (K : Type) [Field K] [CharP K p] :
    CharZero (WittVector p K) := by
  obtain ⟨l, hl⟩ := CharP.exists (WittVector p K)
  rcases CharP.char_is_prime_or_zero (WittVector p K) l with h | h
  · exfalso
    have h1 : ((l : ℕ) : WittVector p K) = 0 := CharP.cast_eq_zero _ l
    have h2 : ((l : ℕ) : K) = 0 := by
      have := congrArg (WittVector.constantCoeff : WittVector p K →+* K) h1
      rwa [map_natCast, map_zero] at this
    have h3 : p ∣ l := (CharP.cast_eq_zero_iff K p l).1 h2
    have h4 : p = l := (Nat.prime_dvd_prime_iff_eq hp.out h).1 h3
    subst h4
    exact WittVector.p_nonzero p K h1
  · subst h
    exact CharP.charP_to_charZero _

end GlobalTheory
end
