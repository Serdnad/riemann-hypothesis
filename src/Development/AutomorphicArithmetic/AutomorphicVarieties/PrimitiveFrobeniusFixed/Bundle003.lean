module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
public import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.ExistsBinomialExpansionModSq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
public import Mathlib.RingTheory.DedekindDomain.Factorization

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

private theorem cyc_hom_ext {K Ω : Type} [Field K] [CharZero K] [Field Ω] [CharZero Ω] (N : ℕ) [NeZero N]
    [IsCyclotomicExtension {N} ℚ K] (f g : K →+* Ω) (h : ∀ x : K, x ^ N = 1 → f x = g x) : f = g := by
  have key : f.toRatAlgHom = g.toRatAlgHom := by
    apply AlgHom.ext
    intro x
    have hx := IsCyclotomicExtension.adjoin_roots (S := {N}) (A := ℚ) x
    induction hx using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨n, hn, -, hy1⟩ := hy
      rw [Set.mem_singleton_iff] at hn
      rw [hn] at hy1
      exact h y hy1
    | algebraMap c => rw [AlgHom.commutes, AlgHom.commutes]
    | add a b _ _ ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
    | mul a b _ _ ha hb => rw [map_mul, map_mul, ha, hb]
  ext x
  exact congrArg (fun φ : K →ₐ[ℚ] Ω => φ x) key

private theorem card_gal (M q : ℕ) [NeZero M] [NeZero (q * M)] (K K' : Type) [Field K] [NumberField K]
    [IsCyclotomicExtension {M} ℚ K] [Field K'] [NumberField K'] [IsCyclotomicExtension {q * M} ℚ K'] [Algebra K K']
    [IsGalois K K'] (hq : q.Prime) (hc : q.Coprime M) : Nat.card (K' ≃ₐ[K] K') = q - 1 := by
  haveI : IsScalarTower ℚ K K' := inferInstance
  haveI : FiniteDimensional K K' := Module.Finite.of_restrictScalars_finite ℚ K K'
  have h1 := IsCyclotomicExtension.finrank K' (Polynomial.cyclotomic.irreducible_rat (NeZero.pos (q * M)))
  have h2 := IsCyclotomicExtension.finrank K (Polynomial.cyclotomic.irreducible_rat (NeZero.pos M))
  rw [IsGalois.card_aut_eq_finrank]
  have htow := Module.finrank_mul_finrank ℚ K K'
  rw [h1, h2, Nat.totient_mul hc, Nat.totient_prime hq] at htow
  have hM : 0 < M.totient := Nat.totient_pos.mpr (NeZero.pos M)
  exact Nat.eq_of_mul_eq_mul_left hM (by rw [htow, mul_comm])

theorem UpperTheory.norm_cyclotomic_prime_layer_eq_nrm_generator :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (M q : ℕ) [NeZero M] [NeZero (q * M)] (K K' : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] [Field K'] [NumberField K'] [IsCyclotomicExtension {q * M} ℚ K'] [Algebra K K'] (ι' : K' →+* Ω), q.Prime → q.Coprime M → ∀ τ ∈ fixMu ℚ Ω M, GenAt q τ → ∀ x : K', nrm q τ (ι' x) = ι' (algebraMap K K' (Algebra.norm K x)) := by
  intro Ω _ _ M q _ _ K K' _ _ _ _ _ _ _ ι' hq hc τ hτ hgen x
  classical
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : IsScalarTower ℚ K K' := inferInstance
  haveI : FiniteDimensional K K' := Module.Finite.of_restrictScalars_finite ℚ K K'
  haveI : IsGalois ℚ K' := IsCyclotomicExtension.isGalois {q * M} ℚ K'
  haveI : IsGalois K K' := IsGalois.tower_top_of_isGalois ℚ K K'
  obtain ⟨b, hbgen, hb⟩ := hgen
  have hb' : ∀ y : Ω, y ^ q = 1 → τ y = y ^ (b : ZMod q).val := hb
  have hτM : ∀ y : Ω, y ^ M = 1 → τ y = y := hτ
  have hpm : ∀ {R : Type} [Monoid R] (y : R) (N m n : ℕ), y ^ N = 1 → m ≡ n [MOD N] → y ^ m = y ^ n := by
    intro R _ y N m n hy h
    rw [← Nat.mod_add_div m N, ← Nat.mod_add_div n N, show m % N = n % N from h, pow_add, pow_add,
      pow_mul, pow_mul, hy, one_pow, one_pow]
  obtain ⟨A, hA1, hA0⟩ : ∃ A, A ≡ 1 [MOD q] ∧ A ≡ 0 [MOD M] :=
    ⟨(Nat.chineseRemainder hc 1 0).1, (Nat.chineseRemainder hc 1 0).2.1, (Nat.chineseRemainder hc 1 0).2.2⟩
  obtain ⟨B, hB0, hB1⟩ : ∃ B, B ≡ 0 [MOD q] ∧ B ≡ 1 [MOD M] :=
    ⟨(Nat.chineseRemainder hc 0 1).1, (Nat.chineseRemainder hc 0 1).2.1, (Nat.chineseRemainder hc 0 1).2.2⟩
  obtain ⟨e, he⟩ : ∃ e, e = A * (b : ZMod q).val + B := ⟨_, rfl⟩
  have he_q : e ≡ (b : ZMod q).val [MOD q] := by
    have h := (hA1.mul_right (b : ZMod q).val).add hB0
    rwa [one_mul, add_zero, ← he] at h
  have he_M : e ≡ 1 [MOD M] := by
    have h := (hA0.mul_right (b : ZMod q).val).add hB1
    rwa [zero_mul, zero_add, ← he] at h
  have hτe : ∀ y : Ω, y ^ (q * M) = 1 → τ y = y ^ e := by
    intro y hy
    have hAB : A + B ≡ 1 [MOD q * M] := (Nat.modEq_and_modEq_iff_modEq_mul hc).mp
      ⟨by simpa using hA1.add hB0, by simpa using hA0.add hB1⟩
    obtain ⟨cA, hcA⟩ := (Nat.modEq_zero_iff_dvd.mp hA0)
    obtain ⟨cB, hcB⟩ := (Nat.modEq_zero_iff_dvd.mp hB0)
    have hyA : (y ^ A) ^ q = 1 := by
      rw [← pow_mul, show A * q = q * M * cA by rw [hcA]; ring, pow_mul, hy, one_pow]
    have hyB : (y ^ B) ^ M = 1 := by
      rw [← pow_mul, show B * M = q * M * cB by rw [hcB]; ring, pow_mul, hy, one_pow]
    calc τ y = τ (y ^ A * y ^ B) := by rw [← pow_add, hpm y (q * M) (A + B) 1 hy hAB, pow_one]
      _ = (y ^ A) ^ (b : ZMod q).val * y ^ B := by rw [map_mul, hb' _ hyA, hτM _ hyB]
      _ = y ^ e := by rw [he, ← pow_mul, ← pow_add]
  have hζ := IsCyclotomicExtension.zeta_spec (q * M) ℚ K'
  have he_cop : e.Coprime (q * M) := by
    apply Nat.Coprime.mul_right
    · exact he_q.gcd_eq.trans (ZMod.val_coe_unit_coprime b)
    · exact he_M.gcd_eq.trans (Nat.gcd_one_left M)
  have hμ := hζ.pow_of_coprime e he_cop
  have hirr := Polynomial.cyclotomic.irreducible_rat (NeZero.pos (q * M))
  have hσ0ζ := IsCyclotomicExtension.fromZetaAut_spec hμ hirr
  have hσ0 : ∀ z : K', z ^ (q * M) = 1 → IsCyclotomicExtension.fromZetaAut hμ hirr z = z ^ e := by
    intro z hz
    obtain ⟨j, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hz
    rw [map_pow, hσ0ζ, ← pow_mul, ← pow_mul, mul_comm e j]
  have hσ0K : ∀ y : K, IsCyclotomicExtension.fromZetaAut hμ hirr (algebraMap K K' y) = algebraMap K K' y := by
    have h := cyc_hom_ext M ((IsCyclotomicExtension.fromZetaAut hμ hirr).toRingEquiv.toRingHom.comp (algebraMap K K'))
      (algebraMap K K') (fun y hy => by
        show IsCyclotomicExtension.fromZetaAut hμ hirr (algebraMap K K' y) = algebraMap K K' y
        have h1 : (algebraMap K K' y) ^ M = 1 := by rw [← map_pow, hy, map_one]
        rw [hσ0 _ (by rw [mul_comm, pow_mul, h1, one_pow]), hpm _ M e 1 h1 he_M, pow_one])
    exact fun y => RingHom.congr_fun h y
  let σ1 : K' ≃ₐ[K] K' := AlgEquiv.ofRingEquiv (f := (IsCyclotomicExtension.fromZetaAut hμ hirr).toRingEquiv) hσ0K
  have hσ1 : ∀ z : K', z ^ (q * M) = 1 → σ1 z = z ^ e := fun z hz => hσ0 z hz
  have hcomm : ∀ z : K', τ (ι' z) = ι' (σ1 z) := by
    have h := cyc_hom_ext (q * M) ((τ : Ω ≃ₐ[ℚ] Ω).toRingEquiv.toRingHom.comp ι') (ι'.comp σ1.toRingEquiv.toRingHom)
      (fun z hz => by
        show τ (ι' z) = ι' (σ1 z)
        rw [hσ1 z hz, map_pow, hτe _ (by rw [← map_pow, hz, map_one])])
    exact fun z => RingHom.congr_fun h z
  have hcommi : ∀ i : ℕ, ∀ z : K', (τ ^ i) (ι' z) = ι' ((σ1 ^ i) z) := by
    intro i
    induction i with
    | zero => intro z; rw [pow_zero, pow_zero, AlgEquiv.one_apply, AlgEquiv.one_apply]
    | succ i ih => intro z; rw [pow_succ, pow_succ, AlgEquiv.mul_apply, AlgEquiv.mul_apply, hcomm, ih]
  have hζq : IsPrimitiveRoot (IsCyclotomicExtension.zeta (q * M) ℚ K' ^ M) q := by
    have h := hζ.pow_of_dvd (NeZero.ne M) (dvd_mul_left M q)
    rwa [Nat.mul_div_cancel q (NeZero.pos M)] at h
  have hζq1 : (IsCyclotomicExtension.zeta (q * M) ℚ K' ^ M) ^ (q * M) = 1 := by
    rw [pow_mul, hζq.pow_eq_one, one_pow]
  have hσpow : ∀ i : ℕ, (σ1 ^ i) (IsCyclotomicExtension.zeta (q * M) ℚ K' ^ M)
      = (IsCyclotomicExtension.zeta (q * M) ℚ K' ^ M) ^ (e ^ i) := by
    intro i
    induction i with
    | zero => rw [pow_zero, pow_zero, pow_one, AlgEquiv.one_apply]
    | succ i ih => rw [pow_succ, AlgEquiv.mul_apply, hσ1 _ hζq1, map_pow, ih, ← pow_mul, pow_succ]
  have horder : orderOf b = q - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hbgen, Nat.card_eq_fintype_card, ZMod.card_units]
  have hinj : ∀ i ∈ Finset.range (q - 1), ∀ j ∈ Finset.range (q - 1), σ1 ^ i = σ1 ^ j → i = j := by
    intro i hi j hj hij
    have h1 : (IsCyclotomicExtension.zeta (q * M) ℚ K' ^ M) ^ (e ^ i) = (IsCyclotomicExtension.zeta (q * M) ℚ K' ^ M) ^ (e ^ j) := by
      rw [← hσpow, ← hσpow, hij]
    rw [hpm _ q (e ^ i) (e ^ i % q) hζq.pow_eq_one (Nat.mod_modEq _ _).symm,
      hpm _ q (e ^ j) (e ^ j % q) hζq.pow_eq_one (Nat.mod_modEq _ _).symm] at h1
    have h2 : e ^ i ≡ e ^ j [MOD q] := hζq.pow_inj (Nat.mod_lt _ hq.pos) (Nat.mod_lt _ hq.pos) h1
    have h3 : ((e : ZMod q)) = (b : ZMod q) := by
      rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr he_q, ZMod.natCast_zmod_val]
    have h4 : (b : ZMod q) ^ i = (b : ZMod q) ^ j := by
      rw [← h3, ← Nat.cast_pow, ← Nat.cast_pow, (ZMod.natCast_eq_natCast_iff _ _ _).mpr h2]
    have h5 : b ^ i = b ^ j := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, h4])
    have h6 := pow_eq_pow_iff_modEq.mp h5
    rw [horder] at h6
    have h7 : i % (q - 1) = j % (q - 1) := h6
    rwa [Nat.mod_eq_of_lt (Finset.mem_range.mp hi), Nat.mod_eq_of_lt (Finset.mem_range.mp hj)] at h7
  have himg : (Finset.range (q - 1)).image (fun i => σ1 ^ i) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn (fun i hi j hj h => hinj i hi j hj h), Finset.card_range,
      ← Nat.card_eq_fintype_card, card_gal M q K K' hq hc]
  show ∏ i ∈ Finset.range (q - 1), (τ ^ i) (ι' x) = _
  rw [Algebra.norm_eq_prod_automorphisms, map_prod, ← himg, Finset.prod_image (fun i hi j hj h => hinj i hi j hj h)]
  exact Finset.prod_congr rfl (fun i _ => hcommi i x)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

private theorem val_count_int {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) (ha : a ≠ 0) :
    v.valuation K (a : K) = WithZero.exp (-FractionalIdeal.count K v
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K))) := by
  have h1 : v.valuation K (a : K) = v.intValuation a := v.valuation_of_algebraMap a
  have h2 : FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K)
      = ((Ideal.span {a} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) :=
    (FractionalIdeal.coeIdeal_span_singleton a).symm
  rw [h1, h2, v.intValuation_if_neg ha, FractionalIdeal.count_coe K v (by simpa using ha)]

private theorem val_count {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (x : K) (hx : x ≠ 0) :
    v.valuation K x = WithZero.exp (-FractionalIdeal.count K v
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ x)) := by
  obtain ⟨a, b, hb, e⟩ := IsFractionRing.div_surjective (𝓞 K) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : (b : K) ≠ 0 := by exact_mod_cast hb0
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hx
    simp [← e]
  have e' : x * (b : K) = (a : K) := by
    rw [← e]; exact div_mul_cancel₀ _ hbK
  have h1 := val_count_int v a ha0
  have h2 := val_count_int v b hb0
  rw [← e', map_mul, h2, ← FractionalIdeal.spanSingleton_mul_spanSingleton,
    FractionalIdeal.count_mul K v (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx)
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hbK), neg_add, WithZero.exp_add] at h1
  exact mul_right_cancel₀ WithZero.exp_ne_zero h1

theorem UpperTheory.valuation_kummerElement_eq_one_of_not_over :
    ∀ (M : ℕ) [NeZero M] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] (b r : ℕ) (v w : HeightOneSpectrum (𝓞 K)) (X : K), IsX M K b v.asIdeal X → (r : 𝓞 K) ∈ v.asIdeal → (r : 𝓞 K) ∉ w.asIdeal → w.valuation K X = 1 := by
  intro M _ K _ _ _ b r v w X hX hv hw
  have hX0 : X ≠ 0 := left_ne_zero_of_mul_eq_one hX.1
  let P : (ZMod M)ˣ → HeightOneSpectrum (𝓞 K) := fun t =>
    HeightOneSpectrum.comap (sgO M K t : 𝓞 K →+* 𝓞 K) (sgO M K t).surjective v
  have hP : ∀ t, (P t).asIdeal = conjI M K v.asIdeal t := fun t => rfl
  have hne : ∀ t, P t ≠ w := by
    intro t h
    apply hw
    rw [← h, hP, mem_conjI, map_natCast]
    exact hv
  rw [val_count w X hX0, hX.2, FractionalIdeal.count_prod]
  · rw [Finset.sum_eq_zero, neg_zero, WithZero.exp_zero]
    intro t _
    rw [FractionalIdeal.count_zpow, ← hP, FractionalIdeal.count_maximal_coprime K w (hne t), mul_zero]
  · intro t _
    apply zpow_ne_zero
    rw [← hP]
    exact FractionalIdeal.coeIdeal_ne_zero.mpr (P t).ne_bot
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

private theorem zSumP_key {Ω : Type} [Field Ω] [Algebra ℚ Ω] (F : ℕ) [NeZero F] (t d : (ZMod F)ˣ) (g h k : G ℚ Ω)
    (hg : Lifts F t g) (hh : Lifts F d h) (hk : Lifts F (t * d) k) : k⁻¹ * (g * h) ∈ fixMu ℚ Ω F := by
  have hg' : ∀ x : Ω, x ^ F = 1 → g x = x ^ (t : ZMod F).val := hg
  have hh' : ∀ x : Ω, x ^ F = 1 → h x = x ^ (d : ZMod F).val := hh
  have hk' : ∀ x : Ω, x ^ F = 1 → k x = x ^ ((t * d : (ZMod F)ˣ) : ZMod F).val := hk
  show ∀ x : Ω, x ^ F = 1 → (k⁻¹ * (g * h)) x = x
  intro x hx
  have hgh : (g * h) x = k x := by
    rw [AlgEquiv.mul_apply, hh' x hx, map_pow, hg' x hx, ← pow_mul, hk' x hx, Units.val_mul, ZMod.val_mul]
    conv_lhs => rw [← Nat.mod_add_div ((t : ZMod F).val * (d : ZMod F).val) F]
    rw [pow_add, pow_mul, hx, one_pow, mul_one]
  rw [AlgEquiv.mul_apply, hgh, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]

theorem UpperTheory.V.ML.zSumP :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (O : Type) [CommRing O] (F a : ℕ) [NeZero F] (I : O) (α : G ℚ Ω →* Oˣ), (∀ g ∈ fixMu ℚ Ω F, I ∣ (α g : O) - 1) → ∀ σ : (ZMod F)ˣ → G ℚ Ω, (∀ t, Lifts F t (σ t)) →
    ∀ (k : (ZMod F)ˣ → ℤ), (∀ (d : (ZMod F)ˣ) (δ : G ℚ Ω), Lifts F d δ → I ∣ zSum α σ (fun t => k (t * d) - a * k t) - ((α δ : O) - a) * zSum α σ k) ∧
    ∀ n : ℤ, zSum α σ (fun t => n * k t) = n * zSum α σ k := by
  intro Ω _ _ _ O _ F a _ I α hI σ hσ k
  refine ⟨fun d δ hδ => ?_, fun n => ?_⟩
  · have hre : ∑ t, (k t : O) * (((α (σ t))⁻¹ : Oˣ) : O) = ∑ t, (k (t * d) : O) * (((α (σ (t * d)))⁻¹ : Oˣ) : O) :=
      (Fintype.sum_equiv (Equiv.mulRight d) _ _ (fun t => rfl)).symm
    have h1 : zSum α σ (fun t => k (t * d) - a * k t) - ((α δ : O) - a) * zSum α σ k
        = ∑ t, (k (t * d) : O) * (((α (σ t))⁻¹ : Oˣ) : O) - (α δ : O) * ∑ t, (k t : O) * (((α (σ t))⁻¹ : Oˣ) : O) := by
      simp only [zSum, Int.cast_sub, Int.cast_mul, Int.cast_natCast, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
      ring
    have h2 : ∑ t, (k (t * d) : O) * (((α (σ t))⁻¹ : Oˣ) : O) - (α δ : O) * ∑ t, (k (t * d) : O) * (((α (σ (t * d)))⁻¹ : Oˣ) : O)
        = ∑ t, (k (t * d) : O) * (((α (σ t))⁻¹ : Oˣ) : O) * (1 - (α ((σ (t * d))⁻¹ * (σ t * δ)) : O)) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun t _ => ?_
      have hu : (((α (σ t))⁻¹ : Oˣ) : O) * (α (σ t) : O) = 1 := Units.inv_mul _
      simp only [map_mul, map_inv, Units.val_mul]
      linear_combination ((α δ : O) * (k (t * d) : O) * (((α (σ (t * d)))⁻¹ : Oˣ) : O)) * hu
    rw [h1, hre, h2]
    refine Finset.dvd_sum fun t _ => Dvd.dvd.mul_left ?_ _
    exact dvd_sub_comm.mp (hI _ (zSumP_key F t d (σ t) δ (σ (t * d)) (hσ t) hδ (hσ (t * d))))
  · simp only [zSum, Int.cast_mul, mul_assoc, Finset.mul_sum]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

theorem UpperTheory.admissible_prime_not_dvd_orderOf_and_not_dvd_level :
    ∀ (l F r d : ℕ), F ≠ 0 → l.Prime → r.Prime → r ≡ 1 [MOD F] → ML.admitted l F r d → ¬ l ∣ orderOf (r : ZMod (F * d)) ∧ ¬ r ∣ F * d := by
  intro l F r d _ hl hr hrF hd
  obtain ⟨hsq, hq⟩ := hd
  have hone : ∀ p : ℕ, p.Prime → p ≡ 1 [MOD F] → ¬ p ∣ F := fun p hp h hpF => by
    have h1 : p ≡ 1 [MOD p] := h.of_dvd hpF
    have h2 : p ∣ 1 := (h1.dvd_iff dvd_rfl).1 dvd_rfl
    exact hp.one_lt.ne' (Nat.dvd_one.1 h2)
  refine ⟨?_, ?_⟩
  · set n := ∏ q ∈ d.primeFactors, orderOf (r : ZMod q) with hn
    have hln : ¬ l ∣ n := by
      intro h
      obtain ⟨q, hqm, hlq⟩ := (Prime.dvd_finsetProd_iff hl.prime _).1 h
      exact (hq q (Nat.prime_of_mem_primeFactors hqm) (Nat.dvd_of_mem_primeFactors hqm)).2.2.2 hlq
    have hcop : Nat.Coprime F d := by
      apply Nat.coprime_of_dvd
      intro k hk hkF hkd
      exact hone k hk (hq k hk hkd).2.1 hkF
    have hpos : 1 ≤ r ^ n := Nat.one_le_pow _ _ hr.pos
    have hF : r ^ n ≡ 1 [MOD F] := by simpa using hrF.pow n
    have hD : r ^ n ≡ 1 [MOD d] := by
      have h1 : ∏ q ∈ d.primeFactors, q ∣ r ^ n - 1 := by
        apply Finset.prod_primes_dvd
        · intro a ha
          exact (Nat.prime_of_mem_primeFactors ha).prime
        · intro a ha
          have h2 : (r : ZMod a) ^ n = 1 :=
            orderOf_dvd_iff_pow_eq_one.1 (Finset.dvd_prod_of_mem (fun q : ℕ => orderOf (r : ZMod q)) ha)
          have h3 : r ^ n ≡ 1 [MOD a] := by
            rw [← ZMod.natCast_eq_natCast_iff]
            simpa using h2
          exact (Nat.modEq_iff_dvd' hpos).1 h3.symm
      rw [Nat.prod_primeFactors_of_squarefree hsq] at h1
      exact ((Nat.modEq_iff_dvd' hpos).2 h1).symm
    have hFD : r ^ n ≡ 1 [MOD F * d] := (Nat.modEq_and_modEq_iff_modEq_mul hcop).1 ⟨hF, hD⟩
    have h4 : (r : ZMod (F * d)) ^ n = 1 := by
      have := (ZMod.natCast_eq_natCast_iff _ _ _).2 hFD
      simpa using this
    exact fun h => hln (h.trans (orderOf_dvd_of_pow_eq_one h4))
  · intro h
    rcases (Nat.Prime.dvd_mul hr).1 h with h | h
    · exact hone r hr hrF h
    · exact (hq r hr h).2.2.1 rfl
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

private theorem th_eq (F b : ℕ) [NeZero F] (t : ZMod F) (ht : t ≠ 0) (hy : (b : ZMod F) * t ≠ 0) :
    (b : ℤ) * (t.val : ℤ) = (((b : ZMod F) * t).val : ℤ) + F * ((t.val * b / F : ℕ) : ℤ) ∧
    th F b t = 2 * ((t.val * b / F : ℕ) : ℤ) - ((b : ℤ) - 1) := by
  have hF : 0 < F := Nat.pos_of_ne_zero (NeZero.ne F)
  have h1 : ((b : ZMod F) * t).val = t.val * b % F := by
    rw [ZMod.val_mul, ZMod.val_natCast, Nat.mod_mul_mod, mul_comm]
  have h0 : 0 < ((b : ZMod F) * t).val := Nat.pos_of_ne_zero fun h => hy ((ZMod.val_eq_zero _).1 h)
  have hlt := ZMod.val_lt ((b : ZMod F) * t)
  have h2 : F * (t.val * b / F) + t.val * b % F = t.val * b := Nat.div_add_mod _ _
  have h3 : F * ((-t).val * b / F) + (-t).val * b % F = (-t).val * b := Nat.div_add_mod _ _
  have h4 : (-t).val * b % F < F := Nat.mod_lt _ hF
  have h5 : (-t).val + t.val = F := by
    rw [ZMod.neg_val, if_neg ht]
    have := ZMod.val_lt t
    omega
  rw [← h1] at h2
  rw [th]
  generalize ((b : ZMod F) * t).val = y at *
  generalize (-t).val * b % F = r at *
  generalize (-t).val * b / F = j' at *
  generalize t.val * b / F = j at *
  generalize (-t).val = s at *
  generalize t.val = u at *
  zify at h0 hlt h2 h3 h4 h5 hF
  have hr : (0 : ℤ) ≤ r := by positivity
  have h6 : (F : ℤ) * (b - j - j') = y + r := by linear_combination -h2 - h3 - b * h5
  have h7 : (0 : ℤ) < b - j - j' := by
    by_contra h
    nlinarith
  have h8 : (b : ℤ) - j - j' < 2 := by
    by_contra h
    nlinarith
  exact ⟨by linear_combination -h2, by omega⟩

private theorem pointwise (F e b : ℕ) [NeZero F] (t : ZMod F) (ht : t ≠ 0) (hy : (b : ZMod F) * t ≠ 0) :
    ∃ z : ℤ, (Stk.dk (e + 1) : ℚ) * ((b : ℚ) ^ e * (th F b t * (t.val : ℚ) ^ e) +
      2 * (Bern.bcoef F (e + 1) ((b : ZMod F) * t).val / (e + 1) -
        (b : ℚ) ^ (e + 1) * (Bern.bcoef F (e + 1) t.val / (e + 1)))) = F * z := by
  have hM0 : 0 < F := Nat.pos_of_ne_zero (NeZero.ne F)
  have hM : (F : ℚ) ≠ 0 := by exact_mod_cast hM0.ne'
  have hD : (primorial (e + 1 + 1) : ℚ) ≠ 0 := by exact_mod_cast (primorial_pos _).ne'
  have hk : (e : ℚ) + 1 ≠ 0 := by positivity
  obtain ⟨h1, h2⟩ := th_eq F b t ht hy
  obtain ⟨z1, hz1⟩ := Stk.stickelbergerBernoulliCoeff_expansion_mod_denominator F e ((b : ZMod F) * t).val hM0
  obtain ⟨z2, hz2⟩ := Stk.stickelbergerBernoulliCoeff_expansion_mod_denominator F e t.val hM0
  rw [h2]
  generalize ((b : ZMod F) * t).val = y at *
  generalize t.val * b / F = j at *
  generalize t.val = u at *
  obtain ⟨⟨z3, hz3⟩, ⟨w, hw⟩⟩ := Stk.exists_binomial_expansion_mod_sq ((b : ℤ) * u) (-(j : ℤ)) F e
  have h3 : (b : ℤ) * u + F * (-(j : ℤ)) = y := by linear_combination h1
  rw [h3] at hz3 hw
  have q3 : (y : ℚ) ^ (e + 1) =
      ((b : ℚ) * u) ^ (e + 1) + ((e : ℚ) + 1) * ((b : ℚ) * u) ^ e * ((F : ℚ) * (-(j : ℚ))) + (F : ℚ) ^ 2 * z3 := by
    exact_mod_cast hz3
  have qw : (y : ℚ) ^ e = ((b : ℚ) * u) ^ e + (F : ℚ) * w := by
    exact_mod_cast hw
  have hdk : (Stk.dk (e + 1) : ℚ) = 2 * ((e : ℚ) + 1) * (primorial (e + 1 + 1) : ℚ) := by
    rw [Stk.dk]; push_cast; ring
  refine ⟨4 * z1 - 4 * (b : ℤ) ^ (e + 1) * z2 + 4 * (primorial (e + 1 + 1) : ℤ) * z3
    - 2 * ((e : ℤ) + 1) * (primorial (e + 1 + 1) : ℤ) * w, ?_⟩
  rw [Nat.cast_add, Nat.cast_one] at hz1 hz2
  rw [hz1, hz2, q3, qw, hdk]
  push_cast
  field_simp
  ring

private theorem genB_units {R : Type} [CommRing R] [Algebra ℚ R] {F : ℕ} [NeZero F] (hF : 1 < F) (k : ℕ)
    (χ : DirichletCharacter R F) :
    Bern.genB k (χ : ZMod F → R) = ∑ t : (ZMod F)ˣ, χ t * algebraMap ℚ R (Bern.bcoef F k (t : ZMod F).val) := by
  haveI : Fact (1 < F) := ⟨hF⟩
  have h1 : Bern.genB k (χ : ZMod F → R) = ∑ t : ZMod F, χ t * algebraMap ℚ R (Bern.bcoef F k t.val) := by
    rw [← Bern.b_sumicc (fun x : ZMod F => χ x * algebraMap ℚ R (Bern.bcoef F k x.val)), Bern.genB]
    refine Finset.sum_congr rfl fun a ha => ?_
    rcases (Finset.mem_Icc.1 ha).2.lt_or_eq with h | h
    · rw [ZMod.val_cast_of_lt h]
    · rw [h, ZMod.natCast_self, χ.map_nonunit not_isUnit_zero, zero_mul, zero_mul]
  rw [h1]
  symm
  refine Finset.sum_of_injOn (fun t : (ZMod F)ˣ => (t : ZMod F)) (fun a _ b _ h => Units.ext h)
    (fun _ _ => Finset.mem_univ _) ?_ (fun _ _ => rfl)
  intro x _ hx
  rw [χ.map_nonunit, zero_mul]
  rintro ⟨u, rfl⟩
  exact hx ⟨u, by simp, rfl⟩

private theorem norm_chi {R : Type} [NormedField R] {F : ℕ} [NeZero F] (χ : DirichletCharacter R F) (t : (ZMod F)ˣ) :
    ‖χ t‖ = 1 := by
  have h : χ t ^ Fintype.card (ZMod F)ˣ = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one]
  have h2 : ‖χ t‖ ^ Fintype.card (ZMod F)ˣ = 1 := by rw [← norm_pow, h, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) Fintype.card_ne_zero).1 h2

theorem UpperTheory.V.ML.zCong :
    ∀ (l : ℕ) [Fact l.Prime] (F m e b : ℕ) [NeZero F], l ^ m ∣ F → 1 ≤ m → 1 ≤ e → b.Coprime F → ∀ χ : DirichletCharacter (PadicAlgCl l) F, χ (-1) = (-1) ^ (e + 1) →
    ‖(UpperTheory.V.Stk.dk (e + 1) : PadicAlgCl l) * ((b : PadicAlgCl l) ^ e * χ b * ∑ t : (ZMod F)ˣ, (th F b t : PadicAlgCl l) * (((t : ZMod F).val : PadicAlgCl l) ^ e * χ t) -
      2 * (χ b * (b : PadicAlgCl l) ^ (e + 1) - 1) * (UpperTheory.V.Bern.genB (e + 1) (χ : ZMod F → PadicAlgCl l) / (e + 1)))‖ ≤ ‖(l : PadicAlgCl l) ^ m‖ := by
  intro l hl F m e b _ hm h1m _ hb χ _
  have hF : 1 < F := lt_of_lt_of_le (Nat.one_lt_pow (by omega) hl.out.one_lt)
    (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne F)) hm)
  haveI : Fact (1 < F) := ⟨hF⟩
  set u : (ZMod F)ˣ := ZMod.unitOfCoprime b hb with hu
  have hub : (u : ZMod F) = b := ZMod.coe_unitOfCoprime b hb
  have g1 := genB_units hF (e + 1) χ
  have g2 : Bern.genB (e + 1) (χ : ZMod F → PadicAlgCl l) = ∑ t : (ZMod F)ˣ, χ ((b : ZMod F) * t) *
      algebraMap ℚ (PadicAlgCl l) (Bern.bcoef F (e + 1) ((b : ZMod F) * t).val) := by
    rw [g1, ← hub]
    exact (Equiv.sum_comp (Equiv.mulLeft u) (fun t : (ZMod F)ˣ => χ t *
      algebraMap ℚ (PadicAlgCl l) (Bern.bcoef F (e + 1) (t : ZMod F).val))).symm
  have hp : ∀ t : (ZMod F)ˣ, _ := fun t => pointwise F e b (t : ZMod F) t.ne_zero (by
    rw [← hub]; exact (u * t).ne_zero)
  choose z hz using hp
  have key : (UpperTheory.V.Stk.dk (e + 1) : PadicAlgCl l) * ((b : PadicAlgCl l) ^ e * χ b * ∑ t : (ZMod F)ˣ, (th F b t : PadicAlgCl l) * (((t : ZMod F).val : PadicAlgCl l) ^ e * χ t) -
      2 * (χ b * (b : PadicAlgCl l) ^ (e + 1) - 1) * (UpperTheory.V.Bern.genB (e + 1) (χ : ZMod F → PadicAlgCl l) / (e + 1))) =
      ∑ t : (ZMod F)ˣ, χ ((b : ZMod F) * t) * ((F : PadicAlgCl l) * z t) := by
    have e1 : 2 * (χ b * (b : PadicAlgCl l) ^ (e + 1) - 1) * (UpperTheory.V.Bern.genB (e + 1) (χ : ZMod F → PadicAlgCl l) / (e + 1)) =
      2 * (χ b * (b : PadicAlgCl l) ^ (e + 1)) / (e + 1) * UpperTheory.V.Bern.genB (e + 1) (χ : ZMod F → PadicAlgCl l)
        - 2 / (e + 1) * UpperTheory.V.Bern.genB (e + 1) (χ : ZMod F → PadicAlgCl l) := by ring
    rw [e1]
    nth_rewrite 2 [g2]
    rw [g1, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    have h := congrArg (algebraMap ℚ (PadicAlgCl l)) (hz t)
    simp only [map_mul, map_sub, map_add (f := _), map_pow, map_natCast, map_intCast, map_div₀, map_one, map_ofNat] at h
    rw [← h, map_mul]
    ring
  rw [key]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun t _ => ?_
  obtain ⟨c, hc⟩ := hm
  have hn : ‖χ ((b : ZMod F) * t)‖ = 1 := by
    rw [← hub]; exact norm_chi χ (u * t)
  have hFc : (F : PadicAlgCl l) * z t = (l : PadicAlgCl l) ^ m * (((c : ℤ) * z t : ℤ) : PadicAlgCl l) := by
    have : (F : PadicAlgCl l) = (l : PadicAlgCl l) ^ m * c := by exact_mod_cast congrArg (Nat.cast : ℕ → PadicAlgCl l) hc
    rw [this]; push_cast; ring
  rw [norm_mul, hn, one_mul, hFc, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (IsUltrametricDist.norm_intCast_le_one _ _)
end
