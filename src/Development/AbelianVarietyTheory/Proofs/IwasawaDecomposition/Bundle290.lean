module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle010
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle277
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle278
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PowEqPowIffModEqOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FieldSizeAdjoinKthRoot
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle279
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHeckeCharTrivOnRealSubfieldInfinityType
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

section

open Formalism.BasicNotions Formalism.L2.Col GlobalTheory.Mem

namespace GlobalTheory.Mem.Col2

theorem fOk_of_fieldsOk {X : Fields} (hX : X.Ok) (σ : X.K →+* ℂ) (hσ : ∀ x, σ (star x) = starRingEnd ℂ (σ x)) :
    FOk X.emb σ :=
  ⟨hX.conjE, hX.emb_star, hσ⟩

theorem base_fOk (B : Base) : letI := B.fields.starE; FOk B.fields.emb B.embLL :=
  fOk_of_fieldsOk (GlobalTheory.Mem.FieldsLaws.fields_ok B) B.embLL B.starLL_cx

theorem base_fields_primes_ok : ∀ (B : Base) (X : PreX B.toPre),
    B.fields.Ok ∧ (B.primes X).Ok ∧ B.wts.Ok ∧ (letI := B.host.cmStar; FOk B.tauLL B.embLL) ∧
      2 * B.fields.f * B.R.k < (B.primes X).g 0 - 1 := fun B X =>
  ⟨GlobalTheory.Mem.FieldsLaws.fields_ok B, (GlobalTheory.BasePrimes.primes_ok B X).1,
    { row_ok τ := ⟨B.hc τ, rfl⟩
      hc_row u τ := by
        show RowPar.of (B.hcW u τ) = RowPar.of (B.hc τ)
        unfold RowPar.of
        rw [B.hcW_v, B.hcW_b, B.hcW_e]
      u_first u u' τ h := (B.hcW_first u τ h).trans (B.hcW_first u' τ h).symm
      u_last u u' τ h := (B.hcW_last u τ (by omega)).trans (B.hcW_last u' τ (by omega)).symm },
    base_fOk B, by rw [B.fields_f]; exact X.g_big 0⟩

end GlobalTheory.Mem.Col2
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.RayZeta

variable {K M L : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Field L] [NumberField L]
  [Algebra K M] [Algebra K L] [Algebra M L] [IsScalarTower K M L]


open NumberField IsDedekindDomain in
open scoped nonZeroDivisors IntermediateField in
variable {K M L : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Field L] [NumberField L]
  [Algebra K M] [Algebra K L] [Algebra M L] [IsScalarTower K M L] in
private theorem eq_of_pow_eq_one_of_sub_mem_prime {R : Type} [CommRing R] [IsDomain R] (P : Ideal R)
    [P.IsPrime] (p : ℕ) (hp : (p : R) ∉ P) {x y : R} (hx : x ^ p = 1) (hy : y ^ p = 1)
    (hxy : x - y ∈ P) : x = y := by
  by_contra hne
  have hS : ∑ k ∈ Finset.range p, x ^ k * y ^ (p - 1 - k) = 0 := by
    have := geom_sum₂_mul x y p
    rw [hx, hy, sub_self] at this
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hne)
  have hmem : (p : R) * x ^ (p - 1) ∈ P := by
    have : (p : R) * x ^ (p - 1) = ∑ k ∈ Finset.range p, (x ^ (p - 1) - x ^ k * y ^ (p - 1 - k)) := by
      rw [Finset.sum_sub_distrib, hS, Finset.sum_const, Finset.card_range, nsmul_eq_mul, sub_zero]
    rw [this]
    refine Ideal.sum_mem _ fun k hk => ?_
    have hk' : k + (p - 1 - k) = p - 1 := by
      have := Finset.mem_range.mp hk; omega
    obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow x y (p - 1 - k)
    have : x ^ (p - 1) - x ^ k * y ^ (p - 1 - k) = x ^ k * ((x - y) * c) := by
      rw [← hc, mul_sub, ← pow_add, hk']
    rw [this]
    exact P.mul_mem_left _ (P.mul_mem_right _ hxy)
  rcases Ideal.IsPrime.mem_or_mem ‹_› hmem with h | h
  · exact hp h
  · have hx0 : x ∈ P := Ideal.IsPrime.mem_of_pow_mem ‹_› _ h
    have : (1 : R) ∈ P := by
      rw [← hx]
      rcases Nat.eq_zero_or_pos p with rfl | hp0
      · simp at hp
      · exact P.pow_mem_of_mem hx0 _ hp0
    exact Ideal.IsPrime.ne_top ‹_› ((Ideal.eq_top_iff_one _).mpr this)


open NumberField IsDedekindDomain in
open scoped nonZeroDivisors IntermediateField in
variable {K M L : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Field L] [NumberField L]
  [Algebra K M] [Algebra K L] [Algebra M L] [IsScalarTower K M L] in
theorem _root_.GlobalTheory.Mem.RayZeta.root_mem_rayField : ∀ (K M L : Type) [Field K] [NumberField K]
    [Field M] [NumberField M] [Field L] [NumberField L]
    [Algebra K M] [Algebra K L] [Algebra M L] [IsScalarTower K M L] [IsGalois K L] (𝔮 : Ideal (𝓞 K))
    (p : ℕ), p ≠ 0 →
    𝔮 ≤ Ideal.span {(p : 𝓞 K)} → _root_.GlobalTheory.Mem.Fld.IsRayField K M 𝔮 →
    Subgroup.closure {σ : L ≃ₐ[K] L | ∃ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔮 ∧
      _root_.GlobalTheory.NT.IsFrob L v σ} = ⊤ →
    (∀ (I : Ideal (𝓞 K)) (α β : 𝓞 K), _root_.GlobalTheory.NT.RayPair 𝔮 α β → I * Ideal.span {β} = Ideal.span {α} →
      Ideal.absNorm I ≡ 1 [MOD p]) → ∀ ζ : L, ζ ^ p = 1 → ζ ∈ Set.range (algebraMap M L) := by
  intro K M L _ _ _ _ _ _ _ _ _ _ _ 𝔮 p hp hq hM hgen hnorm ζ hζ
  obtain ⟨hab, hunr, -, hray⟩ := hM
  haveI : IsGalois K M := hab.toIsGalois
  have hpow : ∀ a b : ℕ, a ≡ b [MOD p] → ζ ^ a = ζ ^ b := by
    intro a b h
    rw [← Nat.mod_add_div a p, ← Nat.mod_add_div b p, pow_add, pow_add, pow_mul, pow_mul, hζ,
      one_pow, one_pow, (h : a % p = b % p)]
  have hζint : IsIntegral ℤ ζ := IsIntegral.of_pow (Nat.pos_of_ne_zero hp) (hζ ▸ isIntegral_one)
  let z : 𝓞 L := ⟨ζ, hζint⟩
  have hz : z ^ p = 1 := by
    exact NumberField.RingOfIntegers.ext hζ
  have hfrob : ∀ (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K)), ¬ v.asIdeal ∣ 𝔮 →
      _root_.GlobalTheory.NT.IsFrob L v σ → σ ζ = ζ ^ Ideal.absNorm v.asIdeal := by
    intro σ v hv hF
    obtain ⟨P, hP, hlies, hx⟩ := hF
    have hpP : ((p : ℕ) : 𝓞 L) ∉ P := by
      intro hmem
      apply hv
      rw [Ideal.dvd_iff_le]
      refine hq.trans ?_
      rw [Ideal.span_le, Set.singleton_subset_iff, Ideal.over_def P v.asIdeal, Ideal.under,
        SetLike.mem_coe, Ideal.mem_comap, map_natCast]
      exact hmem
    have h1 : (σ • z) ^ p = 1 := by rw [← smul_pow', hz, smul_one]
    have := eq_of_pow_eq_one_of_sub_mem_prime P p hpP h1 (by rw [← pow_mul, mul_comm, pow_mul, hz, one_pow]) (hx z)
    exact congrArg (fun w : 𝓞 L => (w : L)) this
  let Q : (L ≃ₐ[K] L) → Prop := fun σ => ∃ I : Ideal (𝓞 K), I ≠ ⊥ ∧ IsCoprime I 𝔮 ∧
    (∀ χ : (M ≃ₐ[K] M) →* ℂˣ, _root_.GlobalTheory.NT.heckeIdeal M χ I =
      (χ (AlgEquiv.restrictNormalHom M σ) : ℂ)) ∧ σ ζ = ζ ^ Ideal.absNorm I
  have hmul : ∀ σ τ, Q σ → Q τ → Q (σ * τ) := by
    rintro σ τ ⟨I, hI0, hIq, hIχ, hIζ⟩ ⟨J, hJ0, hJq, hJχ, hJζ⟩
    refine ⟨I * J, fun h => (Ideal.mul_eq_bot.mp h).elim hI0 hJ0, hIq.mul_left hJq, fun χ => ?_, ?_⟩
    · rw [_root_.GlobalTheory.NT.Model.heckeIdeal_mul M χ hI0 hJ0, hIχ, hJχ, map_mul, map_mul, Units.val_mul]
    · rw [AlgEquiv.mul_apply, hJζ, map_pow, hIζ, ← pow_mul, map_mul]
  have hone : Q 1 := by
    refine ⟨1, by rw [Ideal.one_eq_top]; exact top_ne_bot, isCoprime_one_left, fun χ => ?_, ?_⟩
    · rw [_root_.GlobalTheory.NT.Model.heckeIdeal_top, map_one, map_one, Units.val_one]
    · rw [map_one, pow_one, AlgEquiv.one_apply]
  have hgenQ : ∀ σ ∈ {σ : L ≃ₐ[K] L | ∃ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔮 ∧
      _root_.GlobalTheory.NT.IsFrob L v σ}, Q σ := by
    rintro σ ⟨v, hv, hF⟩
    refine ⟨v.asIdeal, v.ne_bot, ?_, fun χ => ?_, hfrob σ v hv hF⟩
    · rw [Ideal.isCoprime_iff_sup_eq]
      by_contra hne
      apply hv
      rw [Ideal.dvd_iff_le]
      have := v.isMaximal.eq_of_le hne le_sup_left
      rw [this]
      exact le_sup_right
    · rw [_root_.GlobalTheory.NT.Model.heckeIdeal_prime,
        _root_.GlobalTheory.NT.heckeVal_of_unramIn M χ (hunr v hv)
          (_root_.GlobalTheory.RayMaximal.isFrob_restrictNormal (L := M) hF)]
      rfl
  have hall : ∀ σ, Q σ := by
    intro σ
    have hσ : σ ∈ Subgroup.closure {σ : L ≃ₐ[K] L | ∃ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔮 ∧
      _root_.GlobalTheory.NT.IsFrob L v σ} := hgen ▸ Subgroup.mem_top σ
    induction hσ using Subgroup.closure_induction with
    | mem σ hσ => exact hgenQ σ hσ
    | one => exact hone
    | mul σ τ _ _ hσ hτ => exact hmul σ τ hσ hτ
    | inv σ _ hσ =>
      have hpowQ : ∀ n : ℕ, Q (σ ^ n) := by
        intro n
        induction n with
        | zero => simpa using hone
        | succ n ih => rw [pow_succ]; exact hmul _ _ ih hσ
      have : σ⁻¹ = σ ^ (orderOf σ - 1) := by
        refine (eq_inv_of_mul_eq_one_left ?_).symm
        rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos σ), pow_orderOf_eq_one]
      rw [this]
      exact hpowQ _
  haveI := IsGalois.tower_top_of_isGalois K M L
  rw [InfiniteGalois.mem_range_algebraMap_iff_fixed]
  intro τ
  obtain ⟨I, hI0, hIq, hIχ, hIζ⟩ := hall (τ.restrictScalars K)
  have hres : AlgEquiv.restrictNormalHom M (τ.restrictScalars K) = 1 := by
    ext m
    apply (algebraMap M L).injective
    show algebraMap M L ((τ.restrictScalars K).restrictNormal M m) = _
    rw [AlgEquiv.restrictNormal_commutes]
    simp
  obtain ⟨α, β, hαβ, hI⟩ := (hray I hI0 hIq).mp fun χ => by
    rw [hIχ, hres, map_one, Units.val_one]
  have := hpow _ _ (hnorm I α β hαβ hI)
  rw [pow_one] at this
  exact hIζ.trans this

end GlobalTheory.Mem.RayZeta

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld GlobalTheory.Mem.FieldsEx
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.KPsiRam

theorem prime_dvd_of_mem_different (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (N : ℕ) (hmem : (N : 𝓞 L) ∈ differentIdeal (𝓞 K) (𝓞 L)) {p : ℕ} (hp : p.Prime) (h : p ∣ (discr L).natAbs) :
    p ∣ N ∨ p ∣ (discr K).natAbs := by
  have h1 := NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow K (𝓞 K) L (𝓞 L)
  have h2 : Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 L)) ∣ Ideal.absNorm (Ideal.span {(N : 𝓞 L)}) :=
    Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 hmem)
  rw [Ideal.absNorm_span_natCast] at h2
  rw [h1] at h
  exact ((Nat.Prime.dvd_mul hp).1 h).imp (fun h => hp.dvd_of_dvd_pow (h.trans h2)) hp.dvd_of_dvd_pow

theorem sup_adjoin_root (F : IntermediateField ℚ ℂ) [NumberField F] {k : ℕ} (hk : 0 < k) {y : F}
    (hy : y ∈ powIdealElts F k) {z : ℂ} (hz : z ^ k = (y : ℂ)) :
    ∃ _ : NumberField ↥(F ⊔ ℚ⟮z⟯), ∀ p : ℕ, p.Prime → p ∣ (discr ↥(F ⊔ ℚ⟮z⟯)).natAbs →
      p ∣ k ∨ p ∣ (discr F).natAbs := by
  obtain ⟨hy, I, hI⟩ := hy
  have hI' : (I : Submodule (𝓞 F) F) ^ k = Submodule.span (𝓞 F) {y} := by
    rw [← FractionalIdeal.coe_pow, ← hI, FractionalIdeal.coe_spanSingleton]
  set L : IntermediateField ℚ ℂ := F ⊔ ℚ⟮z⟯ with hLdef
  have hzL : z ∈ L := (le_sup_right : ℚ⟮z⟯ ≤ L) (IntermediateField.mem_adjoin_simple_self ℚ z)
  have hzF : IsIntegral F z := IsIntegral.of_pow hk (by rw [hz]; exact isIntegral_algebraMap (x := y))
  have hzQ : IsIntegral ℚ z := isIntegral_trans z hzF
  haveI : FiniteDimensional ℚ ℚ⟮z⟯ := IntermediateField.adjoin.finiteDimensional hzQ
  have hLfin : FiniteDimensional ℚ L := IntermediateField.finiteDimensional_sup F ℚ⟮z⟯
  letI : NumberField L := NumberField.mk
  letI : Algebra F L := (IntermediateField.inclusion (le_sup_left : F ≤ L)).toRingHom.toAlgebra
  haveI : IsScalarTower F L ℂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hz' : (⟨z, hzL⟩ : L) ^ k = algebraMap F L y := Subtype.ext hz
  have hzi : IsIntegral F (⟨z, hzL⟩ : L) := Algebra.IsIntegral.isIntegral _
  have htop : F⟮(⟨z, hzL⟩ : L)⟯ = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨w, hw⟩ -
    let M : IntermediateField ℚ ℂ :=
      ((F⟮(⟨z, hzL⟩ : L)⟯).map (IsScalarTower.toAlgHom F L ℂ)).restrictScalars ℚ
    have hM : L ≤ M := by
      refine sup_le (fun v hv => ?_) (IntermediateField.adjoin_simple_le_iff.mpr ?_)
      · exact ((F⟮(⟨z, hzL⟩ : L)⟯).map (IsScalarTower.toAlgHom F L ℂ)).algebraMap_mem ⟨v, hv⟩
      · exact ⟨_, IntermediateField.mem_adjoin_simple_self F _, rfl⟩
    obtain ⟨w', hw', hww⟩ := hM hw
    have : w' = ⟨w, hw⟩ := Subtype.ext hww
    rwa [this] at hw'
  have htop' : Algebra.adjoin F {(⟨z, hzL⟩ : L)} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hzi.isAlgebraic, htop,
      IntermediateField.top_toSubalgebra]
  have hD := GlobalTheory.FieldSize.natCast_mem_differentIdeal_of_root k hk y hy _ hI' _ hz' htop'
  exact ⟨inferInstance, fun p hp h => prime_dvd_of_mem_different F L k hD hp h⟩

theorem sup_adjoin_roots {E : Type} [Field E] [NumberField E] (φ : E →+* ℂ) {h : ℕ} (hh : 0 < h) (S : Set ℂ)
    (hS : S.Finite) (hS' : ∀ z ∈ S, ∃ y ∈ powIdealElts E h, z ^ h = φ y) :
    ∃ _ : NumberField ↥(imField φ ⊔ IntermediateField.adjoin ℚ S), ∀ p : ℕ, p.Prime →
      p ∣ (discr ↥(imField φ ⊔ IntermediateField.adjoin ℚ S)).natAbs → p ∣ h ∨ p ∣ (discr E).natAbs := by
  induction S, hS using Set.Finite.induction_on with
  | empty =>
    rw [IntermediateField.adjoin_empty, sup_bot_eq]
    let e₀ : E ≃ₐ[ℚ] imField φ := AlgEquiv.ofInjectiveField φ.toRatAlgHom
    have : FiniteDimensional ℚ (imField φ) := e₀.toLinearEquiv.finiteDimensional
    have hN : NumberField (imField φ) := NumberField.of_module_finite ℚ _
    exact ⟨hN, fun p _ hp => Or.inr (by rwa [discr_eq_discr_of_algEquiv _ e₀])⟩
  | @insert z S _ _ ih =>
    obtain ⟨_, ih⟩ := ih fun w hw => hS' w (Set.mem_insert_of_mem _ hw)
    obtain ⟨y, hy, hz⟩ := hS' z (Set.mem_insert _ _)
    have hE : ∀ x, φ x ∈ imField φ ⊔ IntermediateField.adjoin ℚ S := (imField_le_iff φ).1 le_sup_left
    obtain ⟨hN, H⟩ := sup_adjoin_root _ hh (map_mem_pow (φ.codRestrict _ hE) hy) hz
    rw [Set.insert_eq, Set.union_comm, IntermediateField.adjoin_union, ← sup_assoc]
    exact ⟨hN, fun p hp hd => (H p hp hd).elim Or.inl (ih p hp)⟩

theorem typeNorm_mem {R : Ranks} (H : Host R) (p q : ℕ) {h : ℕ} {γ : H.E} (hγ : γ ∈ powIdealElts H.E h) :
    typeNorm H p q γ ∈ powIdealElts H.E h := by
  have hσ : ∀ (σ : H.E ≃ₐ[ℚ] H.E) {x}, x ∈ powIdealElts H.E h → σ x ∈ powIdealElts H.E h :=
    fun σ _ hx => map_mem_pow (σ : H.E →+* H.E) hx
  exact prod_mem_pow _ _ fun g _ => mul_mem_pow (npow_mem_pow (hσ _ hγ) _) (npow_mem_pow (hσ _ (hσ _ hγ)) _)

theorem prime_dvd_discr_iSup_kPsi : ∀ (P : Pre) (δ : FieldDat P),
    ∃ _ : NumberField ↥(⨆ j ∈ Set.Icc 1 P.R.m, δ.KPsi j), ∀ p : ℕ, p.Prime →
      p ∣ (discr ↥(⨆ j ∈ Set.Icc 1 P.R.m, δ.KPsi j)).natAbs → p ∣ classNumber P.host.E * (discr P.host.E).natAbs := by
  intro P δ
  let S : Set ℂ := {rootOne (classNumber P.host.E)} ∪ ⋃ j ∈ Set.Icc 1 P.R.m, ⋃ i,
    {z | z ^ δ.basis.h i = P.host.φ₀ (typeNorm P.host (P.R.sigW j).1 (P.R.sigW j).2 (δ.basis.γ i : P.host.E))}
  have hS : S.Finite := by
    refine (Set.finite_singleton _).union ((Set.finite_Icc _ _).biUnion fun j _ => Set.finite_iUnion fun i => ?_)
    refine Set.Finite.subset (Polynomial.nthRoots (δ.basis.h i) (P.host.φ₀
      (typeNorm P.host (P.R.sigW j).1 (P.R.sigW j).2 (δ.basis.γ i : P.host.E)))).toFinset.finite_toSet fun z hz => ?_
    rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_nthRoots (δ.basis.h_pos i)]
    exact hz
  have hS' : ∀ z ∈ S, ∃ y ∈ powIdealElts P.host.E (classNumber P.host.E), z ^ classNumber P.host.E = P.host.φ₀ y := by
    rintro z (rfl | hz)
    · exact ⟨1, one_mem_pow, by
        rw [map_one]; exact (Complex.isPrimitiveRoot_exp _ (classNumber_ne_zero _)).pow_eq_one⟩
    · simp only [Set.mem_iUnion] at hz
      obtain ⟨j, -, i, hz⟩ := hz
      have hγ : (δ.basis.γ i : P.host.E) ∈ powIdealElts P.host.E (δ.basis.h i) :=
        ⟨(δ.basis.γ i).ne_zero, δ.basis.c i, by
          rw [← coe_toPrincipalIdeal, ← δ.basis.pow_eq i, Units.val_pow_eq_pow_val]; rfl⟩
      obtain ⟨k, hk⟩ : δ.basis.h i ∣ classNumber P.host.E := orderOf_dvd_card
      refine ⟨_, hk ▸ pow_mem_powIdealElts (typeNorm_mem P.host (P.R.sigW j).1 (P.R.sigW j).2 hγ) k, ?_⟩
      rw [hk, pow_mul, map_pow]
      exact congrArg (· ^ k) hz
  obtain ⟨_, H⟩ := sup_adjoin_roots P.host.φ₀ (classNumber_pos P.host.E) S hS hS'
  have hle : (⨆ j ∈ Set.Icc 1 P.R.m, δ.KPsi j) ≤ imField P.host.φ₀ ⊔ IntermediateField.adjoin ℚ S := by
    refine iSup₂_le fun j hj => sup_le (sup_le le_sup_left (le_sup_of_le_right ?_)) (le_sup_of_le_right ?_)
    · exact IntermediateField.adjoin.mono _ _ _ Set.subset_union_left
    · refine IntermediateField.adjoin.mono _ _ _ ?_
      rintro z ⟨i, hz⟩
      exact Or.inr (Set.mem_iUnion₂.2 ⟨j, hj, Set.mem_iUnion.2 ⟨i, hz⟩⟩)
  have : FiniteDimensional ℚ ↥(⨆ j ∈ Set.Icc 1 P.R.m, δ.KPsi j) :=
    Module.Finite.of_injective (IntermediateField.inclusion hle).toLinearMap (IntermediateField.inclusion hle).injective
  have hN : NumberField ↥(⨆ j ∈ Set.Icc 1 P.R.m, δ.KPsi j) := NumberField.mk
  letI := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  refine ⟨hN, fun p hp hd => (Nat.Prime.dvd_mul hp).2 (H p hp (hd.trans ?_))⟩
  exact Int.natAbs_dvd_natAbs.2 (discr_dvd_discr _ _)

end GlobalTheory.Mem.KPsiRam
end

section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.FieldsEx

theorem absNorm_pow_eq_prod_sq {L : Type} [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L] {I : Type} [Fintype I]
    (φ : I → L →+* ℂ) (hφ : Function.Bijective fun i => InfinitePlace.mk (φ i)) (v : HeightOneSpectrum (𝓞 L)) (h : ℕ)
    (k : L) (hk : FractionalIdeal.spanSingleton (𝓞 L)⁰ k = (v.asIdeal : FractionalIdeal (𝓞 L)⁰ L) ^ h) :
    ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ h = (∏ i, ‖φ i k‖) ^ 2 := by
  have h1 := InfinitePlace.prod_eq_abs_norm k
  rw [← hφ.prod_comp] at h1
  have h2 : ∀ i, (InfinitePlace.mk (φ i)) k ^ (InfinitePlace.mk (φ i)).mult = ‖φ i k‖ ^ 2 := by
    intro i
    rw [InfinitePlace.apply, IsTotallyComplex.mult_eq]
  simp_rw [h2] at h1
  have h3 := congrArg FractionalIdeal.absNorm hk
  rw [FractionalIdeal.absNorm_span_singleton, map_pow, FractionalIdeal.coeIdeal_absNorm] at h3
  rw [← Finset.prod_pow, h1, h3]
  simp

theorem valTw_mem_kummerField : ∀ (L : Type) [Field L] [NumberField L] [IsGalois ℚ L] [_root_.NumberField.IsTotallyComplex L] (φ₀ : L →+* ℂ) (I : Type) [Fintype I] (φ : I → L →+* ℂ), (Function.Bijective fun i => InfinitePlace.mk (φ i)) → ∀ (χ : HChar L) (n : I → ℤ) (r : ℤ), χ.HasInf φ n → (∀ i, Even (n i - r)) → ∀ (v : HeightOneSpectrum (𝓞 L)) (h : ℕ) (k : Lˣ), FractionalIdeal.spanSingleton (𝓞 L)⁰ (k : L) = (v.asIdeal : FractionalIdeal (𝓞 L)⁰ L) ^ h → χ.inf k * χ.val v ^ h = 1 → χ.valTw ((r : ℝ) / 2) v ∈ kummerField φ₀ h := by
  intro L _ _ _ _ φ₀ I _ φ hφ χ n r hinf hev v h k hk hχ
  choose s hs using exists_aut φ₀
  choose m hm using hev
  have hkm : (k : L) ∈ powIdealElts L h := ⟨k.ne_zero, _, hk⟩
  have hsm : ∀ τ, s τ (k : L) ∈ powIdealElts L h := fun τ => map_mem_pow (s τ : L →+* L) hkm
  have hy : ∏ i, ((s (φ i) k ^ n i)⁻¹ * (s (φ i) k * s ((starRingEnd ℂ).comp (φ i)) k) ^ m i) ∈ powIdealElts L h :=
    prod_mem_pow _ _ fun i _ => mul_mem_pow (inv_mem_pow (zpow_mem_pow (hsm _) _))
      (zpow_mem_pow (mul_mem_pow (hsm _) (hsm _)) _)
  refine mem_kummerField φ₀ hy ?_
  have hp := congrArg (Units.val : ℂˣ → ℂ) hχ
  rw [Units.val_mul, hinf, Units.val_one, Units.val_pow_eq_pow_val] at hp
  have hN := absNorm_pow_eq_prod_sq φ hφ v h k hk
  have hpow : ∀ m : ℕ, (m : ℂ) ^ (-(((r : ℝ) / 2 : ℝ) : ℂ)) = (((m : ℝ) ^ (-((r : ℝ) / 2)) : ℝ) : ℂ) := by
    intro m
    rw [Complex.ofReal_cpow (Nat.cast_nonneg m), Complex.ofReal_natCast, Complex.ofReal_neg]
  have hreal : (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-((r : ℝ) / 2))) ^ h = (∏ i, ‖φ i k‖) ^ (-r) := by
    have h0 : 0 ≤ ∏ i, ‖φ i k‖ := Finset.prod_nonneg fun _ _ => norm_nonneg _
    rw [Real.rpow_pow_comm (Nat.cast_nonneg _), hN, ← Real.rpow_natCast, ← Real.rpow_mul h0, ← Real.rpow_intCast]
    congr 1
    push_cast
    ring
  have hc : χ.valTw ((r : ℝ) / 2) v ^ h = ((χ.val v : ℂˣ) : ℂ) ^ h * ∏ i, ((‖φ i k‖ : ℝ) : ℂ) ^ (-r) := by
    unfold HChar.valTw
    rw [hpow, mul_pow, ← Complex.ofReal_pow, hreal, Finset.prod_zpow, Complex.ofReal_zpow, Complex.ofReal_prod]
  rw [hc, eq_inv_of_mul_eq_one_right hp, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hz' : ((‖φ i k‖ : ℝ) : ℂ) ≠ 0 := by simp
  rw [map_mul, map_inv₀, map_zpow₀, map_zpow₀, map_mul, ← hs, ← hs, RingHom.comp_apply, Complex.mul_conj', sq,
    mul_zpow, ← zpow_add₀ hz', ← hm, sub_eq_add_neg, zpow_add₀ hz', div_zpow, inv_div, div_eq_mul_inv]
  ring

end GlobalTheory.Mem.FieldsEx
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.RayMono

theorem exists_apply_eq_of_normal {K A Ω : Type} [Field K] [Field A] [Field Ω] [Algebra K A] [Algebra K Ω]
    [Normal K A] (i j : A →ₐ[K] Ω) (x : A) : ∃ y, j y = i x := by
  let _ := j.toRingHom.toAlgebra
  have : IsScalarTower K A Ω := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  exact ⟨i.restrictNormal A x, i.restrictNormal_commutes A x⟩

theorem le_of_isRayFieldIn_of_dvd : ∀ (E : Type) [Field E] [NumberField E] (φ : E →+* ℂ) (𝔪 𝔪' : Ideal (𝓞 E))
    (M M' : IntermediateField ℚ ℂ), 𝔪' ≠ ⊥ → 𝔪 ∣ 𝔪' → IsRayFieldIn φ 𝔪 M → IsRayFieldIn φ 𝔪' M' → M ≤ M' := by
  rintro E _ _ φ 𝔪 𝔪' M M' hn hd ⟨h, _, hM⟩ ⟨h', _, hM'⟩ z hz
  let _ := algOf φ M h
  let _ := algOf φ M' h'
  let _ := φ.toAlgebra
  have := hM.1
  have := hM'.1
  obtain ⟨f⟩ := nonempty_algHom_of_isRay_of_dvd hn hd hM'.2 hM.2
  let i : M →ₐ[E] ℂ := { M.val.toRingHom with commutes' := fun _ => rfl }
  let i' : M' →ₐ[E] ℂ := { M'.val.toRingHom with commutes' := fun _ => rfl }
  obtain ⟨y, hy⟩ := exists_apply_eq_of_normal i (i'.comp f) ⟨z, hz⟩
  have hy' : ((f y : M') : ℂ) = z := hy
  exact hy' ▸ (f y).2

end GlobalTheory.Mem.RayMono
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.DefU.NonTriv

section Char

open Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_unit (k : Eˣ) (hk : _root_.Neutral.B1.diagUnits E k ∈ unitIdl E) : ∃ u : (𝓞 E)ˣ, ((u : 𝓞 E) : E) = k := by
  have hv : ∀ x : Eˣ, _root_.Neutral.B1.diagUnits E x ∈ unitIdl E → ∀ v : HeightOneSpectrum (𝓞 E), v.valuation E (x : E) ≤ 1 :=
    fun x hx v => by rw [← GlobalTheory.Mem.Chr.AntiExist.val_diag v x, hx v]
  obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) (K := E) (k : E) (hv k hk)
  obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) (K := E) ((k⁻¹ : Eˣ) : E)
    (hv k⁻¹ (inv_mem hk))
  have hab : a * b = 1 := RingOfIntegers.ext (by
    change algebraMap (𝓞 E) E (a * b) = algebraMap (𝓞 E) E 1
    rw [map_mul, ha, hb, map_one, Units.mul_inv])
  exact ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, ha⟩

end Char

section Char

open Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


end Char

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open Formalism.L2.Host

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

end GlobalTheory.DefU.NonTriv

end
end
