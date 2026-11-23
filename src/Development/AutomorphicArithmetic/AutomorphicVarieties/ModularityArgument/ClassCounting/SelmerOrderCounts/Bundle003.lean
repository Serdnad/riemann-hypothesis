module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.TwoLe
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
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
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.RingTheory.DedekindDomain.Factorization

@[expose] public section

section

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.ZK UpperTheory.V.ZK.Ct

private theorem intValuation_equivOfRingEquiv_apply {F : Type} [Field F] [NumberField F] (e : 𝓞 F ≃+* 𝓞 F)
    (P : HeightOneSpectrum (𝓞 F)) (r : 𝓞 F) :
    (HeightOneSpectrum.equivOfRingEquiv e P).intValuation (e r) = P.intValuation r := by
  set Q := HeightOneSpectrum.equivOfRingEquiv e P with hQdef
  have hQ : Q.asIdeal = P.asIdeal.map e := by
    rw [hQdef, ← Ideal.comap_symm]
    rfl
  have key : ∀ n : ℕ, Q.intValuation (e r) ≤ WithZero.exp (-(n : ℤ)) ↔
      P.intValuation r ≤ WithZero.exp (-(n : ℤ)) := by
    intro n
    rw [HeightOneSpectrum.intValuation_le_pow_iff_mem, HeightOneSpectrum.intValuation_le_pow_iff_mem,
      hQ, ← Ideal.map_pow, Ideal.apply_mem_of_equiv_iff]
  by_cases hr : r = 0
  · simp [hr]
  have hr' : e r ≠ 0 := by simpa using hr
  obtain ⟨m, hm⟩ : ∃ m : ℕ, Q.intValuation (e r) = WithZero.exp (-(m : ℤ)) :=
    ⟨_, HeightOneSpectrum.intValuation_if_neg _ hr'⟩
  obtain ⟨k, hk⟩ : ∃ k : ℕ, P.intValuation r = WithZero.exp (-(k : ℤ)) :=
    ⟨_, HeightOneSpectrum.intValuation_if_neg _ hr⟩
  rw [hm, hk] at key ⊢
  have h1 := (key k).2 le_rfl
  have h2 := (key m).1 le_rfl
  rw [WithZero.exp_le_exp] at h1 h2
  have hmk : m = k := by omega
  rw [hmk]

private theorem valuation_equivOfRingEquiv_mapRingEquiv_apply {F : Type} [Field F] [NumberField F] (σ : F ≃+* F)
    (P : HeightOneSpectrum (𝓞 F)) (x : F) :
    (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv σ) P).valuation F (σ x) =
      P.valuation F x := by
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) x
  have ha : σ (algebraMap (𝓞 F) F a) = algebraMap (𝓞 F) F (RingOfIntegers.mapRingEquiv σ a) := rfl
  have hb : σ (algebraMap (𝓞 F) F b) = algebraMap (𝓞 F) F (RingOfIntegers.mapRingEquiv σ b) := rfl
  rw [map_div₀, ha, hb, map_div₀, map_div₀, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, intValuation_equivOfRingEquiv_apply, intValuation_equivOfRingEquiv_apply]

private theorem ordP_actU_inv_eq_ordP_actP {L F : Type} [Field L] [Field F] [NumberField F] [Algebra L F]
    (γ : Gal(F/L)) (α : Fˣ) (P : HeightOneSpectrum (𝓞 F)) :
    ordP P (actU γ⁻¹ α) = ordP (actP γ P) α := by
  have h := valuation_equivOfRingEquiv_mapRingEquiv_apply γ.toRingEquiv P ((γ⁻¹ : Gal(F/L)) (α : F))
  have e1 : γ.toRingEquiv ((γ⁻¹ : Gal(F/L)) (α : F)) = α := by
    simp [AlgEquiv.aut_inv]
  rw [e1] at h
  simp only [ordP, actP, actU, Units.coe_map]
  rw [h]
  rfl

private theorem actP_mul_selmer_order_counts {L F : Type} [Field L] [Field F] [NumberField F] [Algebra L F]
    (σ τ : Gal(F/L)) (P : HeightOneSpectrum (𝓞 F)) : actP (σ * τ) P = actP σ (actP τ P) := by
  apply HeightOneSpectrum.ext
  ext x
  change (RingOfIntegers.mapRingEquiv (σ * τ).toRingEquiv).symm x ∈ P.asIdeal ↔
    (RingOfIntegers.mapRingEquiv τ.toRingEquiv).symm
      ((RingOfIntegers.mapRingEquiv σ.toRingEquiv).symm x) ∈ P.asIdeal
  have : (RingOfIntegers.mapRingEquiv (σ * τ).toRingEquiv).symm x =
      (RingOfIntegers.mapRingEquiv τ.toRingEquiv).symm
        ((RingOfIntegers.mapRingEquiv σ.toRingEquiv).symm x) := by
    apply RingOfIntegers.ext
    simp
    rw [← AlgEquiv.aut_inv, ← AlgEquiv.aut_inv, ← AlgEquiv.aut_inv, mul_inv_rev, AlgEquiv.mul_apply]
  rw [this]

private theorem actP_one_selmer_order_counts {L F : Type} [Field L] [Field F] [NumberField F] [Algebra L F]
    (P : HeightOneSpectrum (𝓞 F)) : actP (1 : Gal(F/L)) P = P := by
  apply HeightOneSpectrum.ext
  ext x
  change (RingOfIntegers.mapRingEquiv (1 : Gal(F/L)).toRingEquiv).symm x ∈ P.asIdeal ↔ x ∈ P.asIdeal
  have : (RingOfIntegers.mapRingEquiv (1 : Gal(F/L)).toRingEquiv).symm x = x := by
    apply RingOfIntegers.ext
    simp
    rw [← AlgEquiv.aut_inv, inv_one, AlgEquiv.one_apply]
  rw [this]

private theorem actU_mul' {L F : Type} [Field L] [Field F] [Algebra L F]
    (σ τ : Gal(F/L)) (α : Fˣ) : actU (σ * τ) α = actU σ (actU τ α) := by
  ext
  simp [actU]

private theorem actU_one' {L F : Type} [Field L] [Field F] [Algebra L F] (α : Fˣ) :
    actU (1 : Gal(F/L)) α = α := by
  ext
  simp [actU]

private theorem ordP_mul' {F : Type} [Field F] [NumberField F] (P : HeightOneSpectrum (𝓞 F))
    (α β : Fˣ) : ordP P (α * β) = ordP P α + ordP P β := by
  have hα : P.valuation F (α : F) ≠ 0 := by simp
  have hβ : P.valuation F (β : F) ≠ 0 := by simp
  simp only [ordP, Units.val_mul, map_mul]
  rw [WithZero.log_mul hα hβ]
  ring

private theorem one_lt_valuation_iff_ordP_neg {F : Type} [Field F] [NumberField F] (P : HeightOneSpectrum (𝓞 F))
    (α : Fˣ) : 1 < P.valuation F (α : F) ↔ ordP P α < 0 := by
  have hw : P.valuation F (α : F) ≠ 0 := by simp
  conv_lhs => rw [← WithZero.exp_log hw]
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
  simp only [ordP]
  omega

private theorem finite_setOf_ordP_ne_zero {F : Type} [Field F] [NumberField F] (α : Fˣ) :
    {P : HeightOneSpectrum (𝓞 F) | ordP P α ≠ 0}.Finite := by
  refine ((HeightOneSpectrum.Support.finite (𝓞 F) (α : F)).union
    (HeightOneSpectrum.Support.finite (𝓞 F) ((α⁻¹ : Fˣ) : F))).subset ?_
  intro P hP
  have hinv : ordP P α⁻¹ = -ordP P α := by
    have h := ordP_mul' P α α⁻¹
    have h1 : ordP P (1 : Fˣ) = 0 := by simp [ordP]
    rw [mul_inv_cancel, h1] at h
    omega
  simp only [Set.mem_setOf_eq] at hP
  rcases lt_or_gt_of_ne hP with h | h
  · left
    exact (one_lt_valuation_iff_ordP_neg P α).2 h
  · right
    exact (one_lt_valuation_iff_ordP_neg P α⁻¹).2 (by omega)

theorem UpperTheory.V.ZK.Ct.datEx :
    ∀ (L F : Type) [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] (γ : F ≃ₐ[L] F) (a : ℕ), 2 ≤ a → ∃ D : Dat (Additive Fˣ) (HeightOneSpectrum (𝓞 F) →₀ ℤ), IsDat γ a D := by
  intro L F _ _ _ _ _ γ a ha
  let E := HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv γ.toRingEquiv)
  let g : Module.End ℤ (Additive Fˣ) := (MonoidHom.toAdditive (actU γ⁻¹)).toIntLinearMap
  let gI : Module.End ℤ (HeightOneSpectrum (𝓞 F) →₀ ℤ) :=
    (Finsupp.domLCongr E.symm : (HeightOneSpectrum (𝓞 F) →₀ ℤ) ≃ₗ[ℤ] _).toLinearMap
  let dA : Additive Fˣ →+ (HeightOneSpectrum (𝓞 F) →₀ ℤ) :=
    { toFun := fun y => Finsupp.ofSupportFinite (fun P => ordP P (Additive.toMul y))
        (finite_setOf_ordP_ne_zero (Additive.toMul y))
      map_zero' := by
        ext P
        simp [Finsupp.ofSupportFinite_coe, ordP]
      map_add' := by
        intro y z
        ext P
        simp [Finsupp.ofSupportFinite_coe, ordP_mul']
        rfl }
  have hg1 : ∀ α : Fˣ, g (Additive.ofMul α) = Additive.ofMul (actU γ⁻¹ α) := fun α => rfl
  have hgI1 : ∀ (𝔡 : HeightOneSpectrum (𝓞 F) →₀ ℤ) (P : HeightOneSpectrum (𝓞 F)),
      (gI 𝔡) P = 𝔡 (actP γ P) := by
    intro 𝔡 P
    simp [gI, Finsupp.domLCongr_apply, Finsupp.equivMapDomain_apply]
    rfl
  have hd1 : ∀ (α : Fˣ) (P : HeightOneSpectrum (𝓞 F)),
      (dA.toIntLinearMap (Additive.ofMul α)) P = ordP P α := by
    intro α P
    rfl
  have hgk : ∀ (k : ℕ) (α : Fˣ), (g ^ k) (Additive.ofMul α) = Additive.ofMul (actU (γ⁻¹ ^ k) α) := by
    intro k
    induction k with
    | zero =>
      intro α
      rw [pow_zero, pow_zero, Module.End.one_apply, actU_one']
    | succ k ih =>
      intro α
      rw [pow_succ, Module.End.mul_apply, hg1, ih, pow_succ, actU_mul']
  have hgIk : ∀ (k : ℕ) (𝔡 : HeightOneSpectrum (𝓞 F) →₀ ℤ) (P : HeightOneSpectrum (𝓞 F)),
      ((gI ^ k) 𝔡) P = 𝔡 (actP (γ ^ k) P) := by
    intro k
    induction k with
    | zero =>
      intro 𝔡 P
      rw [pow_zero, pow_zero, Module.End.one_apply, actP_one_selmer_order_counts]
    | succ k ih =>
      intro 𝔡 P
      rw [pow_succ', Module.End.mul_apply, hgI1, ih, pow_succ, actP_mul_selmer_order_counts]
  have hn1 : γ⁻¹ ^ orderOf γ = 1 := by rw [inv_pow, pow_orderOf_eq_one, inv_one]
  have hn2 : γ ^ orderOf γ = 1 := pow_orderOf_eq_one γ
  refine ⟨⟨g, gI, dA.toIntLinearMap, orderOf γ, a, ?_, ?_, ?_, orderOf_pos γ, ha, ?_⟩,
    ⟨rfl, rfl, hg1, hgI1, hd1⟩⟩
  · intro y
    ext P
    rw [hgI1]
    change ordP P (actU γ⁻¹ (Additive.toMul y)) = ordP (actP γ P) (Additive.toMul y)
    exact ordP_actU_inv_eq_ordP_actP γ (Additive.toMul y) P
  · apply LinearMap.ext
    intro y
    rw [Module.End.one_apply]
    have h := hgk (orderOf γ) (Additive.toMul y)
    rw [hn1, actU_one'] at h
    exact h
  · apply LinearMap.ext
    intro 𝔡
    rw [Module.End.one_apply]
    ext P
    rw [hgIk, hn2, actP_one_selmer_order_counts]
  · intro m x hm hx
    ext P
    have h := congrArg (fun f => f P) hx
    simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.coe_zero, Pi.zero_apply,
      mul_eq_zero] at h
    rcases h with h | h
    · exact absurd h hm
    · simpa using h
end

section

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.ZK UpperTheory.V.ZK.Ct
open scoped nonZeroDivisors

private theorem fractionalIdeal_count_spanSingleton_eq_ordP {F : Type} [Field F] [NumberField F] (P : HeightOneSpectrum (𝓞 F)) (x : Fˣ) :
    FractionalIdeal.count F P (FractionalIdeal.spanSingleton (𝓞 F)⁰ (x : F)) = ordP P x := by
  obtain ⟨r, s, hs, hrs⟩ := IsFractionRing.div_surjective (𝓞 F) (x : F)
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hrs
    exact x.ne_zero hrs.symm
  have hI : FractionalIdeal.spanSingleton (𝓞 F)⁰ (x : F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ ((algebraMap (𝓞 F) F) s)⁻¹ * ↑(Ideal.span {r}) := by
    rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_mul_spanSingleton,
      ← hrs, div_eq_mul_inv, mul_comm]
  rw [FractionalIdeal.count_well_defined F P (by rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact x.ne_zero) hI]
  unfold ordP
  rw [← hrs, map_div₀]
  erw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
  rw [HeightOneSpectrum.intValuation_if_neg _ hr0, HeightOneSpectrum.intValuation_if_neg _ hs0,
    ← WithZero.exp_sub, WithZero.log_exp]
  ring

theorem UpperTheory.V.ZK.Ct.clFin :
    ∀ (L F : Type) [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] (γ : F ≃ₐ[L] F) (a : ℕ) (D : Dat (Additive Fˣ) (HeightOneSpectrum (𝓞 F) →₀ ℤ)), IsDat γ a D → Finite ((HeightOneSpectrum (𝓞 F) →₀ ℤ) ⧸ LinearMap.range D.d) := by
  intro L F _ _ _ _ _ γ a D hD
  classical
  obtain ⟨I, hI⟩ : ∃ I : (HeightOneSpectrum (𝓞 F) →₀ ℤ) → (FractionalIdeal (𝓞 F)⁰ F)ˣ,
      ∀ e P, FractionalIdeal.count F P (I e : FractionalIdeal (𝓞 F)⁰ F) = e P :=
    ⟨fun e => Units.mk0 (e.prod fun P n => ((P.asIdeal : FractionalIdeal (𝓞 F)⁰ F)) ^ n)
      (Finset.prod_ne_zero_iff.mpr fun P _ =>
        zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr P.ne_bot)),
      fun e P => FractionalIdeal.count_finsuppProd F P e⟩
  have key : ∀ e e', ClassGroup.mk F (I e) = ClassGroup.mk F (I e') → e - e' ∈ LinearMap.range D.d := by
    intro e e' h
    have h' : ClassGroup.mk F (I e * (I e')⁻¹) = 1 := by
      rw [map_mul, map_inv, h, mul_inv_cancel]
    obtain ⟨x, hx⟩ := (ClassGroup.mk_eq_one_iff.1 h').principal
    have hJ : ((I e * (I e')⁻¹ : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) =
        FractionalIdeal.spanSingleton (𝓞 F)⁰ x := by
      apply FractionalIdeal.coeToSubmodule_injective
      dsimp only
      rw [FractionalIdeal.coe_spanSingleton]
      exact hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [FractionalIdeal.spanSingleton_zero] at hJ
      exact Units.ne_zero _ hJ
    refine ⟨Additive.ofMul (Units.mk0 x hx0), ?_⟩
    ext P
    rw [hD.d_eq, Finsupp.coe_sub, Pi.sub_apply, ← hI e P, ← hI e' P, ← fractionalIdeal_count_spanSingleton_eq_ordP, Units.val_mk0, ← hJ,
      Units.val_mul, Units.val_inv_eq_inv_val,
      FractionalIdeal.count_mul F P (Units.ne_zero _) (inv_ne_zero (Units.ne_zero _)),
      FractionalIdeal.count_inv]
    ring
  refine Finite.of_injective (fun q => ClassGroup.mk F (I (Quotient.out q))) ?_
  intro q1 q2 h
  rw [← Submodule.Quotient.mk_out q1, ← Submodule.Quotient.mk_out q2]
  exact (Submodule.Quotient.eq _).2 (key _ _ h)
end

section

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.ZK UpperTheory.V.ZK.Ct

private theorem actP_actP_inv' {L F : Type} [Field L] [Field F] [Algebra L F] (γ : Gal(F/L))
    (Q : HeightOneSpectrum (𝓞 F)) : actP γ (actP γ⁻¹ Q) = Q := by
  ext x
  change ((RingOfIntegers.mapRingEquiv γ⁻¹.toRingEquiv).symm
    ((RingOfIntegers.mapRingEquiv γ.toRingEquiv).symm x)) ∈ Q.asIdeal ↔ x ∈ Q.asIdeal
  have : ((RingOfIntegers.mapRingEquiv γ⁻¹.toRingEquiv).symm
      ((RingOfIntegers.mapRingEquiv γ.toRingEquiv).symm x)) = x := by
    apply RingOfIntegers.ext
    simp [RingOfIntegers.mapRingEquiv]
    rw [AlgEquiv.aut_inv, AlgEquiv.symm_symm, AlgEquiv.apply_symm_apply]
  rw [this]

private theorem card_addMonoidHom_zmod_le_card (H : Type) [AddCommGroup H] [Finite H] (q : ℕ) [NeZero q] :
    Nat.card (H →+ ZMod q) ≤ Nat.card H := by
  have : Fintype H := Fintype.ofFinite H
  have hinj : Function.Injective (fun ψ : H →+ ZMod q => ZMod.stdAddChar.compAddMonoidHom ψ) := by
    intro ψ₁ ψ₂ h
    ext x
    have := DFunLike.congr_fun h x
    simp only [AddChar.compAddMonoidHom_apply] at this
    exact ZMod.injective_stdAddChar this
  calc Nat.card (H →+ ZMod q) ≤ Nat.card (AddChar H ℂ) := Nat.card_le_card_of_injective _ hinj
    _ = Nat.card H := by rw [Nat.card_eq_fintype_card, AddChar.card_eq, Nat.card_eq_fintype_card]

private theorem card_addMonoidHom_zmod_prime_pow_le_pow_factorization (G : Type) [AddCommGroup G] [Finite G] (l ν : ℕ) (hl : l.Prime) :
    Nat.card (G →+ ZMod (l ^ ν)) ≤ l ^ (Nat.card G).factorization l := by
  haveI : NeZero (l ^ ν) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have hn0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hcop : l.Coprime (Nat.card G / l ^ (Nat.card G).factorization l) := Nat.coprime_ordCompl hl hn0
  have hnm := Nat.ordProj_mul_ordCompl_eq_self (Nat.card G) l
  set e := (Nat.card G).factorization l
  set m := Nat.card G / l ^ e
  let H := (nsmulAddMonoidHom (α := G) m).range
  haveI : Finite (H →+ ZMod (l ^ ν)) := Finite.of_injective _ DFunLike.coe_injective
  have hres : Function.Injective (fun ψ : G →+ ZMod (l ^ ν) => ψ.comp H.subtype) := by
    intro ψ₁ ψ₂ h
    ext x
    have hx : ψ₁ (m • x) = ψ₂ (m • x) := by
      have := DFunLike.congr_fun h ⟨m • x, x, rfl⟩
      simpa using this
    rw [map_nsmul, map_nsmul, nsmul_eq_mul, nsmul_eq_mul] at hx
    have hu : IsUnit ((m : ZMod (l ^ ν))) :=
      (ZMod.unitOfCoprime m (Nat.Coprime.pow_left ν hcop).symm).isUnit
    exact hu.mul_left_cancel hx
  have h1 : Nat.card (G →+ ZMod (l ^ ν)) ≤ Nat.card (H →+ ZMod (l ^ ν)) :=
    Nat.card_le_card_of_injective _ hres
  have h2 := card_addMonoidHom_zmod_le_card H (l ^ ν)
  have hkill : ∀ h : H, (l ^ e) • h = 0 := by
    rintro ⟨_, x, rfl⟩
    apply Subtype.ext
    simp only [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero, nsmulAddMonoidHom_apply]
    rw [smul_smul, hnm]
    exact card_nsmul_eq_zero'
  have hcopH : (Nat.card H).Coprime m := by
    apply Nat.coprime_of_dvd
    intro k hk hkH hkm
    haveI := Fact.mk hk
    obtain ⟨h, hh⟩ := exists_prime_addOrderOf_dvd_card' k hkH
    have hk' : k ∣ l ^ e := hh ▸ addOrderOf_dvd_of_nsmul_eq_zero (hkill h)
    have : k = l := (Nat.prime_dvd_prime_iff_eq hk hl).1 (hk.dvd_of_dvd_pow hk')
    subst this
    exact (Nat.Prime.coprime_iff_not_dvd hk).1 hcop hkm
  have hdvd : Nat.card H ∣ l ^ e := by
    have := AddSubgroup.card_addSubgroup_dvd_card H
    rw [← hnm] at this
    exact hcopH.dvd_of_dvd_mul_right this
  exact h1.trans (h2.trans (Nat.le_of_dvd (pow_pos hl.pos _) hdvd))

theorem UpperTheory.V.ZK.Ct.eqHomLe :
    ∀ (L F : Type) [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] (γ : F ≃ₐ[L] F) (a l ν : ℕ) (D : Dat (Additive Fˣ) (HeightOneSpectrum (𝓞 F) →₀ ℤ)), l.Prime → IsDat γ a D → Finite D.ClQ → Finite (EqHom γ a (l ^ ν)) ∧ Nat.card (EqHom γ a (l ^ ν)) ≤ l ^ (Nat.card D.ClQ).factorization l := by
  classical
  intro L F _ _ _ _ _ γ a l ν D hl hD hfin
  haveI : NeZero (l ^ ν) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have hinv : ∀ Q, actP γ⁻¹ (actP γ Q) = Q := fun Q => by
    simpa using actP_actP_inv' γ⁻¹ Q
  have hsingle : ∀ (P : HeightOneSpectrum (𝓞 F)) (n : ℤ),
      D.gI (Finsupp.single P n) = Finsupp.single (actP γ⁻¹ P) n := by
    intro P n
    ext Q
    rw [hD.gI_eq, Finsupp.single_apply, Finsupp.single_apply]
    have hiff : (P = actP γ Q) ↔ (actP γ⁻¹ P = Q) :=
      ⟨fun h => h ▸ hinv Q, fun h => h ▸ (actP_actP_inv' γ P).symm⟩
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (hiff.1 h1) h2
    · exact absurd (hiff.2 h2) h1
    · rfl
  let ψ0 : (HeightOneSpectrum (𝓞 F) → ZMod (l ^ ν)) → ((HeightOneSpectrum (𝓞 F) →₀ ℤ) →+ ZMod (l ^ ν)) :=
    fun φ => Finsupp.liftAddHom fun P => (AddMonoidHom.mulRight (φ P)).comp (Int.castAddHom (ZMod (l ^ ν)))
  have hψs : ∀ φ P (n : ℤ), ψ0 φ (Finsupp.single P n) = (n : ZMod (l ^ ν)) * φ P := by
    intro φ P n
    simp [ψ0]
  have hle : ∀ φ ∈ EqHom γ a (l ^ ν),
      LinearMap.range D.d ⊔ LinearMap.range D.delI ≤ LinearMap.ker (ψ0 φ).toIntLinearMap := by
    intro φ hφ
    apply sup_le
    · rintro _ ⟨y, rfl⟩
      rw [LinearMap.mem_ker, AddMonoidHom.coe_toIntLinearMap]
      have h1 := hφ.1 (Additive.toMul y)
      rw [← h1]
      simp only [ψ0, Finsupp.liftAddHom_apply, Finsupp.sum]
      rw [finsum_eq_sum_of_support_subset]
      · apply Finset.sum_congr rfl
        intro P _
        simp [← hD.d_eq]
      · intro P hP
        rw [Function.mem_support] at hP
        rw [Finset.mem_coe, Finsupp.mem_support_iff]
        intro h0
        apply hP
        rw [← hD.d_eq]
        simp [h0]
    · have key : ∀ 𝔡, ψ0 φ (D.gI 𝔡) = (a : ZMod (l ^ ν)) * ψ0 φ 𝔡 := by
        intro 𝔡
        induction 𝔡 using Finsupp.induction_linear with
        | zero => simp
        | add f g hf hg => rw [map_add (f := _), map_add (f := _), map_add (f := _), hf, hg, mul_add]
        | single P n =>
          rw [hsingle, hψs, hψs, hφ.2 P]
          ring
      rintro _ ⟨𝔡, rfl⟩
      rw [LinearMap.mem_ker, AddMonoidHom.coe_toIntLinearMap]
      simp only [Dat.delI, LinearMap.sub_apply, map_sub, key, hD.a_eq]
      simp
  let f : EqHom γ a (l ^ ν) → (D.ClQ →+ ZMod (l ^ ν)) := fun φ =>
    ((LinearMap.range D.d ⊔ LinearMap.range D.delI).liftQ (ψ0 φ.1).toIntLinearMap (hle φ.1 φ.2)).toAddMonoidHom
  have hf : Function.Injective f := by
    intro φ₁ φ₂ h
    apply Subtype.ext
    funext P
    have := DFunLike.congr_fun h (Submodule.Quotient.mk (Finsupp.single P 1))
    simpa [f, hψs] using this
  haveI : Finite (D.ClQ →+ ZMod (l ^ ν)) := Finite.of_injective _ DFunLike.coe_injective
  refine ⟨Finite.of_injective f hf, ?_⟩
  exact (Nat.card_le_card_of_injective f hf).trans (card_addMonoidHom_zmod_prime_pow_le_pow_factorization D.ClQ l ν hl)
end
