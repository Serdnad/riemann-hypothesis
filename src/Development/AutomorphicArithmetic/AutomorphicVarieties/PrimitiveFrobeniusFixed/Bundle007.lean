module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.DecGen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.GalBasic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.SplitProd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PlaceBasic
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
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

private theorem chi_dvd (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (O : Type)
    [CommRing O] [Algebra ℤ_[l] O] (n : ℕ) (g : G ℚ Ω) (h : g ∈ fixMu ℚ Ω (l ^ n)) :
    (l : O) ^ n ∣ (chiO ℚ Ω l O g : O) - 1 := by
  have hl : l.Prime := Fact.out
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hl.ne_zero⟩
  haveI : Fact (1 < l ^ n) := ⟨Nat.one_lt_pow hn.ne' hl.one_lt⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : NeZero (l : Ω) := ⟨Nat.cast_ne_zero.mpr hl.ne_zero⟩
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  have h1 : (1 : ZMod (l ^ n)) = modularCyclotomicCharacter Ω
      (HasEnoughRootsOfUnity.natCard_rootsOfUnity Ω (l ^ n)) (MulSemiringAction.toRingAut (G ℚ Ω) Ω g) := by
    apply modularCyclotomicCharacter.unique
    intro t ht
    rw [ZMod.val_one, pow_one]
    rw [mem_rootsOfUnity] at ht
    exact h (t : Ω) (by rw [← Units.val_pow_eq_pow_val, ht, Units.val_one])
  have h2 : (cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G ℚ Ω) Ω g)).val.toZModPow n = 1 := by
    rw [cyclotomicCharacter.toZModPow, ← h1]
  have h3 : (l : ℤ_[l]) ^ n ∣ (cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G ℚ Ω) Ω g)).val - 1 := by
    rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, h2, map_one, sub_self]
  have h4 := map_dvd (algebraMap ℤ_[l] O) h3
  simpa [chiO, cycZ] using h4

theorem UpperTheory.V.ML.step :
    Rec → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (N₀ m F N q : ℕ) (α : G ℚ Ω →* Oˣ), Dat l N₀ m F α → F ∣ N → N ≠ 0 → q.Prime → q ≡ 1 [MOD F] →
    ∀ ν : G ℚ Ω → QO l O, IsNu (l ^ m) F (N * q) (dualChar l α) ν → ∀ (δ : G ℚ Ω) (a₀ a : O) (w₀ : QO l O), a₀ ∣ a → a ∣ (l : O) ^ m → (∀ y : O, y • w₀ = 0 ↔ a ∣ y) →
    (∀ u ∈ fixMu ℚ Ω F, a • ν u = 0) → ∀ c ∈ ShT (QO l O) α δ F a₀,
    (∀ A : ValuationSubring Ω, Over A N → ¬ Over A F → ¬ Over A q → ∀ g ∈ Dec (F := ℚ) A, c g = 0) →
    ∀ A : ValuationSubring Ω, Over A q → ∀ g ∈ Dec (F := ℚ) A, ∀ τ ∈ Ine (F := ℚ) A, ∀ y : O, ν τ = y • w₀ → y • c g = 0 := by
  intro hRec Ω _ _ _ l _ O _ _ _ _ _ N₀ m F N q α hD hFN hN hq hq1 ν hν δ a₀ a w₀ ha₀a hal hw₀ hνa c hc hyp A hA g hg τ hτ y hy
  obtain ⟨⟨hlc, hcoc⟩, -, hac0, hunrc, hlocc⟩ := hc
  have hl : l.Prime := Fact.out
  have hF : F ≠ 0 := by
    rintro rfl
    exact hN (zero_dvd_iff.mp hFN)
  have hlmF : l ^ m ∣ F := Dvd.intro_left N₀ hD.lev.symm
  have hlF : l ∣ F := (dvd_pow_self l (by have := hD.pos; omega)).trans hlmF
  have hlN : l ∣ N := hlF.trans hFN
  have hql : q ≠ l := by
    intro hql
    have h := hq1.of_dvd hlF
    rw [hql] at h
    unfold Nat.ModEq at h
    rw [Nat.mod_self, Nat.mod_eq_of_lt hl.one_lt] at h
    exact absurd h (by norm_num)
  obtain ⟨-, hopen, -, -, -, -, -, -, -, -⟩ := galBasic Ω F hF
  obtain ⟨-, hfrobEx, hoverMul, hcopNot, hIne, -, hPows, -, hplace, -⟩ := placeBasic Ω
  have hcop : q.Coprime F := hq1.gcd_eq.trans (Nat.gcd_one_left F)
  have hAF : ¬Over A F := hcopNot A q F hcop hA
  have hIneA : Ine A ≤ fixMu ℚ Ω F := hIne A F hAF
  have hdivA : ∀ x ∈ fixMu ℚ Ω F, a ∣ (α x : O) - 1 := fun x hx => hal.trans (hD.triv x hx)
  have hl0 : (l : O) ≠ 0 := by
    obtain ⟨hinj, -⟩ := dvrFacts l O
    intro h0
    have h1 : algebraMap ℤ_[l] O (l : ℤ_[l]) = algebraMap ℤ_[l] O 0 := by simpa using h0
    exact (Nat.cast_ne_zero.mpr hl.ne_zero : (l : ℤ_[l]) ≠ 0) (hinj h1)
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact pow_ne_zero m hl0 (zero_dvd_iff.mp hal)
  let S : Subgroup (G ℚ Ω) :=
    { carrier := {x | a ∣ (α x : O) - 1}
      mul_mem' := fun {x z} hx hz => by
        have e : (α (x * z) : O) - 1 = (α x : O) * ((α z : O) - 1) + ((α x : O) - 1) := by
          rw [map_mul, Units.val_mul]; ring
        show a ∣ (α (x * z) : O) - 1
        rw [e]
        exact dvd_add (dvd_mul_of_dvd_right hz _) hx
      one_mem' := by
        show a ∣ (α 1 : O) - 1
        simp
      inv_mem' := fun {x} hx => by
        have hxx : (α x⁻¹ : O) * (α x : O) = 1 := by
          rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
        have e : (α x⁻¹ : O) - 1 = -(α x⁻¹ : O) * ((α x : O) - 1) := by
          linear_combination hxx
        show a ∣ (α x⁻¹ : O) - 1
        rw [e]
        exact dvd_mul_of_dvd_right hx _ }
  have hSo : IsOpen {x : G ℚ Ω | a ∣ (α x : O) - 1} :=
    Subgroup.isOpen_mono (H₁ := fixMu ℚ Ω F) (H₂ := S) (fun x hx => hdivA x hx) hopen
  obtain ⟨φ, hφ⟩ := hfrobEx A q hq hA
  have hφF : φ ∈ fixMu ℚ Ω F := by
    intro z hz
    rw [hPows A q F φ hφ hAF z hz, pow_eq_pow_mod q hz, hq1, ← pow_eq_pow_mod 1 hz, pow_one]
  obtain ⟨v, hv, hnv, -⟩ := hplace A q hq hA
  have hfr : IsFrob A (normV v) φ := by rw [hnv]; exact hφ
  have hDecA : Dec A ≤ fixMu ℚ Ω F := Kum.decGen ℚ Ω A v φ (fixMu ℚ Ω F) hv hfr hopen hIneA hφF
  obtain ⟨δ', hδ'⟩ := hD.notCyc
  have hβ : IsUnit (((dualChar l α) δ' : O) - 1) := by
    have hu : (((α δ')⁻¹ : Oˣ) : O) * (α δ' : O) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have e : ((dualChar l α) δ' : O) - 1 =
        -(((α δ')⁻¹ : Oˣ) : O) * ((α δ' : O) - (chiO ℚ Ω l O δ' : O)) := by
      simp only [dualChar, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul]
      linear_combination hu
    rw [e]
    exact (Units.isUnit _).neg.mul hδ'
  obtain ⟨n, hncoc, hnν, hnform⟩ := ext Ω O (QO l O) (l ^ m) F (N * q) hF (dualChar l α) ν hν δ' hβ
  have han : ∀ x, a • n x = 0 := by
    intro x
    obtain ⟨u, hu, z, hz⟩ := hnform x
    rw [hz, smul_comm, hνa u hu, smul_zero]
  have hac : ∀ x, a • c x = 0 := by
    intro x
    obtain ⟨k, hk⟩ := ha₀a
    rw [hk, mul_comm, mul_smul, hac0, smul_zero]
  have hnotF : ∀ B : ValuationSubring Ω, ¬Over B (N * q) → ¬Over B F := by
    intro B hB hBF
    obtain ⟨k, hk⟩ := hFN
    exact hB ((hoverMul B N q).mpr (Or.inl (by rw [hk]; exact (hoverMul B F k).mpr (Or.inl hBF))))
  have hunr : ∀ B : ValuationSubring Ω, ¬Over B (N * q) → ∀ x ∈ Ine B,
      a ∣ (α x : O) - 1 ∧ c x = 0 ∧ n x = 0 := by
    intro B hB x hx
    have hBF := hnotF B hB
    have hxF := hIne B F hBF hx
    exact ⟨hdivA x hxF, hunrc B hBF x hx, by rw [hnν x hxF]; exact hν.unr B hB x hx⟩
  have hloc : ∀ B : ValuationSubring Ω, Over B N → ¬Over B q →
      ∃ w, a • w = 0 ∧ ∀ x ∈ Dec B, c x = (α x : O) • w - w := by
    intro B hBN hBq
    by_cases hBF : Over B F
    · obtain ⟨w, hw, hw'⟩ := hlocc B hBF
      obtain ⟨k, hk⟩ := ha₀a
      exact ⟨w, by rw [hk, mul_comm, mul_smul, hw, smul_zero], hw'⟩
    · exact ⟨0, smul_zero _, fun x hx => by rw [hyp B hBN hBF hBq x hx, smul_zero, sub_zero]⟩
  have hdec : ∀ x ∈ Dec A, a ∣ (α x : O) - 1 ∧ a ∣ ((dualChar l α) x : O) - 1 := by
    intro x hx
    have hxF := hDecA hx
    refine ⟨hdivA x hxF, ?_⟩
    have hxl : x ∈ fixMu ℚ Ω (l ^ m) := fixMu_le ℚ Ω hlmF hxF
    have h1 := chi_dvd Ω l O m x hxl
    have h2 := hdivA x⁻¹ (inv_mem hxF)
    have e : ((dualChar l α) x : O) - 1 =
        (chiO ℚ Ω l O x : O) * ((α x⁻¹ : O) - 1) + ((chiO ℚ Ω l O x : O) - 1) := by
      simp only [dualChar, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, map_inv]
      ring
    rw [e]
    exact dvd_add (dvd_mul_of_dvd_right h2 _) (hal.trans h1)
  have hine : ∀ x ∈ Ine A, c x = 0 := fun x hx => hunrc A hAF x hx
  have hnτ : n τ = y • w₀ := by rw [hnν τ (hIneA hτ)]; exact hy
  exact hRec Ω l hD.odd_l O α a ha0 w₀ hw₀ hSo N q hN hlN hq hql c n ⟨hlc, hcoc⟩ hncoc hac han hunr hloc
    A hA hdec hine g hg τ hτ y hnτ
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

private theorem val_int {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) {r : 𝓞 E} (hr : r ≠ 0) :
    v.valuation E (algebraMap (𝓞 E) E r) = WithZero.exp (-FractionalIdeal.count E v
      (FractionalIdeal.spanSingleton (𝓞 E)⁰ (algebraMap (𝓞 E) E r))) := by
  classical
  have hr' : algebraMap (𝓞 E) E r ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr hr
  have hI : FractionalIdeal.spanSingleton (𝓞 E)⁰ (algebraMap (𝓞 E) E r) ≠ 0 := by
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
    exact hr'
  have h : FractionalIdeal.spanSingleton (𝓞 E)⁰ (algebraMap (𝓞 E) E r) =
      FractionalIdeal.spanSingleton (𝓞 E)⁰ ((algebraMap (𝓞 E) E 1)⁻¹) * ↑(Ideal.span {r}) := by
    rw [map_one, inv_one, FractionalIdeal.spanSingleton_one, one_mul,
      FractionalIdeal.coeIdeal_span_singleton]
  rw [FractionalIdeal.count_well_defined E v hI h, HeightOneSpectrum.valuation_of_algebraMap,
    v.intValuation_if_neg hr, Ideal.span_singleton_one, ← Ideal.one_eq_top, Associates.mk_one,
    Associates.factors_one, Associates.count_zero v.associates_irreducible]
  simp

private theorem val_count {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) {α : E} (hα : α ≠ 0) :
    v.valuation E α = WithZero.exp (-FractionalIdeal.count E v
      (FractionalIdeal.spanSingleton (𝓞 E)⁰ α)) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (𝓞 E) α
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hα
  have hb' : algebraMap (𝓞 E) E b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr hb0
  have ha' : algebraMap (𝓞 E) E a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr ha0
  have hIa : FractionalIdeal.spanSingleton (𝓞 E)⁰ (algebraMap (𝓞 E) E a) ≠ 0 := by
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
    exact ha'
  have hIb : (FractionalIdeal.spanSingleton (𝓞 E)⁰ (algebraMap (𝓞 E) E b))⁻¹ ≠ 0 := by
    rw [Ne, inv_eq_zero, FractionalIdeal.spanSingleton_eq_zero_iff]
    exact hb'
  rw [div_eq_mul_inv, ← FractionalIdeal.spanSingleton_mul_spanSingleton, ← FractionalIdeal.spanSingleton_inv,
    FractionalIdeal.count_mul E v hIa hIb, FractionalIdeal.count_inv, map_mul, map_inv₀,
    val_int v ha0, val_int v hb0, neg_add, neg_neg, WithZero.exp_add]
  rw [← WithZero.exp_neg, neg_neg]

private theorem count_fam {E ι : Type} [Field E] [NumberField E] [Fintype ι]
    (P : ι → HeightOneSpectrum (𝓞 E)) (hP : Function.Injective P) (k : ι → ℤ) (t : ι) :
    FractionalIdeal.count E (P t) (∏ s, (((P s).asIdeal : FractionalIdeal (𝓞 E)⁰ E)) ^ k s) = k t := by
  classical
  rw [FractionalIdeal.count_prod E (P t) _ _ fun s _ =>
    zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.2 (P s).ne_bot)]
  rw [Finset.sum_eq_single t]
  · exact FractionalIdeal.count_zpow_self E (P t) _
  · intro s _ hs
    rw [FractionalIdeal.count_zpow, FractionalIdeal.count_maximal_coprime E (P t) fun h => hs (hP h), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ t) h

theorem UpperTheory.valuation_kummerElement_at_conjugate_prime :
    ∀ (M : ℕ) [NeZero M] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] (b r : ℕ) (v w : HeightOneSpectrum (𝓞 K)) (X : K) (t : (ZMod M)ˣ), r.Prime → r ≡ 1 [MOD M] → IsX M K b v.asIdeal X → (r : 𝓞 K) ∈ v.asIdeal → w.asIdeal = conjI M K v.asIdeal t → w.valuation K X = w.valuation K (r : K) ^ th M b t := by
  intro M _ K _ _ _ b r v w X t hr hr1 hX hrv hw
  haveI : Fact r.Prime := ⟨hr⟩
  have hndvd : ¬ r ∣ M := by
    intro hd
    have h1 : M ∣ r - 1 := (Nat.modEq_iff_dvd' hr.one_le).mp hr1.symm
    have h2 : r ∣ r - 1 := Nat.dvd_trans hd h1
    have h3 : 0 < r - 1 := by have := hr.two_le; omega
    have := Nat.le_of_dvd h3 h2
    have := hr.two_le
    omega
  have hcop : r.Coprime M := (Nat.Prime.coprime_iff_not_dvd hr).mpr hndvd
  haveI hlies : v.asIdeal.LiesOver (Ideal.span {(r : ℤ)}) := by
    constructor
    have hmax : (Ideal.span {(r : ℤ)}).IsMaximal :=
      ((Ideal.span_singleton_prime (by exact_mod_cast hr.ne_zero)).mpr
        (Nat.prime_iff_prime_int.mp hr)).isMaximal (by simp [hr.ne_zero])
    refine hmax.eq_of_le (Ideal.IsPrime.comap _).ne_top ?_
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show algebraMap ℤ (𝓞 K) (r : ℤ) ∈ v.asIdeal
    simpa using hrv
  have hdeg : v.asIdeal.inertiaDeg ℤ = 1 := by
    rw [IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd r K v.asIdeal hndvd]
    have : (r : ZMod M) = 1 := by
      have := (ZMod.natCast_eq_natCast_iff r 1 M).mpr hr1
      simpa using this
    rw [this, orderOf_one]
  have hnorm : Ideal.absNorm v.asIdeal = r := by
    rw [← Ideal.absNorm_pow_inertiaDeg (Ideal.span {(r : ℤ)}) v.asIdeal, hdeg, pow_one]
    simp [Ideal.absNorm_span_singleton]
  obtain ⟨π, hπ⟩ := (red K r v.asIdeal).1 hnorm
  obtain ⟨hprime, hprod⟩ := splitProd M K r π hcop
  have hinj := splitInj M K r π hcop
  rw [hπ] at hprime hprod hinj
  let fam : (ZMod M)ˣ → HeightOneSpectrum (𝓞 K) := fun s =>
    ⟨conjI M K v.asIdeal s, Ideal.isPrime_of_prime (hprime s), (hprime s).ne_zero⟩
  have hfam : Function.Injective fam := by
    intro s s' h
    exact hinj (congrArg HeightOneSpectrum.asIdeal h)
  obtain rfl : w = fam t := HeightOneSpectrum.ext hw
  have hX0 : X ≠ 0 := left_ne_zero_of_mul_eq_one hX.1
  have hr0 : (r : 𝓞 K) ≠ 0 := by exact_mod_cast hr.ne_zero
  have hrK : (r : K) = algebraMap (𝓞 K) K (r : 𝓞 K) := by simp
  rw [val_count (fam t) hX0, hX.2, hrK, val_int (fam t) hr0,
    ← FractionalIdeal.coeIdeal_span_singleton, ← hprod]
  have hcoe : ((∏ s, conjI M K v.asIdeal s : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) =
      ∏ s, (((fam s).asIdeal : FractionalIdeal (𝓞 K)⁰ K)) ^ ((fun _ => (1 : ℤ)) s) := by
    simp only [zpow_one]
    exact map_prod (FractionalIdeal.coeIdealHom (𝓞 K)⁰ K) _ _
  have hX2 : (∏ s, ((conjI M K v.asIdeal s : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ^ th M b (s : ZMod M)) =
      ∏ s, (((fam s).asIdeal : FractionalIdeal (𝓞 K)⁰ K)) ^ ((fun s : (ZMod M)ˣ => th M b (s : ZMod M)) s) := rfl
  rw [hcoe, hX2, count_fam fam hfam, count_fam fam hfam, ← WithZero.exp_zsmul]
  simp
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

private theorem val_eq_one_of_pow {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {M : ℕ} (hM : M ≠ 0) {x : Ω}
    (h : A.valuation (x ^ M) = 1) : A.valuation x = 1 := by
  rw [map_pow] at h
  rcases lt_trichotomy (A.valuation x) 1 with h1 | h1 | h1
  · exact absurd h (pow_lt_one₀ zero_le h1 hM).ne
  · exact h1
  · exact absurd h (one_lt_pow₀ h1 hM).ne'

theorem UpperTheory.V.ML.kolUnr :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (M F n r a : ℕ) [NeZero M], F * n ≠ 0 → M ∣ F → ∀ (ζ : Ω), IsPrimitiveRoot ζ M → ∀ δ : G ℚ Ω, Pows M a δ → ∀ y : Ω, y ≠ 0 → (∀ h ∈ fixMu ℚ Ω (F * n), h y = y) →
    (∀ A : ValuationSubring Ω, ¬ Over A r → A.valuation y = 1) → ∀ κ : G ℚ Ω → ZMod M, IsKol M F n ζ δ a y κ →
    ∀ A : ValuationSubring Ω, ¬ Over A (F * r * n) → ∀ g ∈ Ine (F := ℚ) A, κ g = 0 := by
  intro Ω _ _ _ M F n r a _ hFn hMF ζ hζ δ hδ y hy hfix hunit κ hκ A hA g hg
  obtain ⟨-, -, hmul, -, hine, hroot, -, -, -, hconj⟩ := placeBasic Ω
  have hM : M ≠ 0 := NeZero.ne M
  have hA1 : ¬ Over A (F * n) := fun h => hA <| by
    rw [mul_right_comm]
    exact (hmul A _ _).2 (Or.inl h)
  have hAr : ¬ Over A r := fun h => hA <| (hmul A _ _).2 (Or.inl ((hmul A _ _).2 (Or.inr h)))
  have hAF : ¬ Over A F := fun h => hA1 ((hmul A _ _).2 (Or.inl h))
  have hAM : ¬ Over A M := fun h => hAF <| by
    obtain ⟨c, rfl⟩ := hMF
    exact (hmul A _ _).2 (Or.inl h)
  have hgFn : g ∈ fixMu ℚ Ω (F * n) := hine A _ hA1 hg
  have hgF : g ∈ fixMu ℚ Ω F := hine A _ hAF hg
  obtain ⟨Y, hY, -⟩ := id hκ
  have key := (kolHom Ω M F n a hFn hMF ζ hζ δ hδ y hy hfix κ hκ).2.2 Y hY g hgF 1
    (by rw [hfix g hgFn, one_pow, div_self hy])
  have h1 : opP δ a (1 : Ω) = 1 := by simp [opP]
  rw [h1, div_one] at key
  have hvY : A.valuation Y = 1 := val_eq_one_of_pow A hM (by rw [hY]; exact hunit A hAr)
  have hvδ : A.valuation (δ Y) = 1 := by
    refine val_eq_one_of_pow A hM ?_
    rw [← map_pow δ, hY]
    have hB : ¬ Over (δ⁻¹ • A) r := fun h => hAr <| by
      have := ((hconj A δ⁻¹).2.2.2.1 (r : Ω)).1 (by rw [map_natCast]; exact h)
      exact this
    have := ((hconj (δ⁻¹ • A) δ).2.2.2.2 y).2 (hunit _ hB)
    rwa [smul_inv_smul] at this
  have hu : A.valuation (opP δ a Y) = 1 := by
    rw [opP, map_div₀, map_pow, hvY, hvδ, one_pow, div_one]
  have hu0 : opP δ a Y ≠ 0 := fun h => by
    rw [h, map_zero] at hu
    exact zero_ne_one hu
  have hlt : A.valuation (ζ ^ (κ g).val - 1) < 1 := by
    have e : ζ ^ (κ g).val - 1 = (g (opP δ a Y) - opP δ a Y) / opP δ a Y := by
      rw [key, sub_div, div_self hu0]
    rw [e, map_div₀, hu, div_one]
    exact hg.2 _ hu.le
  have h2 : ζ ^ (κ g).val = 1 := hroot A M _ hAM (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]) hlt
  have h3 : M ∣ (κ g).val := (hζ.pow_eq_one_iff_dvd _).1 h2
  exact (ZMod.val_eq_zero _).1 (Nat.eq_zero_of_dvd_of_lt h3 (ZMod.val_lt _))
end
