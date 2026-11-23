module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.DecGen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.GalBasic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.LenDirected
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PlaceBasic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

private theorem ordv_prime (r : ℕ) (hr : r.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : (r : 𝓞 ℚ) ∈ v.asIdeal)
    (a : ℚˣ) (ha : (a : ℚ) = r) : UpperTheory.V.Kum.ordv v a = 1 := by
  have hpr : Prime (r : 𝓞 ℚ) := by
    have h1 : Prime ((Rat.ringOfIntegersEquiv : 𝓞 ℚ ≃+* ℤ) (r : 𝓞 ℚ)) := by
      rw [map_natCast]
      exact Nat.prime_iff_prime_int.mp hr
    exact (MulEquiv.prime_iff (Rat.ringOfIntegersEquiv : 𝓞 ℚ ≃+* ℤ).toMulEquiv).mp h1
  have hne : (r : 𝓞 ℚ) ≠ 0 := hpr.ne_zero
  have hspan : v.asIdeal = Ideal.span {(r : 𝓞 ℚ)} := by
    have hP : (Ideal.span {(r : 𝓞 ℚ)}).IsPrime := (Ideal.span_singleton_prime hne).mpr hpr
    have hbot : Ideal.span {(r : 𝓞 ℚ)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact hne
    have hmax := hP.isMaximal hbot
    have hle : Ideal.span {(r : 𝓞 ℚ)} ≤ v.asIdeal := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact hv
    exact (hmax.eq_of_le v.isPrime.ne_top hle).symm
  have hint : v.intValuation (r : 𝓞 ℚ) = WithZero.exp (-1 : ℤ) := v.intValuation_singleton hne hspan
  have hval : ((v.valuationOfNeZero a : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuationOfNeZero_eq, ha, ← hint]
    have : ((r : ℚ)) = algebraMap (𝓞 ℚ) ℚ (r : 𝓞 ℚ) := by simp
    rw [this, HeightOneSpectrum.valuation_of_algebraMap]
  have h2 : v.valuationOfNeZero a = Multiplicative.ofAdd (-1 : ℤ) := by
    apply WithZero.coe_injective
    rw [hval]
    rfl
  unfold UpperTheory.V.Kum.ordv
  rw [h2]
  simp

theorem UpperTheory.V.ML.ineRad :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (r M : ℕ), r.Prime → M.Coprime r → ∀ A : ValuationSubring Ω, Over A r → ∀ ρ ζ : Ω, ρ ^ M = (r : Ω) → ζ ^ M = 1 → ∃ t ∈ Ine (F := ℚ) A, t ρ = ζ * ρ := by
  intro Ω _ _ _ r M hr hM A hA ρ ζ hρ hζ
  have pb := placeBasic Ω
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hr0 : (r : Ω) ≠ 0 := by exact_mod_cast hr.ne_zero
  have hM0 : M ≠ 0 := by
    rintro rfl
    simp [Nat.coprime_zero_left] at hM
    exact hr.ne_one hM
  haveI : NeZero M := ⟨hM0⟩
  have hρ0 : ρ ≠ 0 := by
    rintro rfl
    rw [zero_pow hM0] at hρ
    exact hr0 hρ.symm
  have hnot : ¬ Over A M := fun h => pb.2.2.2.1 A M r hM h hA
  have hfix : Ine (F := ℚ) A ≤ fixMu ℚ Ω M := pb.2.2.2.2.1 A M hnot
  have hroot : ∀ g : G ℚ Ω, (g ρ / ρ) ^ M = 1 := by
    intro g
    rw [div_pow, ← map_pow, hρ, map_natCast, div_self hr0]
  have hgne : ∀ g : G ℚ Ω, g ρ / ρ ≠ 0 := fun g =>
    div_ne_zero (by simpa using hρ0) hρ0
  let χ : ↥(Ine (F := ℚ) A) →* Ωˣ :=
    { toFun := fun g => Units.mk0 ((g : G ℚ Ω) ρ / ρ) (hgne g)
      map_one' := by
        ext
        simp [div_self hρ0]
      map_mul' := by
        intro g h
        ext
        have hc : (g : G ℚ Ω) ((h : G ℚ Ω) ρ / ρ) = (h : G ℚ Ω) ρ / ρ :=
          hfix g.2 _ (hroot h)
        have hh : (h : G ℚ Ω) ρ = ((h : G ℚ Ω) ρ / ρ) * ρ := by
          field_simp
        simp only [Subgroup.coe_mul, Units.val_mk0, Units.val_mul, AlgEquiv.mul_apply]
        rw [hh, map_mul, hc]
        field_simp }
  have hχ : ∀ g, ((χ g : Ωˣ) : Ω) = (g : G ℚ Ω) ρ / ρ := fun g => rfl
  have hle : χ.range ≤ rootsOfUnity M Ω := by
    rintro _ ⟨g, rfl⟩
    rw [mem_rootsOfUnity]
    ext
    rw [Units.val_pow_eq_pow_val, hχ, hroot, Units.val_one]
  haveI : Finite χ.range :=
    Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  have hd0 : 0 < Nat.card χ.range := Nat.card_pos
  have hfixd : ∀ g ∈ Ine (F := ℚ) A, g (ρ ^ Nat.card χ.range) = ρ ^ Nat.card χ.range := by
    intro g hg
    have h1 := congrArg (fun x : χ.range => ((x : Ωˣ) : Ω))
      (pow_card_eq_one' (x := (⟨χ ⟨g, hg⟩, ⟨_, rfl⟩⟩ : χ.range)))
    simp only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, hχ, OneMemClass.coe_one,
      Units.val_one] at h1
    rw [div_pow, div_eq_one_iff_eq (pow_ne_zero _ hρ0)] at h1
    rw [map_pow]
    exact h1
  obtain ⟨v, hvA, -, hvr⟩ := pb.2.2.2.2.2.2.2.2.1 A r hr hA
  let a : ℚˣ := Units.mk0 (r : ℚ) (by exact_mod_cast hr.ne_zero)
  have ha1 : UpperTheory.V.Kum.ordv v a = 1 := ordv_prime r hr v hvr a rfl
  have hpow : UpperTheory.V.Kum.ordv v (a ^ Nat.card χ.range) = Nat.card χ.range := by
    unfold UpperTheory.V.Kum.ordv at ha1 ⊢
    rw [map_pow, toAdd_pow, nsmul_eq_mul, ← mul_neg, ha1, mul_one]
  have hdv := UpperTheory.V.Kum.dvdOfIne ℚ Ω M A v (ρ ^ Nat.card χ.range) (a ^ Nat.card χ.range) hvA
    (by
      rw [← pow_mul, mul_comm, pow_mul, hρ]
      simp [a]) hfixd
  rw [hpow] at hdv
  have hMd : M ∣ Nat.card χ.range := by exact_mod_cast hdv
  have hMle : M ≤ Nat.card χ.range := Nat.le_of_dvd hd0 hMd
  have hcard : Nat.card χ.range ≤ Nat.card (rootsOfUnity M Ω) := Subgroup.card_le_of_le hle
  have heq : χ.range = rootsOfUnity M Ω :=
    Subgroup.eq_of_le_of_card_ge hle (le_trans (card_rootsOfUnity Ω M) hMle)
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hM0] at hζ
    exact zero_ne_one hζ
  have hu : Units.mk0 ζ hζ0 ∈ rootsOfUnity M Ω := by
    rw [mem_rootsOfUnity]
    ext
    simp [hζ]
  rw [← heq] at hu
  obtain ⟨g, hg⟩ := hu
  refine ⟨g, g.2, ?_⟩
  have h2 := congrArg Units.val hg
  rw [hχ, Units.val_mk0, div_eq_iff hρ0] at h2
  exact h2
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

theorem UpperTheory.V.ML.shtNu :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (N₀ m F : ℕ) (α : G ℚ Ω →* Oˣ), Dat l N₀ m F α → ∀ δ : G ℚ Ω, IsUnit ((α δ : O) - 1) → ∀ a : O, a ∣ (l : O) ^ m → ∀ c ∈ ShT (QO l O) α δ F a,
    IsNu (l ^ m) F F α c ∧ ((∀ u ∈ fixMu ℚ Ω F, c u = 0) → c = 0) ∧
    ∀ (q : ℕ) (A : ValuationSubring Ω) (φ : G ℚ Ω), q.Prime → q ≡ 1 [MOD F] → Over A q → IsFrob (F := ℚ) A q φ → c φ = 0 →
      ∀ A' : ValuationSubring Ω, Over A' q → ∀ g ∈ Dec (F := ℚ) A', c g = 0 := by
  intro Ω _ _ _ l _ O _ _ _ _ _ N₀ m F α hD δ hδ a ha c hc
  obtain ⟨⟨hlc, hcoc⟩, hcδ, hac, hunr, -⟩ := hc
  have hkill : ∀ x ∈ fixMu ℚ Ω F, ∀ w : QO l O, a • w = 0 → (α x : O) • w = w := by
    intro x hx w hw
    obtain ⟨t, ht⟩ := hD.triv x hx
    obtain ⟨b, hb⟩ := ha
    have h1 : ((α x : O) - 1) • w = 0 := by
      rw [ht, hb, show a * b * t = (b * t) * a by ring, mul_smul, hw, smul_zero]
    rwa [sub_smul, one_smul, sub_eq_zero] at h1
  have h1 : c 1 = 0 := by
    have e := hcoc 1 1
    simp only [mul_one, map_one, Units.val_one, one_smul] at e
    simpa using e
  have heqv : ∀ g u, u ∈ fixMu ℚ Ω F → c (g * u * g⁻¹) = (α g : O) • c u := by
    intro g u hu
    have e1 := hcoc (g * u) g⁻¹
    have e2 := hcoc g u
    have e3 := hcoc g g⁻¹
    rw [mul_inv_cancel, h1] at e3
    rw [e1, e2, map_mul, Units.val_mul, mul_smul, hkill u hu _ (hac _), add_right_comm, ← e3, zero_add]
  have hF : F ≠ 0 := by
    rw [hD.lev]
    have hl : l.Prime := Fact.out
    have hN : N₀ ≠ 0 := by
      rintro rfl
      exact hl.one_lt.ne' ((Nat.coprime_zero_left _).mp hD.cop)
    exact mul_ne_zero hN (pow_ne_zero _ hl.ne_zero)
  obtain ⟨-, hopen, hcomm, -, -, -, -, -, -, -⟩ := galBasic Ω F hF
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro u hu v _
    rw [hcoc, hkill u hu _ (hac _)]
  · exact hlc.comp_continuous continuous_subtype_val
  · exact heqv
  · intro u _
    obtain ⟨b, hb⟩ := ha
    rw [← Nat.cast_smul_eq_nsmul O, Nat.cast_pow, hb, mul_comm, mul_smul, hac, smul_zero]
  · exact hunr
  · intro hz
    refine funext fun g => ?_
    have hk := hcomm g δ
    have e : g * δ = (g * δ * g⁻¹ * δ⁻¹) * (δ * g) := by group
    have e1 := hcoc g δ
    rw [hcδ, smul_zero, add_zero, e, hcoc _ (δ * g), hz _ hk, zero_add,
      hkill _ hk _ (hac _), hcoc δ g, hcδ, zero_add] at e1
    have e2 : ((α δ : O) - 1) • c g = 0 := by rw [sub_smul, one_smul, e1, sub_self]
    exact (hδ.smul_eq_zero).mp e2
  · intro q A φ hq hq1 hA hφ hcφ A' hA' x hx
    obtain ⟨-, -, -, hcopNot, hIne, -, hPows, hconj, hplace, hact⟩ := placeBasic Ω
    have hcop : q.Coprime F := hq1.gcd_eq.trans (Nat.gcd_one_left F)
    have hAF : ¬Over A F := hcopNot A q F hcop hA
    have hφF : φ ∈ fixMu ℚ Ω F := by
      intro y hy
      rw [hPows A q F φ hφ hAF y hy, pow_eq_pow_mod q hy, hq1, ← pow_eq_pow_mod 1 hy, pow_one]
    let K : Subgroup (G ℚ Ω) :=
      { carrier := {g | g ∈ fixMu ℚ Ω F ∧ c g = 0}
        mul_mem' := fun {u v} hu hv =>
          ⟨mul_mem hu.1 hv.1, by rw [hcoc, hu.2, hkill _ hu.1 _ (hac _), hv.2, add_zero]⟩
        one_mem' := ⟨one_mem _, h1⟩
        inv_mem' := fun {u} hu => by
          refine ⟨inv_mem hu.1, ?_⟩
          have e := hcoc u u⁻¹
          rw [mul_inv_cancel, h1, hu.2, zero_add, hkill _ hu.1 _ (hac _)] at e
          exact e.symm }
    have hKo : IsOpen (K : Set (G ℚ Ω)) := hopen.inter (hlc.isOpen_fiber 0)
    have hIK : Ine A ≤ K := fun g hg => ⟨hIne A F hAF hg, hunr A hAF g hg⟩
    obtain ⟨v, hv, hnv, -⟩ := hplace A q hq hA
    have hfr : IsFrob A (normV v) φ := by rw [hnv]; exact hφ
    have hDec : Dec A ≤ K := Kum.decGen ℚ Ω A v φ K hv hfr hKo hIK ⟨hφF, hcφ⟩
    obtain ⟨g, rfl⟩ := hconj A A' q hq hA hA'
    have hy := hDec (((hact A g).1 x).mp hx)
    have ex : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [ex, heqv g _ hy.1, hy.2, smul_zero]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

section

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {O W : Type} [CommRing O] [AddCommGroup W] [Module O W]

private theorem shT_mono (α : G ℚ Ω →* Oˣ) (δ : G ℚ Ω) (F : ℕ) {a b : O} (h : a ∣ b) :
    ShT W α δ F a ≤ ShT W α δ F b := by
  obtain ⟨t, rfl⟩ := h
  rintro c ⟨h1, h2, h3, h4, h5⟩
  refine ⟨h1, h2, fun g => by rw [mul_comm, mul_smul, h3, smul_zero], h4, fun A hA => ?_⟩
  obtain ⟨m, hm, h⟩ := h5 A hA
  exact ⟨m, by rw [mul_comm, mul_smul, hm, smul_zero], h⟩

private theorem norm_coc (α : G ℚ Ω →* Oˣ) (δ : G ℚ Ω) (hδ : IsUnit ((α δ : O) - 1)) (c : G ℚ Ω → W)
    (hc : IsCoc α c) : ∃ m : W, IsCoc α (fun g => c g - ((α g : O) • m - m)) ∧ c δ - ((α δ : O) • m - m) = 0 := by
  set u := hδ.unit with hu0
  have hu : (u : O) = (α δ : O) - 1 := hδ.unit_spec
  refine ⟨((u⁻¹ : Oˣ) : O) • c δ, ⟨?_, fun g h => ?_⟩, ?_⟩
  · have hloc : IsLocallyConstant fun g : G ℚ Ω => c (g * δ) :=
      hc.1.comp_continuous (continuous_mul_const δ)
    have heq : (fun g => c g - ((α g : O) • ((u⁻¹ : Oˣ) : O) • c δ - ((u⁻¹ : Oˣ) : O) • c δ)) =
        fun g => c g - (((u⁻¹ : Oˣ) : O) • (c (g * δ) - c g) - ((u⁻¹ : Oˣ) : O) • c δ) := by
      funext g
      rw [hc.2 g δ, add_sub_cancel_left, smul_comm (α g : O)]
    rw [heq]
    exact hc.1.sub (((hloc.sub hc.1).comp fun v => ((u⁻¹ : Oˣ) : O) • v).sub
      (IsLocallyConstant.const _))
  · beta_reduce
    rw [hc.2 g h, map_mul, Units.val_mul, mul_smul]
    module
  · have e : (α δ : O) • (((u⁻¹ : Oˣ) : O) • c δ) - ((u⁻¹ : Oˣ) : O) • c δ =
        (u : O) • (((u⁻¹ : Oˣ) : O) • c δ) := by
      rw [hu, sub_smul, one_smul]
    rw [e, smul_smul, Units.mul_inv, one_smul, sub_self]

private theorem unit_kill {x : O} (hx : IsUnit x) {a : O} {w : W} (h : a • x • w = 0) : a • w = 0 := by
  obtain ⟨u, rfl⟩ := hx
  calc a • w = ((u⁻¹ : Oˣ) : O) • (a • (u : O) • w) := by
        rw [smul_comm _ a]
        simp [smul_smul]
    _ = 0 := by rw [h, smul_zero]

private theorem conj_cob (α : G ℚ Ω →* Oˣ) {c : G ℚ Ω → W} (hc : IsCoc α c) (σ x : G ℚ Ω) (m : W)
    (h : c (σ⁻¹ * x * σ) = (α (σ⁻¹ * x * σ) : O) • m - m) :
    c x = (α x : O) • ((α σ : O) • m - c σ) - ((α σ : O) • m - c σ) := by
  have hc1 : c 1 = 0 := by
    have := hc.2 1 1
    simp only [mul_one, map_one, Units.val_one, one_smul] at this
    exact left_eq_add.mp this
  have e0 : c σ⁻¹ + (α σ⁻¹ : O) • c σ = 0 := by
    rw [← hc.2, inv_mul_cancel, hc1]
  have e1 : c (σ⁻¹ * x * σ) = c σ⁻¹ + (α σ⁻¹ : O) • (c x + (α x : O) • c σ) := by
    rw [mul_assoc, hc.2, hc.2]
  have ea : (α (σ⁻¹ * x * σ) : O) = (α x : O) := by
    rw [map_mul, map_mul, map_inv]
    congr 1
    calc (α σ)⁻¹ * α x * α σ = α x * ((α σ)⁻¹ * α σ) := by ac_rfl
      _ = α x := by rw [inv_mul_cancel, mul_one]
  have hs : (α σ : O) * (α σ⁻¹ : O) = 1 := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  rw [e1, ea] at h
  linear_combination (norm := module) (α σ : O) • h - (α σ : O) • e0 - hs • (c x + (α x : O) • c σ - c σ)

private theorem dec_of_ine (α : G ℚ Ω →* Oˣ) {c : G ℚ Ω → W} (hc : IsCoc α c) (g d : G ℚ Ω) (m : W)
    (hg : IsUnit ((α g : O) - 1)) (h : c g = (α g : O) • m - m)
    (h' : c (d⁻¹ * g * d) = (α (d⁻¹ * g * d) : O) • m - m) : c d = (α d : O) • m - m := by
  have key := conj_cob α hc d g m h'
  rw [h] at key
  have e : ((α g : O) - 1) • m = ((α g : O) - 1) • ((α d : O) • m - c d) := by
    rw [sub_smul, one_smul, sub_smul, one_smul]
    exact key
  rw [hg.smul_left_cancel] at e
  linear_combination (norm := module) e

end

private theorem mem_shT (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (O : Type)
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]
    (α : G ℚ Ω →* Oˣ) (δ : G ℚ Ω) (F : ℕ)
    (h1 : ∀ A : ValuationSubring Ω, ¬ Over A F → ∀ g ∈ Ine (F := ℚ) A, α g = 1)
    (h2 : ∀ A : ValuationSubring Ω, Over A F → ¬ Over A l → ∃ g ∈ Ine (F := ℚ) A, IsUnit ((α g : O) - 1))
    (c : G ℚ Ω → QO l O) (hc : IsCoc α c) (hδ : c δ = 0)
    (hs : ∀ D ∈ shaFam ℚ Ω l, ∃ m : QO l O, ∀ g ∈ D, c g = (α g : O) • m - m) :
    ∃ a : O, a ≠ 0 ∧ c ∈ ShT (QO l O) α δ F a := by
  classical
  obtain ⟨A0, hA0⟩ := (placeBasic Ω).1 l (Fact.out : l.Prime)
  obtain ⟨m0, hm0⟩ := hs (Dec A0) (Or.inl ⟨A0, hA0, rfl⟩)
  have hfin : (Set.range c).Finite := hc.1.range_finite
  choose ann hann0 hann using (UpperTheory.V.ML.qoCyc l O).1
  let S : Finset (QO l O) := insert m0 hfin.toFinset
  refine ⟨∏ w ∈ S, ann w, Finset.prod_ne_zero_iff.mpr fun w _ => hann0 w, ?_⟩
  have kill : ∀ w ∈ S, (∏ w ∈ S, ann w) • w = 0 :=
    fun w hw => (hann w _).mpr (Finset.dvd_prod_of_mem _ hw)
  set a := ∏ w ∈ S, ann w
  have killc : ∀ g, a • c g = 0 :=
    fun g => kill _ (Finset.mem_insert_of_mem (hfin.mem_toFinset.mpr ⟨g, rfl⟩))
  have killm0 : a • m0 = 0 := kill _ (Finset.mem_insert_self _ _)
  refine ⟨hc, hδ, killc, fun A hA g hg => ?_, fun A hA => ?_⟩
  · obtain ⟨m, hm⟩ := hs (Ine A) (Or.inr ⟨A, rfl⟩)
    rw [hm g hg, h1 A hA g hg, Units.val_one, one_smul, sub_self]
  · by_cases hl : Over A l
    · obtain ⟨σ, rfl⟩ := (placeBasic Ω).2.2.2.2.2.2.2.1 A0 A l (Fact.out : l.Prime) hA0 hl
      refine ⟨(α σ : O) • m0 - c σ, ?_, fun d hd => ?_⟩
      · rw [smul_sub, smul_comm a (α σ : O) m0, killm0, smul_zero, killc, sub_zero]
      · have hd' : σ⁻¹ * d * σ ∈ Dec A0 := (((placeBasic Ω).2.2.2.2.2.2.2.2.2 A0 σ).1 d).mp hd
        exact conj_cob α hc σ d m0 (hm0 _ hd')
    · obtain ⟨g0, hg0, hu⟩ := h2 A hA hl
      obtain ⟨m, hm⟩ := hs (Ine A) (Or.inr ⟨A, rfl⟩)
      refine ⟨m, ?_, fun d hd => ?_⟩
      · have e : ((α g0 : O) - 1) • m = c g0 := by rw [hm g0 hg0, sub_smul, one_smul]
        exact unit_kill hu (by rw [e, killc])
      · have hdA : d • A = A := mem_Dec.mp hd
        have hg' : d⁻¹ * g0 * d ∈ Ine A := by
          have hh := ((placeBasic Ω).2.2.2.2.2.2.2.2.2 A d).2.1 g0
          rw [hdA] at hh
          exact hh.mp hg0
        exact dec_of_ine α hc g0 d m hu (hm g0 hg0) (hm _ hg')

theorem UpperTheory.V.ML.shaToShT :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (α : G ℚ Ω →* Oˣ) (δ : G ℚ Ω), IsUnit ((α δ : O) - 1) → ∀ F : ℕ, F ≠ 0 →
    (∀ A : ValuationSubring Ω, ¬ Over A F → ∀ g ∈ Ine (F := ℚ) A, α g = 1) →
    (∀ A : ValuationSubring Ω, Over A F → ¬ Over A l → ∃ g ∈ Ine (F := ℚ) A, IsUnit ((α g : O) - 1)) → ∀ n : ℕ∞,
    (∀ a : O, a ≠ 0 → Module.length O (ShT (QO l O) α δ F a) ≤ n) → Module.length O (ShaU (twist₂ l α) l (⊤ : Subgroup (G ℚ Ω))) ≤ n := by
  intro Ω _ _ _ l _ O _ _ _ _ _ α δ hδ F hF h1 h2 n hn
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  let T : Subgroup (G ℚ Ω) := ⊤
  let ι : Z1U (twist₂ l α) T →ₗ[O] (G ℚ Ω → QO l O) :=
    { toFun := fun z g => (z : T → QO l O) ⟨g, Subgroup.mem_top g⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hι : Function.Injective ι := by
    intro z z' h
    apply Subtype.ext
    funext u
    exact congrFun h u.1
  let Q : Z1U (twist₂ l α) T →ₗ[O] H1U (twist₂ l α) T := Submodule.mkQ _
  let P : ℕ → Submodule O (H1U (twist₂ l α) T) := fun k =>
    ((ShT (QO l O) α δ F (ϖ ^ k)).comap ι).map Q
  refine UpperTheory.V.Kum.lenDirected O (H1U (twist₂ l α) T) (ShaU (twist₂ l α) l T) P n ?_ ?_ ?_
  · intro i j hij
    exact Submodule.map_mono (Submodule.comap_mono (shT_mono α δ F (pow_dvd_pow ϖ hij)))
  · intro x hx
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hloc := UpperTheory.V.Base.mk_mem_locSel.mp hx
    obtain ⟨hzc, hzco⟩ := z.2
    set c : G ℚ Ω → QO l O := ι z with hcE
    have hcoc : IsCoc α c := by
      refine ⟨(IsLocallyConstant.iff_continuous _).mpr
        (hzc.comp (continuous_id.subtype_mk fun g => Subgroup.mem_top g)), fun g h => ?_⟩
      exact hzco ⟨g, Subgroup.mem_top g⟩ ⟨h, Subgroup.mem_top h⟩
    obtain ⟨m, hc', hδ'⟩ := norm_coc α δ hδ c hcoc
    set c' : G ℚ Ω → QO l O := fun g => c g - ((α g : O) • m - m) with hcE'
    have hs : ∀ D ∈ shaFam ℚ Ω l, ∃ m' : QO l O, ∀ g ∈ D, c' g = (α g : O) • m' - m' := by
      intro D hD
      obtain ⟨mD, hmD⟩ := hloc D hD
      refine ⟨mD - m, fun g hg => ?_⟩
      have e := hmD ⟨g, Subgroup.mem_top g⟩ hg
      change c g = (α g : O) • mD - mD at e
      simp only [hcE', e]
      module
    obtain ⟨a, ha0, hmem⟩ := mem_shT Ω l O α δ F h1 h2 c' hc' hδ' hs
    obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
    have hmem' : c' ∈ ShT (QO l O) α δ F (ϖ ^ k) :=
      shT_mono α δ F (Units.mul_left_dvd.mpr dvd_rfl) hmem
    let z' : Z1U (twist₂ l α) T := ⟨fun v => c' v.1,
      (hc'.1.comp_continuous continuous_subtype_val).continuous, fun v w => hc'.2 v.1 w.1⟩
    have hq : Q z = Q z' := by
      simp only [Q, Submodule.mkQ_apply]
      rw [UpperTheory.V.Base.mk_eq_mk]
      refine ⟨m, fun v => ?_⟩
      change c v.1 - c' v.1 = (α v.1 : O) • m - m
      simp only [hcE']
      abel
    change Q z ∈ _
    rw [hq]
    exact Submodule.mem_iSup_of_mem k (Submodule.mem_map_of_mem (show z' ∈ _ from hmem'))
  · intro n₀
    refine ⟨n₀, le_rfl, ?_⟩
    calc Module.length O (P n₀) ≤ Module.length O ((ShT (QO l O) α δ F (ϖ ^ n₀)).comap ι) :=
          Module.length_le_of_surjective (Q.submoduleMap _) (LinearMap.submoduleMap_surjective Q _)
      _ ≤ Module.length O (ShT (QO l O) α δ F (ϖ ^ n₀)) :=
          Module.length_le_of_injective (ι.restrict fun x hx => hx)
            (fun x y hxy => Subtype.ext (hι (congrArg Subtype.val hxy)))
      _ ≤ n := hn _ (pow_ne_zero _ hϖ.ne_zero)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

theorem UpperTheory.V.ML.ext :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (O W : Type) [CommRing O] [AddCommGroup W] [Module O W] (M F n : ℕ), F ≠ 0 → ∀ (β : G ℚ Ω →* Oˣ) (ν : G ℚ Ω → W), IsNu M F n β ν → ∀ δ : G ℚ Ω, IsUnit ((β δ : O) - 1) →
    ∃ c : G ℚ Ω → W, IsCoc β c ∧ (∀ u ∈ fixMu ℚ Ω F, c u = ν u) ∧ ∀ g, ∃ u ∈ fixMu ℚ Ω F, ∃ y : O, c g = y • ν u := by
  intro Ω _ _ _ O W _ _ _ M F n hF β ν hν δ hδ
  obtain ⟨hN, -, hcomm, -⟩ := galBasic Ω F hF
  have hk : (↑hδ.unit⁻¹ : O) * ((β δ : O) - 1) = 1 := hδ.val_inv_mul
  have h1 : ν 1 = 0 := by
    have := hν.add 1 (fixMu ℚ Ω F).one_mem 1 (fixMu ℚ Ω F).one_mem
    simpa using this
  have hinv : ∀ u ∈ fixMu ℚ Ω F, ν u⁻¹ = -ν u := by
    intro u hu
    have := hν.add u hu u⁻¹ ((fixMu ℚ Ω F).inv_mem hu)
    rw [mul_inv_cancel, h1] at this
    exact eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact this.symm)
  have hcm : ∀ g, g * δ * g⁻¹ * δ⁻¹ ∈ fixMu ℚ Ω F := fun g => hcomm g δ
  refine ⟨fun g => (-(↑hδ.unit⁻¹ : O)) • ν (g * δ * g⁻¹ * δ⁻¹), ⟨?_, ?_⟩, ?_, fun g => ⟨_, hcm g, _, rfl⟩⟩
  · have hc : Continuous (fun g : G ℚ Ω => g * δ * g⁻¹ * δ⁻¹) := by
      have c1 : Continuous (fun g : G ℚ Ω => g * δ) := continuous_mul_const δ
      have c2 : Continuous (fun g : G ℚ Ω => g⁻¹) := continuous_inv
      have c3 : Continuous (fun g : G ℚ Ω => g * δ * g⁻¹) := c1.mul c2
      exact (continuous_mul_const δ⁻¹).comp c3
    have hf : Continuous (fun g : G ℚ Ω => (⟨g * δ * g⁻¹ * δ⁻¹, hcm g⟩ : fixMu ℚ Ω F)) := hc.subtype_mk hcm
    have hl : IsLocallyConstant (fun g : G ℚ Ω => ν (g * δ * g⁻¹ * δ⁻¹)) := hν.lc.comp_continuous hf
    exact hl.comp (fun w => (-(↑hδ.unit⁻¹ : O)) • w)
  · intro g h
    have e : g * h * δ * (g * h)⁻¹ * δ⁻¹ = g * (h * δ * h⁻¹ * δ⁻¹) * g⁻¹ * (g * δ * g⁻¹ * δ⁻¹) := by
      group
    have hmem : g * (h * δ * h⁻¹ * δ⁻¹) * g⁻¹ ∈ fixMu ℚ Ω F := hN.conj_mem _ (hcm h) g
    show (-(↑hδ.unit⁻¹ : O)) • ν (g * h * δ * (g * h)⁻¹ * δ⁻¹) =
      (-(↑hδ.unit⁻¹ : O)) • ν (g * δ * g⁻¹ * δ⁻¹) + (β g : O) • ((-(↑hδ.unit⁻¹ : O)) • ν (h * δ * h⁻¹ * δ⁻¹))
    rw [e, hν.add _ hmem _ (hcm g), hν.eqv g _ (hcm h), smul_add, smul_comm (-(↑hδ.unit⁻¹ : O)) (β g : O)]
    abel
  · intro u hu
    have hconj : δ * u⁻¹ * δ⁻¹ ∈ fixMu ℚ Ω F := hN.conj_mem _ ((fixMu ℚ Ω F).inv_mem hu) δ
    have e : u * δ * u⁻¹ * δ⁻¹ = u * (δ * u⁻¹ * δ⁻¹) := by
      group
    have e2 : ν u + (β δ : O) • -ν u = -(((β δ : O) - 1) • ν u) := by
      rw [sub_smul, one_smul, smul_neg]
      abel
    show (-(↑hδ.unit⁻¹ : O)) • ν (u * δ * u⁻¹ * δ⁻¹) = ν u
    rw [e, hν.add u hu _ hconj, hν.eqv δ u⁻¹ ((fixMu ℚ Ω F).inv_mem hu), hinv u hu, e2, smul_neg, neg_smul,
      neg_neg, smul_smul, hk, one_smul]
end
