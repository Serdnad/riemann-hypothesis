module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicCases.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompAlg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle008
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle002

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem val_dvd {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {m n : ℕ} (h : m ∣ n)
    (hA : A.valuation (m : Ω) < 1) : A.valuation (n : Ω) < 1 := by
  obtain ⟨k, rfl⟩ := h
  rw [Nat.cast_mul, map_mul]
  have hk : A.valuation (k : Ω) ≤ 1 := by
    simpa using A.valuation_le_one (k : A)
  calc A.valuation (m : Ω) * A.valuation (k : Ω) ≤ A.valuation (m : Ω) * 1 := mul_le_mul' le_rfl hk
    _ < 1 := by rwa [mul_one]

private theorem val_prod {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (S : Finset ℕ)
    (hA : A.valuation ((∏ p ∈ S, p : ℕ) : Ω) < 1) : ∃ p ∈ S, A.valuation (p : Ω) < 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp at hA
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Nat.cast_mul, map_mul] at hA
    by_cases hp : A.valuation (a : Ω) < 1
    · exact ⟨a, Finset.mem_insert_self a S, hp⟩
    · have h1 : A.valuation (a : Ω) = 1 :=
        le_antisymm (by simpa using A.valuation_le_one (a : A)) (not_lt.mp hp)
      rw [h1, one_mul] at hA
      obtain ⟨p, hpS, hp'⟩ := ih hA
      exact ⟨p, Finset.mem_insert_of_mem hpS, hp'⟩

private theorem vlen_le (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l)
    (N : ℕ) [NeZero N] (e : ℕ) (he : e ≠ 0) (ψ : DirichletCharacter c.O N) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    Vlen Ω c e ψ ≤ Chr.VS l (∏ p ∈ S, p) e (Chr.dirG ℚ Ω ψ) := by
  classical
  haveI := c.dvr
  haveI := c.fin
  have hcls := Chr.clsFacts ℚ Ω N
  have hker : (Chr.cls ℚ Ω N).ker ≤ (Chr.dirG ℚ Ω ψ).ker := by
    intro g hg
    rw [MonoidHom.mem_ker] at hg ⊢
    simp [Chr.dirG, hg]
  have hopen : IsOpen ((Chr.dirG ℚ Ω ψ).ker : Set (G ℚ Ω)) := Subgroup.isOpen_mono hker hcls.1
  have hpow : Chr.dirG ℚ Ω ψ ^ (Fintype.card (ZMod N)ˣ) = 1 := by
    refine MonoidHom.ext fun g => ?_
    rw [MonoidHom.pow_apply, MonoidHom.one_apply, Chr.dirG, MonoidHom.comp_apply, ← map_pow,
      pow_card_eq_one, map_one]
  have hint : ∀ (A : ValuationSubring Ω) (x : Ω) (z : ℤ), A.valuation x < 1 →
      A.valuation (x * (z : Ω)) < 1 := by
    intro A x z hx
    rw [map_mul]
    have hz : A.valuation (z : Ω) ≤ 1 := by simpa using A.valuation_le_one (z : A)
    calc A.valuation x * A.valuation (z : Ω) ≤ A.valuation x * 1 := mul_le_mul' le_rfl hz
      _ < 1 := by rwa [mul_one]
  show Chr.VS l (l * N) e (Chr.dirG ℚ Ω ψ) ≤ Chr.VS l (∏ p ∈ S, p) e (Chr.dirG ℚ Ω ψ)
  unfold Chr.VS
  set_option synthInstance.maxHeartbeats 200000 in
   refine Module.length_le_of_injective (Submodule.inclusion ?_) (Submodule.inclusion_injective _)
  intro x hx
  simp only [Base.ShaU, Base.mem_locSel] at hx ⊢
  intro D hD
  rcases hD with ⟨A, hAS, rfl⟩ | ⟨A, rfl⟩
  · obtain ⟨p, hpS, hp⟩ := val_prod A S hAS
    by_cases hdvd : p ∣ l * N
    · exact hx (Dec A) (Or.inl ⟨A, val_dvd A hdvd hp, rfl⟩)
    · have pp := hS p hpS
      have hpl : p ≠ l := by
        rintro rfl
        exact hdvd (dvd_mul_right p N)
      have hpN : ¬ p ∣ N := fun h' => hdvd (dvd_mul_of_dvd_right h' l)
      have hN : ¬ A.valuation (N : Ω) < 1 := by
        intro hN
        have hcop : Nat.gcd p N = 1 := ((Nat.Prime.coprime_iff_not_dvd pp).2 hpN)
        have hb := Nat.gcd_eq_gcd_ab p N
        rw [hcop] at hb
        have h1 : (1 : Ω) = (p : Ω) * (Nat.gcdA p N : Ω) + (N : Ω) * (Nat.gcdB p N : Ω) := by
          have := congrArg (fun z : ℤ => (z : Ω)) hb
          push_cast at this
          exact this
        have hsum := Valuation.map_add_lt A.valuation (hint A _ (Nat.gcdA p N) hp)
          (hint A _ (Nat.gcdB p N) hN)
        rw [← h1, map_one] at hsum
        exact lt_irrefl _ hsum
      have hIne : Ine A ≤ (Chr.dirG ℚ Ω ψ).ker := le_trans (hcls.2.2.2.2 A hN) hker
      have hU : (⊤ : Subgroup (G ℚ Ω)) ⊓ Ine A ≤ ⊤ ⊓ Dec A := inf_le_inf_left _ (Ine_le_Dec A)
      have hinj := (Chr.locUnr Ω l c.O e (Fintype.card (ZMod N)ˣ) (Chr.dirG ℚ Ω ψ) he
        Fintype.card_ne_zero hopen hpow p A pp hpl hp (⊤ ⊓ Ine A) (⊤ ⊓ Dec A) hU
        (top_inf_eq _) (top_inf_eq _)).2 (inf_le_right.trans hIne)
      have h0 := hx (Ine A) (Or.inr ⟨A, rfl⟩)
      have h2 : Base.resU (Chr.rho l e (Chr.dirG ℚ Ω ψ)) hU
          (Base.resU (Chr.rho l e (Chr.dirG ℚ Ω ψ)) (inf_le_left : ⊤ ⊓ Dec A ≤ ⊤) x) = 0 := by
        rw [Base.resU_resU]
        exact h0
      exact hinj (h2.trans (map_zero _).symm)
  · exact hx (Ine A) (Or.inr ⟨A, rfl⟩)

theorem UpperTheory.V.GradeZeroInterpolatingElement.shaEq :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (h : Host) (t : ℕ), h.Big t → ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (e : ℕ), l ≠ 2 → 0 < e → e < t → ∀ ψ ∈ h.X c e, ∀ D : Raw Ω c, D.Good → Aut.OfCase D h e ψ → Vlen Ω c e ψ ≤ D.sha := by
  intro Ω _ _ _ h t _ l _ c e _ he _ ψ _ D hD hA
  have key : ∀ {n' p₁ m₀ : ℕ}, Aut.OfChar D e ψ n' p₁ m₀ → Vlen Ω c e ψ ≤ D.sha := by
    intro n' p₁ m₀ hc
    unfold Raw.sha
    rw [hc.e_eq, hc.psi]
    exact vlen_le Ω l c h.N e he.ne' ψ D.S hD.S_prime
  rcases hA with ⟨_, hc⟩ | ⟨_, hc⟩
  · exact key hc
  · exact key hc
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem cls_one {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {M : ℕ} (N : ℕ) [NeZero N] (hN : N ∣ M)
    (s : G ℚ Ω) (h : ∀ ζ : Ω, ζ ^ M = 1 → s ζ = ζ) : Chr.cls ℚ Ω N s = 1 := by
  refine (Chr.clsFacts ℚ Ω N).2.2.1 s 1 (fun ζ hζ => ?_)
  obtain ⟨k, rfl⟩ := hN
  rw [h ζ (by rw [pow_mul, hζ, one_pow]), Units.val_one, ZMod.val_one_eq_one_mod]
  rcases Nat.lt_or_ge 1 N with h1 | h1
  · rw [Nat.mod_eq_of_lt h1, pow_one]
  · have hN1 : N = 1 := by
      have := NeZero.pos N
      omega
    subst hN1
    simpa using hζ

private theorem dirG_one {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {O : Type} [CommRing O] {M N : ℕ} [NeZero N]
    (χ : DirichletCharacter O N) (hN : N ∣ M) (s : G ℚ Ω) (h : ∀ ζ : Ω, ζ ^ M = 1 → s ζ = ζ) : Chr.dirG ℚ Ω χ s = 1 := by
  rw [Chr.dirG, MonoidHom.comp_apply, cls_one N hN s h, map_one]

private theorem dirG_pow_one {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {O : Type} [CommRing O] {N : ℕ} [NeZero N]
    (χ : DirichletCharacter O N) {a m : ℕ} (h : χ ^ a = 1) (ha : a ∣ m) : Chr.dirG ℚ Ω χ ^ m = 1 := by
  obtain ⟨k, rfl⟩ := ha
  refine MonoidHom.ext fun g => Units.ext ?_
  simp only [MonoidHom.pow_apply, MonoidHom.one_apply, Units.val_pow_eq_pow_val, Units.val_one,
    Chr.dirG, MonoidHom.comp_apply, MulChar.coe_toUnitHom]
  rw [pow_mul, ← MulChar.pow_apply_coe, h, MulChar.one_apply_coe, one_pow]

private theorem tot_two (k : ℕ) : Nat.totient (2 ^ k) ∣ 2 ^ k := by
  cases k with
  | zero => simp
  | succ k =>
    rw [Nat.totient_prime_pow_succ Nat.prime_two, pow_succ]
    exact Nat.mul_dvd_mul_left _ (by norm_num)

private theorem pow_tot {O : Type} [CommRing O] {N : ℕ} [NeZero N] (χ : DirichletCharacter O N) :
    χ ^ Nat.totient N = 1 := by
  ext u
  rw [MulChar.pow_apply_coe, MulChar.one_apply_coe, ← map_pow, ← Units.val_pow_eq_pow_val,
    ZMod.pow_totient, Units.val_one, map_one]

private theorem pow_tot_cond {O : Type} [CommRing O] {N : ℕ} [NeZero N] (χ : DirichletCharacter O N) :
    χ ^ Nat.totient χ.conductor = 1 := by
  haveI : NeZero χ.conductor := ⟨DirichletCharacter.conductor_ne_zero χ⟩
  rw [show χ ^ Nat.totient χ.conductor = DirichletCharacter.changeLevel χ.conductor_dvd_level
      (χ.primitiveCharacter ^ Nat.totient χ.conductor) by
    rw [map_pow, χ.changeLevel_primitiveCharacter]]
  rw [pow_tot, map_one]

theorem UpperTheory.V.GradeZeroInterpolatingElement.levOf :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (h : Host) (t : ℕ), h.Big t → ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (e : ℕ), l ≠ 2 → 0 < e → e < t → ∀ ψ ∈ h.X c e, ∀ D : Raw Ω c, D.Good → ∀ n' p₁ m₀ : ℕ, Aut.OfChar D e ψ n' p₁ m₀ → c2 ψ ≤ n' → m₀ ∣ h.o → (Af.KillsMu (l * 2 ^ n' * h.N * p₁) D.ψ ∧ Af.KillsMu (l * 2 ^ n' * h.N * p₁) D.ξ ∧ Af.KillsMu (l * 2 ^ n' * h.N * p₁) D.om) ∧ D.ψ ^ ((l - 1) * 2 ^ n' * (2 * h.o)) = 1 ∧ D.ξ ^ ((l - 1) * 2 ^ n' * (2 * h.o)) = 1 ∧ D.om ^ ((l - 1) * 2 ^ n' * (2 * h.o)) = 1 := by
  intro Ω _ _ _ h t _ l _ c e _ _ _ ψ hψ D hD n' p₁ m₀ hc hc2 hm₀
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  obtain ⟨hp₁, ξ', ξ₀, -, -, hord, hξ⟩ := hc.xi
  have hpsi := hc.psi
  have hMN : h.N ∣ l * 2 ^ n' * h.N * p₁ := dvd_mul_of_dvd_left (dvd_mul_left _ _) _
  have hMp : p₁ ∣ l * 2 ^ n' * h.N * p₁ := dvd_mul_left _ _
  have hM2 : 2 ^ n' ∣ l * 2 ^ n' * h.N * p₁ :=
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) _
  have hMl : l ∣ l * 2 ^ n' * h.N * p₁ :=
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) _
  have hEo : h.o ∣ (l - 1) * 2 ^ n' * (2 * h.o) := dvd_mul_of_dvd_right (dvd_mul_left _ _) _
  have hE2o : 2 * h.o ∣ (l - 1) * 2 ^ n' * (2 * h.o) := dvd_mul_left _ _
  have hE2 : 2 ^ n' ∣ (l - 1) * 2 ^ n' * (2 * h.o) := dvd_mul_of_dvd_left (dvd_mul_left _ _) _
  have hEl : l - 1 ∣ (l - 1) * 2 ^ n' * (2 * h.o) := dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  have hIs : IsOmT c D.om := ⟨hD.om_pow, fun σ => Ideal.Quotient.eq.mp (hD.om_bar σ)⟩
  have hker := ((omT Ω l c).2 D.om hIs).2.1
  have htot2 : Nat.totient (2 ^ n') ∣ (l - 1) * 2 ^ n' * (2 * h.o) := (tot_two n').trans hE2
  have hpsiE : ψ ^ ((l - 1) * 2 ^ n' * (2 * h.o)) = 1 := by
    have hchar := ((Host.mem_X h).1 hψ).1
    have hcomp := hostComp h c.O ψ hchar
    refine (compAlg c.O h.N 2 Nat.prime_two).2.2.2.2.2.2.2 ψ _ (fun p hp => ?_)
    have pp := Nat.prime_of_mem_primeFactors hp
    by_cases hp2 : p = 2
    · subst hp2
      have hcond := (compCond c.O h.N ψ 2 Nat.prime_two).2.2.2.1
      have h1 := pow_tot_cond (psi2 ψ)
      rw [← hcond] at h1
      have hdv : Nat.totient (2 ^ c2 ψ) ∣ (l - 1) * 2 ^ n' * (2 * h.o) :=
        ((tot_two _).trans (Nat.pow_dvd_pow 2 hc2)).trans hE2
      obtain ⟨k, hk⟩ := hdv
      rw [hk, pow_mul]
      unfold psi2 at h1
      rw [h1, one_pow]
    · exact orderOf_dvd_iff_pow_eq_one.mp (((hcomp.2.2 p pp hp2).1).trans hE2o)
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro s hs
    rw [hpsi]
    exact dirG_one ψ hMN s hs
  · intro s hs
    rw [hξ, MonoidHom.mul_apply, dirG_one ξ₀ hMp s hs, dirG_one ξ' hM2 s hs, mul_one]
  · intro s hs
    have h1 : Chr.cls ℚ Ω l s = 1 := cls_one l hMl s hs
    have h2 : s ∈ D.om.ker := by
      rw [hker]
      exact h1
    exact h2
  · rw [hpsi]
    exact dirG_pow_one ψ hpsiE dvd_rfl
  · rw [hξ, mul_pow, dirG_pow_one ξ₀ (pow_orderOf_eq_one ξ₀) (by rw [hord]; exact hm₀.trans hEo),
      dirG_pow_one ξ' (pow_tot ξ') htot2, mul_one]
  · obtain ⟨k, hk⟩ := hEl
    rw [hk, pow_mul, hD.om_pow, one_pow]
end
