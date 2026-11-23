module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsHostFrame
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle006
public import Formalism.GaloisCohomology.GaloisCohomologyProofs.LdataNonempty
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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

@[expose] public section

section

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual UpperTheory.V UpperTheory.V.Base

private theorem prime_l {l : ℕ} (hl : l.Prime) : Prime ((l : ℕ) : 𝓞 ℚ) := by
  rw [← MulEquiv.prime_iff Rat.ringOfIntegersEquiv, map_natCast]
  exact Nat.prime_iff_prime_int.mp hl

private noncomputable def vQ {l : ℕ} (hl : l.Prime) : Pl where
  asIdeal := Ideal.span {((l : ℕ) : 𝓞 ℚ)}
  isPrime := (Ideal.span_singleton_prime (prime_l hl).ne_zero).mpr (prime_l hl)
  ne_bot := by rw [Ne, Ideal.span_singleton_eq_bot]; exact (prime_l hl).ne_zero

private theorem fin_above {n : ℕ} (hn : n ≠ 0) : {v : Pl | ((n : ℕ) : 𝓞 ℚ) ∈ v.asIdeal}.Finite := by
  have hI : (Ideal.span {((n : ℕ) : 𝓞 ℚ)} : Ideal (𝓞 ℚ)) ≠ 0 := by
    rw [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn
  refine (Ideal.finite_factors hI).subset ?_
  intro v hv
  simp only [Set.mem_setOf_eq] at hv ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]
  exact hv

private theorem cls_exists (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (M : ℕ) [NeZero M] (S : Set Pl)
    (hS : ∀ v ∉ S, ((M : ℕ) : 𝓞 ℚ) ∉ v.asIdeal) :
    ∃ μ : GS Ω S →* (ZMod M)ˣ, μ.comp (toGS Ω S) = Chr.cls ℚ Ω M := by
  obtain ⟨hopen, -, -, -, hine⟩ := Chr.clsFacts ℚ Ω M
  obtain ⟨-, -, -, hpl⟩ := Kum.placeDict ℚ Ω
  have hle : NS Ω S ≤ (Chr.cls ℚ Ω M).ker := by
    apply Subgroup.topologicalClosure_minimal _ _ (Subgroup.isClosed_of_isOpen _ hopen)
    apply Subgroup.normalClosure_le_normal
    intro σ hσ
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_compl_iff] at hσ
    obtain ⟨v, hv, A, hA, hσA⟩ := hσ
    have hn : ¬ A.valuation ((M : ℕ) : Ω) < 1 := by
      rw [hpl A v M hA]
      exact hS v hv
    exact hine A hn hσA
  exact ⟨QuotientGroup.lift (NS Ω S) (Chr.cls ℚ Ω M) hle, QuotientGroup.lift_comp_mk' _ _ _⟩

private theorem cc_exists (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] : ∃ σ : G ℚ Ω, IsCC σ := by
  obtain ⟨σ, j, hj⟩ := exists_isConjOm (E := ℚ) (Ω := Ω)
  exact ⟨AlgEquiv.ofRingEquiv (f := σ) (fun q => by simp), j, fun x => hj x⟩

end

theorem UpperTheory.V.UnitaryThreeInertia.exists_hostFrame :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (c : Coef l) {N : ℕ} [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (o₁ : ℕ), HostData l e ψ o₁ →
    ∃ (S : Finset Pl) (A : S → ValuationSubring Ω) (F : Frame c.O (Formalism.ConjugateSelfDual.G ℚ Ω) (Gam Ω S) S), IsHostFrame Ω c e ψ S A F := by
  intro Ω _ _ _ l _ c N _ e ψ o₁ hd
  have hl : l.Prime := Fact.out
  have hlN : l * N ≠ 0 := Nat.mul_ne_zero hl.ne_zero (NeZero.ne N)
  set S : Finset Pl := (fin_above hlN).toFinset with hSdef
  have hmem : ∀ v : Pl, v ∈ S ↔ (((l * N : ℕ)) : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal :=
    fun v => Set.Finite.mem_toFinset _
  have hout : ∀ m : ℕ, m ∣ l * N → ∀ v ∉ (S : Set Pl),
      ((m : ℕ) : NumberField.RingOfIntegers ℚ) ∉ v.asIdeal := by
    intro m hm v hv hmv
    apply hv
    rw [Finset.mem_coe, hmem]
    obtain ⟨k, hk⟩ := hm
    rw [hk, Nat.cast_mul]
    exact v.asIdeal.mul_mem_right _ hmv
  have h4 : ∀ v ∉ (S : Set Pl), ((4 : ℕ) : NumberField.RingOfIntegers ℚ) ∉ v.asIdeal := by
    intro v hv h4v
    have h2 : ((2 : ℕ) : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal := by
      have h22 : ((4 : ℕ) : NumberField.RingOfIntegers ℚ) =
          ((2 : ℕ) : NumberField.RingOfIntegers ℚ) * ((2 : ℕ) : NumberField.RingOfIntegers ℚ) := by
        rw [← Nat.cast_mul]
      rw [h22] at h4v
      rcases v.isPrime.mem_or_mem h4v with h | h <;> exact h
    exact hout 2 (dvd_mul_of_dvd_right (even_iff_two_dvd.mp hd.N_even) l) v hv h2
  obtain ⟨μN, hμN⟩ := cls_exists Ω N (S : Set Pl) (hout N (dvd_mul_left N l))
  obtain ⟨μ4, hμ4⟩ := cls_exists Ω 4 (S : Set Pl) h4
  obtain ⟨χl, hχl⟩ :=
    Formalism.GaloisCohomology.chi_exists (F := ℚ) (Ω := Ω) l (S : Set Pl) (hout l (dvd_mul_right l N))
  obtain ⟨σ, hσ⟩ := cc_exists Ω
  let A : S → ValuationSubring Ω := fun v => Classical.choose (exists_isPlaceOver Ω (v : Pl))
  have hA := fun v : S => Classical.choose_spec (exists_isPlaceOver Ω (v : Pl))
  have hvl : vQ hl ∈ S := by
    rw [hmem]
    exact Ideal.mem_span_singleton.mpr ⟨(N : NumberField.RingOfIntegers ℚ), by push_cast; ring⟩
  let F : Frame c.O (Formalism.ConjugateSelfDual.G ℚ Ω) (Gam Ω S) S :=
    { π := toGS Ω (S : Set Pl)
      η := (MulChar.toUnitHom ZMod.χ₄).comp μ4
      Ψ := ((Units.map (algebraMap ℤ_[l] c.O : ℤ_[l] →* c.O)).comp χl) ^ e *
        (MulChar.toUnitHom ψ).comp μN
      c := toGS Ω (S : Set Pl) σ
      D := fun v => Dec (A v)
      I := fun v => Ine (A v)
      vl := ⟨vQ hl, hvl⟩
      Sb := {v | ∃ p ∈ Sb l ψ, (p : NumberField.RingOfIntegers ℚ) ∈ (v : Pl).asIdeal} }
  refine ⟨S, A, F, ?_⟩
  refine ⟨hmem, hA, rfl, ?_, ?_, ⟨σ, hσ, rfl⟩, fun _ => rfl, fun _ => rfl, ?_, fun _ => Iff.rfl⟩
  · show ((MulChar.toUnitHom ZMod.χ₄).comp μ4).comp (toGS Ω (S : Set Pl)) = eta4 Ω
    rw [MonoidHom.comp_assoc, hμ4]
    unfold eta4 UpperTheory.V.Chr.dirG
    rfl
  · show (((Units.map (algebraMap ℤ_[l] c.O : ℤ_[l] →* c.O)).comp χl) ^ e *
        (MulChar.toUnitHom ψ).comp μN).comp (toGS Ω (S : Set Pl)) = _
    unfold UpperTheory.V.Chr.Psi UpperTheory.V.Chr.dirG UpperTheory.V.Base.chiO
    rw [← hχl, ← hμN]
    ext τ
    simp
  · exact Ideal.mem_span_singleton_self _
end

section

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia Module

open UpperTheory.V in
private theorem quartic_character_eq_one (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (ζ : Ω) (hζ : IsPrimitiveRoot ζ 4)
    (σ : Formalism.ConjugateSelfDual.G ℚ Ω) (h : σ ζ = ζ) : eta4 Ω σ = 1 := by
  unfold eta4 Chr.dirG
  rw [MonoidHom.comp_apply]
  have hc := Chr.cls_spec (k := ℚ) (Ω := Ω) 4 σ ζ hζ.pow_eq_one
  rw [h] at hc
  have hv : ((Chr.cls ℚ Ω 4 σ : (ZMod 4)ˣ) : ZMod 4).val = 1 := by
    have h1 : ζ ^ 1 = ζ ^ ((Chr.cls ℚ Ω 4 σ : (ZMod 4)ˣ) : ZMod 4).val := by rwa [pow_one]
    have hlt := ZMod.val_lt ((Chr.cls ℚ Ω 4 σ : (ZMod 4)ˣ) : ZMod 4)
    exact (hζ.pow_inj (by norm_num) hlt h1).symm
  have hu : Chr.cls ℚ Ω 4 σ = 1 := Units.ext (ZMod.val_injective 4 (by rw [hv]; rfl))
  rw [hu, map_one]

theorem UpperTheory.exists_absGalois_fixing_sqrt_neg_one_cyclotomic_ne_one :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ∃ σ : Formalism.ConjugateSelfDual.G ℚ Ω, eta4 Ω σ = 1 ∧ cycMod ℚ Ω l 1 σ ≠ 1 := by
  intro Ω _ _ _ l _ hl2
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hlp : l.Prime := Fact.out
  haveI : NeZero l := ⟨hlp.ne_zero⟩
  obtain ⟨m, hm⟩ : ∃ m, l = 2 * m + 1 := hlp.eq_two_or_odd'.resolve_left hl2
  have hm1 : 1 ≤ m := by have := hlp.two_le; omega
  haveI : NeZero (4 * l) := ⟨by omega⟩
  let a : ZMod (4 * l) := ((4 * m + 1 : ℕ) : ZMod (4 * l))
  have ha : a * a = 1 := by
    have hnat : ((4 * m + 1) * (4 * m + 1) : ℕ) = 1 + (4 * l) * (2 * m) := by rw [hm]; ring
    show ((4 * m + 1 : ℕ) : ZMod (4 * l)) * ((4 * m + 1 : ℕ) : ZMod (4 * l)) = 1
    rw [← Nat.cast_mul, hnat, Nat.cast_add, Nat.cast_one, Nat.cast_mul (4 * l), ZMod.natCast_self,
      zero_mul, add_zero]
  let u : (ZMod (4 * l))ˣ := ⟨a, a, ha, ha⟩
  obtain ⟨σ, hσ⟩ := (UpperTheory.V.Chr.clsOnto Ω (4 * l)).1 u
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (4 * l)
  have hval : ((u : ZMod (4 * l))).val = 4 * m + 1 := by
    show (((4 * m + 1 : ℕ) : ZMod (4 * l))).val = 4 * m + 1
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have hspec : ∀ t : Ω, t ^ (4 * l) = 1 → σ t = t ^ (4 * m + 1) := by
    intro t ht
    rw [UpperTheory.V.Chr.cls_spec (4 * l) σ t ht, hσ, hval]
  refine ⟨σ, ?_, ?_⟩
  · have h4l : (ζ ^ l) ^ (4 * l) = 1 := by
      rw [← pow_mul, mul_comm l (4 * l), pow_mul, hζ.pow_eq_one, one_pow]
    have h4 : (ζ ^ l) ^ 4 = 1 := by rw [← pow_mul, mul_comm, hζ.pow_eq_one]
    refine quartic_character_eq_one Ω (ζ ^ l) (hζ.pow (by omega) (mul_comm 4 l)) σ ?_
    rw [hspec _ h4l, pow_succ, pow_mul, h4, one_pow, one_mul]
  · intro hcyc
    have hprim : IsPrimitiveRoot (ζ ^ 4) l := hζ.pow (by omega) rfl
    have h4l : (ζ ^ 4) ^ (4 * l) = 1 := by
      rw [← pow_mul, mul_comm 4 (4 * l), pow_mul, hζ.pow_eq_one, one_pow]
    haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
    unfold cycMod cycZ at hcyc
    have hz : PadicInt.toZModPow 1 ((cyclotomicCharacter Ω l
        (MulSemiringAction.toRingAut (Formalism.ConjugateSelfDual.G ℚ Ω) Ω σ) : ℤ_[l]ˣ) : ℤ_[l]) = 1 := by
      simpa using congrArg Units.val hcyc
    have hs := cyclotomicCharacter.spec l (n := 1) (MulSemiringAction.toRingAut (Formalism.ConjugateSelfDual.G ℚ Ω) Ω σ)
      (ζ ^ 4) (by rw [pow_one]; exact hprim.pow_eq_one)
    rw [hz, ZMod.val_one'' (by rw [pow_one]; exact hlp.one_lt.ne')] at hs
    have hs' : σ (ζ ^ 4) = (ζ ^ 4) ^ 1 := hs
    have heq := (hspec _ h4l).symm.trans hs'
    have hred : (ζ ^ 4) ^ (4 * m + 1) = (ζ ^ 4) ^ (2 * m) := by
      rw [show 4 * m + 1 = 2 * m + l by omega, pow_add, hprim.pow_eq_one, mul_one]
    rw [hred] at heq
    have := hprim.pow_inj (by omega) (by omega) heq
    omega
end
