module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.RingTheory.Henselian
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_expand :
    ∀ (N k a : ℕ), 0 < N → bcoef N k a = ∑ j ∈ range (k + 1), (k.choose j : ℚ) * bernoulli j * (N : ℚ) ^ ((j : ℤ) - 1) * (a : ℚ) ^ (k - j) := by
  intro N k a hN
  have hN' : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  simp only [bcoef]
  rw [Polynomial.bernoulli, Polynomial.eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjk : j ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  rw [Polynomial.eval_monomial, div_pow]
  have hsplit : (N : ℚ) ^ ((k : ℤ) - 1) = (N : ℚ) ^ ((j : ℤ) - 1) * (N : ℚ) ^ ((k - j : ℕ) : ℤ) := by
    rw [← zpow_add₀ hN']
    congr 1
    push_cast [hjk]
    ring
  rw [hsplit, zpow_natCast]
  have hp : (N : ℚ) ^ (k - j) ≠ 0 := pow_ne_zero _ hN'
  field_simp
end

section

open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_charbij :
    ∀ {N : ℕ} [NeZero N] {K Ω : Type} [Field K] [Field Ω] [HasEnoughRootsOfUnity K (Monoid.exponent (ZMod N)ˣ)] (f : K →+* Ω) (P : Set (Subgroup (ZMod N)ˣ)), Set.BijOn (fun χ : DirichletCharacter K N => (χ.ringHomComp f : DirichletCharacter Ω N)) (charSet K P) (charSet Ω P) := by
  intro N _ K Ω _ _ _ f P
  have hf : Function.Injective f := f.injective
  have hker : ∀ χ : DirichletCharacter K N, (MulChar.toUnitHom (χ.ringHomComp f)).ker = (MulChar.toUnitHom χ).ker := by
    intro χ
    ext u
    simp only [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one, MulChar.ringHomComp_apply]
    constructor
    · intro h
      exact hf (h.trans (map_one f).symm)
    · intro h
      rw [h, map_one]
  refine ⟨?_, ?_, ?_⟩
  · intro χ hχ
    simp only [charSet, Set.mem_setOf_eq] at hχ ⊢
    rw [hker]
    exact hχ
  · intro χ₁ _ χ₂ _ h
    ext u
    have h' := congrArg (fun ψ : DirichletCharacter Ω N => ψ u) h
    simp only [MulChar.ringHomComp_apply] at h'
    exact hf h'
  · intro χ' hχ'
    have he : NeZero (Monoid.exponent (ZMod N)ˣ) := ⟨Monoid.exponent_ne_zero_of_finite⟩
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K (Monoid.exponent (ZMod N)ˣ)
    have hne : (primitiveRoots (Monoid.exponent (ZMod N)ˣ) K).Nonempty :=
      ⟨ζ, (mem_primitiveRoots (NeZero.pos _)).mpr hζ⟩
    have hmem : ∀ u, MulChar.toUnitHom χ' u ∈ rootsOfUnity (Monoid.exponent (ZMod N)ˣ) Ω := by
      intro u
      rw [mem_rootsOfUnity, ← map_pow, Monoid.pow_exponent_eq_one, map_one]
    let ψ : (ZMod N)ˣ →* Kˣ := (rootsOfUnity (Monoid.exponent (ZMod N)ˣ) K).subtype.comp
      ((rootsOfUnityEquivOfPrimitiveRoots hf hne).symm.toMonoidHom.comp
        ((MulChar.toUnitHom χ').codRestrict _ hmem))
    have hcomp : (MulChar.ofUnitHom ψ).ringHomComp f = χ' := by
      ext u
      rw [MulChar.ringHomComp_apply, MulChar.ofUnitHom_coe]
      show f (((rootsOfUnityEquivOfPrimitiveRoots hf hne).symm ⟨MulChar.toUnitHom χ' u, hmem u⟩ : Kˣ) : K) = χ' u
      rw [rootsOfUnityEquivOfPrimitiveRoots_symm_apply]
      simp [MulChar.coe_toUnitHom]
    refine ⟨MulChar.ofUnitHom ψ, ?_, hcomp⟩
    simp only [charSet, Set.mem_setOf_eq] at hχ' ⊢
    rw [← hker, hcomp]
    exact hχ'
end

section

open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_parity :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] {N : ℕ} [NeZero N] (k : ℕ) (χ : DirichletCharacter Ω N), (χ.toUnitHom.ker ∈ parKer N k ↔ χ (-1) = (-1) ^ k) ∧ (χ.primitiveCharacter (-1) = χ (-1)) := by
  intro Ω _ _ N _ k χ
  have hne : (-1 : Ω) ≠ 1 := by norm_num
  refine ⟨?_, ?_⟩
  · have hval : χ.toUnitHom (-1) = 1 ↔ χ (-1) = 1 := by
      rw [← Units.val_inj, MulChar.coe_toUnitHom, Units.val_neg, Units.val_one, Units.val_one]
    show ((-1 : (ZMod N)ˣ) ∈ χ.toUnitHom.ker ↔ Even k) ↔ _
    rw [MonoidHom.mem_ker, hval]
    rcases Nat.even_or_odd k with hk | hk
    · rw [hk.neg_one_pow]
      simp [hk]
    · rw [hk.neg_one_pow]
      have hk' : ¬ Even k := Nat.not_even_iff_odd.mpr hk
      rcases χ.even_or_odd with h | h
      · have h1 : χ (-1) = 1 := h
        simp [hk', h1, hne.symm]
      · have h1 : χ (-1) = -1 := h
        simp [hk', h1, hne]
  · have hd := DirichletCharacter.conductor_dvd_level χ
    have h := DirichletCharacter.changeLevel_eq_cast_of_dvd χ.primitiveCharacter hd (-1)
    rw [DirichletCharacter.changeLevel_primitiveCharacter, Units.val_neg, Units.val_one,
      ZMod.cast_neg hd, ZMod.cast_one hd] at h
    exact h.symm
end

section

open Finset UpperTheory.V.Bern

private theorem bernoulli_poly_reflection (k : ℕ) (x : ℚ) :
    (Polynomial.bernoulli k).eval (1 - x) = (-1) ^ k * (Polynomial.bernoulli k).eval x := by
  exact Polynomial.bernoulli_eval_one_sub k x

theorem UpperTheory.V.Bern.b_shift :
    ∀ (N k a : ℕ), 0 < N → bcoef N k (a + N) = bcoef N k a + (k : ℚ) * (a : ℚ) ^ (k - 1) ∧ (∀ m : ℕ, 0 < m → bcoef (m * N) k (m * a) = (m : ℚ) ^ ((k : ℤ) - 1) * bcoef N k a) ∧ (a ≤ N → bcoef N k (N - a) = (-1) ^ k * bcoef N k a) := by
  intro N k a hN
  have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  refine ⟨?_, ?_, ?_⟩
  · unfold bcoef
    have e : ((a + N : ℕ) : ℚ) / N = 1 + (a : ℚ) / N := by
      push_cast; field_simp; ring
    rw [e, Polynomial.bernoulli_eval_one_add, mul_add]
    congr 1
    rcases k with _ | k
    · simp
    · have : ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) := by push_cast; ring
      rw [this, zpow_natCast, Nat.add_sub_cancel, div_pow]
      field_simp
  · intro m hm
    have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
    unfold bcoef
    have e : ((m * a : ℕ) : ℚ) / ((m * N : ℕ) : ℚ) = (a : ℚ) / N := by
      push_cast; field_simp
    rw [e, Nat.cast_mul, mul_zpow, mul_assoc]
  · intro h
    unfold bcoef
    have e : ((N - a : ℕ) : ℚ) / N = 1 - (a : ℚ) / N := by
      rw [Nat.cast_sub h]; field_simp
    rw [e, bernoulli_poly_reflection]
    ring
end

section

open Finset UpperTheory.V.Bern

private theorem UpperTheory.V.Bern.b_one_sum {R : Type} [AddCommMonoid R] {N : ℕ} [NeZero N] (Φ : ZMod N → R) :
    ∑ a ∈ Icc 1 N, Φ (a : ZMod N) = ∑ a : ZMod N, Φ a := by
  refine Finset.sum_nbij' (fun a : ℕ => (a : ZMod N)) (fun b => (b - 1).val + 1) ?_ ?_ ?_ ?_ ?_
  · intro a _
    simp
  · intro b _
    simp only [Finset.mem_Icc]
    exact ⟨by omega, ZMod.val_lt _⟩
  · intro a ha
    simp only [Finset.mem_Icc] at ha
    obtain ⟨k, rfl⟩ : ∃ k, a = k + 1 := ⟨a - 1, by omega⟩
    have hk : k < N := by omega
    simp [Nat.cast_add, ZMod.val_cast_of_lt hk]
  · intro b _
    push_cast
    simp
  · intro a _
    rfl

theorem UpperTheory.V.Bern.b_one :
    ∀ {R : Type} [CommRing R] [Algebra ℚ R] {N : ℕ} [NeZero N] (Φ : ZMod N → R), ∑ a : ZMod N, Φ a = 0 → (N : R) * genB 1 Φ = ∑ a ∈ Icc 1 N, Φ (a : ZMod N) * (a : R) := by
  intro R _ _ N _ Φ hΦ
  simp only [genB, bcoef, Polynomial.bernoulli_one]
  have hs : ∑ a ∈ Icc 1 N, Φ (a : ZMod N) = 0 := (UpperTheory.V.Bern.b_one_sum Φ).trans hΦ
  have hN : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have key : ∀ x : ℕ, (N : R) * (Φ (x : ZMod N) * algebraMap ℚ R ((N : ℚ) ^ ((1 : ℕ) - 1 : ℤ) * Polynomial.eval ((x : ℚ) / N) (Polynomial.X - Polynomial.C 2⁻¹))) = Φ (x : ZMod N) * (x : R) - algebraMap ℚ R ((N : ℚ) / 2) * Φ (x : ZMod N) := by
    intro x
    have e : (N : ℚ) * ((N : ℚ) ^ ((1 : ℕ) - 1 : ℤ) * Polynomial.eval ((x : ℚ) / N) (Polynomial.X - Polynomial.C 2⁻¹)) = (x : ℚ) - (N : ℚ) / 2 := by
      simp
      field_simp
    calc (N : R) * (Φ (x : ZMod N) * algebraMap ℚ R ((N : ℚ) ^ ((1 : ℕ) - 1 : ℤ) * Polynomial.eval ((x : ℚ) / N) (Polynomial.X - Polynomial.C 2⁻¹)))
        = Φ (x : ZMod N) * algebraMap ℚ R ((N : ℚ) * ((N : ℚ) ^ ((1 : ℕ) - 1 : ℤ) * Polynomial.eval ((x : ℚ) / N) (Polynomial.X - Polynomial.C 2⁻¹))) := by
          rw [map_mul (algebraMap ℚ R) (N : ℚ), map_natCast]
          ring
      _ = _ := by
          rw [e, map_sub, map_natCast]
          ring
  rw [Finset.mul_sum]
  simp_rw [key]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hs, mul_zero, sub_zero]
end

section

open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_egf :
    ∀ (N a : ℕ), 0 < N → (PowerSeries.mk fun k => bcoef N k a / (k.factorial : ℚ)) * (PowerSeries.rescale (N : ℚ) (PowerSeries.exp ℚ) - 1) = PowerSeries.X * PowerSeries.rescale (a : ℚ) (PowerSeries.exp ℚ) := by
  intro N a hN
  have hN' : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have h := congrArg (PowerSeries.rescale (N : ℚ)) (Polynomial.bernoulli_generating_function ((a : ℚ) / N))
  rw [map_mul, map_mul, map_sub, map_one, PowerSeries.rescale_mk, PowerSeries.rescale_X,
    PowerSeries.rescale_rescale] at h
  have hc : ((a : ℚ) / N) * N = a := by field_simp
  rw [hc] at h
  beta_reduce at h
  have hmk : (PowerSeries.mk fun k => bcoef N k a / (k.factorial : ℚ)) =
      PowerSeries.C (1 / (N : ℚ)) * PowerSeries.mk (fun n => (N : ℚ) ^ n *
        (Polynomial.aeval ((a : ℚ) / N)) ((1 / (n.factorial : ℚ)) • Polynomial.bernoulli n)) := by
    ext n
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
    simp only [bcoef, map_smul, Polynomial.coe_aeval_eq_eval, smul_eq_mul]
    rw [zpow_sub_one₀ hN', zpow_natCast]
    have hf : (n.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
    field_simp
  rw [hmk, mul_assoc, h, ← mul_assoc, ← mul_assoc, ← map_mul, one_div_mul_cancel hN', map_one, one_mul]
end

section

open Finset UpperTheory.V.Bern

private theorem change_level_value_eq {R S : Type} [CommRing R] [CommRing S] {N : ℕ} [NeZero N] (f : R →+* S)
    {d e : ℕ} (hde : e = d) (hd : d ∣ N) (he : e ∣ N) (φ : DirichletCharacter R d) (ψ : DirichletCharacter S e)
    (h : DirichletCharacter.changeLevel he ψ = (DirichletCharacter.changeLevel hd φ).ringHomComp f) (a : ℕ) :
    ψ (a : ZMod e) = f (φ (a : ZMod d)) := by
  subst hde
  have hc : (DirichletCharacter.changeLevel hd φ).ringHomComp f = DirichletCharacter.changeLevel hd (φ.ringHomComp f) := by
    ext u
    simp [MulChar.ringHomComp_apply, DirichletCharacter.changeLevel_eq_cast_of_dvd]
  have hψ : ψ = φ.ringHomComp f := DirichletCharacter.changeLevel_injective hd (h.trans hc)
  subst hψ
  simp [MulChar.ringHomComp_apply]

theorem UpperTheory.V.Bern.b_condmap :
    ∀ {R S : Type} [CommRing R] [CommRing S] {N : ℕ} [NeZero N] (f : R →+* S), Function.Injective f → ∀ χ : DirichletCharacter R N, DirichletCharacter.conductor (χ.ringHomComp f) = χ.conductor ∧ (∀ a : ℕ, primVal (χ.ringHomComp f) a = f (primVal χ a)) ∧ (χ.ringHomComp f).toUnitHom.ker = χ.toUnitHom.ker := by
  intro R S _ _ N _ f hf χ
  have hker : (χ.ringHomComp f).toUnitHom.ker = χ.toUnitHom.ker := by
    ext u
    simp only [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one, MulChar.ringHomComp_apply]
    constructor
    · intro h
      exact hf (h.trans (map_one f).symm)
    · intro h
      rw [h, map_one]
  have hset : DirichletCharacter.conductorSet (χ.ringHomComp f) = χ.conductorSet := by
    ext d
    simp only [DirichletCharacter.mem_conductorSet_iff]
    constructor
    · intro h
      have h' := (DirichletCharacter.factorsThrough_iff_ker_unitsMap h.dvd).mp h
      rw [hker] at h'
      exact (DirichletCharacter.factorsThrough_iff_ker_unitsMap h.dvd).mpr h'
    · intro h
      have h' := (DirichletCharacter.factorsThrough_iff_ker_unitsMap h.dvd).mp h
      rw [← hker] at h'
      exact (DirichletCharacter.factorsThrough_iff_ker_unitsMap h.dvd).mpr h'
  have hcond : DirichletCharacter.conductor (χ.ringHomComp f) = χ.conductor := by
    unfold DirichletCharacter.conductor
    rw [hset]
  refine ⟨hcond, ?_, hker⟩
  intro a
  unfold primVal
  exact change_level_value_eq f hcond χ.conductor_dvd_level (DirichletCharacter.conductor_dvd_level (χ.ringHomComp f))
    χ.primitiveCharacter (DirichletCharacter.primitiveCharacter (χ.ringHomComp f))
    (by rw [DirichletCharacter.changeLevel_primitiveCharacter, DirichletCharacter.changeLevel_primitiveCharacter]) a
end
