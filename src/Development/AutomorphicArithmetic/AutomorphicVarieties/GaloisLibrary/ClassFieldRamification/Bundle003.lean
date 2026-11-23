module

public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.Bundle002
public import Mathlib.Order.CompletePartialOrder
public import GroundTheory.GlobalFields.KummerTheory.Bundle001
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.Bundle003
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.Algebra.AffineMonoid.Basic
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
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.NumberTheory.RamificationInertia.Galois
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IsClassFieldHilbert
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr

@[expose] public section

section

open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

private theorem mem_ker_iff {N d : ℕ} [NeZero N] (h : d ∣ N) (u : (ZMod N)ˣ) :
    u ∈ (ZMod.unitsMap h).ker ↔ (u : ZMod N).val ≡ 1 [MOD d] := by
  rw [MonoidHom.mem_ker, ZMod.unitsMap_def, Units.ext_iff, Units.coe_map, Units.val_one]
  simp only [MonoidHom.coe_coe, ZMod.castHom_apply, ZMod.cast_eq_val]
  rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff]

private theorem ker_le_sup {N g d e : ℕ} [NeZero N] (hg : g ∣ N) (hd : d ∣ N) (he : e ∣ N)
    (hgcd : Nat.gcd d e ∣ g) (hN : N ∣ d * e) :
    (ZMod.unitsMap hg).ker ≤ (ZMod.unitsMap hd).ker ⊔ (ZMod.unitsMap he).ker := by
  intro u hu
  rw [mem_ker_iff hg] at hu
  have hx1 : 1 ≡ (u : ZMod N).val [MOD Nat.gcd d e] := (Nat.ModEq.of_dvd hgcd hu).symm
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder' hx1
  have hxN : (u : ZMod N).val.Coprime N := ZMod.val_coe_unit_coprime u
  have hkd : k.Coprime d := by
    unfold Nat.Coprime
    rw [hk1.gcd_eq]
    exact Nat.gcd_one_left d
  have hke : k.Coprime e := by
    unfold Nat.Coprime
    rw [hk2.gcd_eq]
    exact Nat.Coprime.coprime_dvd_right he hxN
  have hkN : k.Coprime N := Nat.Coprime.coprime_dvd_right hN (Nat.Coprime.mul_right hkd hke)
  have hvval : ((ZMod.unitOfCoprime k hkN : (ZMod N)ˣ) : ZMod N).val = k % N := by
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
  have hv : ZMod.unitOfCoprime k hkN ∈ (ZMod.unitsMap hd).ker := by
    rw [mem_ker_iff hd, hvval]
    exact ((Nat.mod_modEq k N).of_dvd hd).trans hk1
  have key : ZMod.unitsMap he (ZMod.unitOfCoprime k hkN) = ZMod.unitsMap he u := by
    ext
    rw [ZMod.unitsMap_def, Units.coe_map, Units.coe_map]
    simp only [MonoidHom.coe_coe, ZMod.castHom_apply, ZMod.cast_eq_val]
    rw [hvval, ZMod.natCast_eq_natCast_iff]
    exact ((Nat.mod_modEq k N).of_dvd he).trans hk2
  have hw : (ZMod.unitOfCoprime k hkN)⁻¹ * u ∈ (ZMod.unitsMap he).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, key, inv_mul_cancel]
  have hu' : u = ZMod.unitOfCoprime k hkN * ((ZMod.unitOfCoprime k hkN)⁻¹ * u) := by
    rw [mul_inv_cancel_left]
  rw [hu']
  exact Subgroup.mul_mem_sup hv hw

private theorem aux (N : ℕ) [NeZero N] (b : ℕ) : ∀ (a : ℕ) (ha : a ∣ N), a * b = N → a.Coprime b →
    (ZMod.unitsMap ha).ker ≤ ⨆ p ∈ b.primeFactors, KStar.Ram.inertiaUnits N p := by
  induction b using Nat.strong_induction_on with
  | _ b ih =>
  intro a ha hab hcop
  have hN0 : N ≠ 0 := NeZero.ne N
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hN0 (by rw [← hab, mul_zero])
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hN0 (by rw [← hab, zero_mul])
  by_cases hb1 : b = 1
  · subst hb1
    rw [mul_one] at hab
    subst hab
    intro u hu
    rw [mem_ker_iff ha] at hu
    have hu1 : u = 1 := by
      ext
      rw [Units.val_one, ← ZMod.natCast_zmod_val (u : ZMod a), ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff]
      exact hu
    rw [hu1]
    exact one_mem _
  · obtain ⟨p, hp, hpb⟩ := Nat.exists_prime_and_dvd hb1
    have hpa : ¬ p ∣ a := by
      intro h
      have h1 := Nat.dvd_gcd h hpb
      rw [hcop.gcd_eq_one] at h1
      exact hp.ne_one (Nat.dvd_one.mp h1)
    have hbsplit := Nat.ordProj_mul_ordCompl_eq_self b p
    have hk0 : 0 < b.factorization p := hp.factorization_pos_of_dvd hb0 hpb
    have hb'pos : 0 < b / p ^ b.factorization p := Nat.ordCompl_pos p hb0
    have hpk : 2 ≤ p ^ b.factorization p := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
    have hb'lt : b / p ^ b.factorization p < b := by
      have h2 : 2 * (b / p ^ b.factorization p) ≤ p ^ b.factorization p * (b / p ^ b.factorization p) :=
        Nat.mul_le_mul_right _ hpk
      omega
    have hb'dvd : b / p ^ b.factorization p ∣ b := Nat.ordCompl_dvd b p
    have hpb' : Nat.Coprime p (b / p ^ b.factorization p) := Nat.coprime_ordCompl hp hb0
    have ha'N : a * p ^ b.factorization p * (b / p ^ b.factorization p) = N := by
      rw [mul_assoc, hbsplit, hab]
    have ha'dvd : a * p ^ b.factorization p ∣ N := ⟨_, ha'N.symm⟩
    have ha'cop : (a * p ^ b.factorization p).Coprime (b / p ^ b.factorization p) :=
      Nat.Coprime.mul_left (Nat.Coprime.coprime_dvd_right hb'dvd hcop) (Nat.Coprime.pow_left _ hpb')
    have IH := ih _ hb'lt (a * p ^ b.factorization p) ha'dvd ha'N ha'cop
    have hvN : N.factorization p = b.factorization p := by
      rw [← hab, Nat.factorization_mul ha0 hb0, Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd hpa, zero_add]
    have hNsplit := Nat.ordProj_mul_ordCompl_eq_self N p
    have hcopE : (p ^ b.factorization p).Coprime (N / p ^ N.factorization p) :=
      Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hp hN0)
    have hgcd : Nat.gcd (a * p ^ b.factorization p) (N / p ^ N.factorization p) ∣ a := by
      rw [Nat.Coprime.gcd_mul_right_cancel a hcopE]
      exact Nat.gcd_dvd_left _ _
    have hNde : N ∣ (a * p ^ b.factorization p) * (N / p ^ N.factorization p) := by
      refine ⟨a, ?_⟩
      rw [← hvN, mul_assoc, hNsplit, mul_comm]
    have hstep := ker_le_sup ha ha'dvd (Nat.ordCompl_dvd N p) hgcd hNde
    refine hstep.trans (sup_le (IH.trans ?_) ?_)
    · exact iSup₂_le fun q hq =>
        le_iSup₂ (f := fun q (_ : q ∈ b.primeFactors) => KStar.Ram.inertiaUnits N q) q
          (Nat.primeFactors_mono hb'dvd hb0 hq)
    · exact le_iSup₂ (f := fun q (_ : q ∈ b.primeFactors) => KStar.Ram.inertiaUnits N q) p
        (Nat.mem_primeFactors.2 ⟨hp, hpb, hb0⟩)

theorem UpperTheory.V.CF.unitsGen :
    ∀ (a b : ℕ) [NeZero (a * b)], a.Coprime b → (ZMod.unitsMap (dvd_mul_right a b)).ker ≤ ⨆ p ∈ b.primeFactors, KStar.Ram.inertiaUnits (a * b) p := by
  intro a b _ h
  exact aux (a * b) b a _ rfl h
end

section

open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.splitCyc :
    ∀ (N : ℕ) [NeZero N] (C : Type) [Field C] [NumberField C] [IsCyclotomicExtension {N} ℚ C] (v : HeightOneSpectrum (𝓞 ℚ)) (p : ℕ), p.Prime → (p : 𝓞 ℚ) ∈ v.asIdeal → ¬ p ∣ N → GroundTheory.Global.SplitsCompletely C v → p ≡ 1 [MOD N] := by
  intro N _ C _ _ _ v p hp hpv hpN hspl
  haveI := Fact.mk hp
  haveI := v.isMaximal
  have hspan : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have hvZ : v.asIdeal.under ℤ = Ideal.span {(p : ℤ)} := by
    refine (hspan.eq_of_le (Ideal.IsPrime.under ℤ v.asIdeal).ne_top ?_).symm
    rw [Ideal.span_singleton_le_iff_mem, Ideal.under, Ideal.mem_comap, map_natCast]
    exact hpv
  haveI : v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := ⟨hvZ.symm⟩
  have hsurj : Function.Surjective (algebraMap ℤ (𝓞 ℚ)) := fun y => ⟨Rat.ringOfIntegersEquiv y, by
    have h : (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) = algebraMap ℤ (𝓞 ℚ) :=
      Subsingleton.elim _ _
    rw [← h]
    exact Rat.ringOfIntegersEquiv.symm_apply_apply y⟩
  have hv1 : v.asIdeal.inertiaDeg ℤ = 1 := by
    letI := Ideal.Quotient.field (Ideal.span {(p : ℤ)})
    letI := Ideal.Quotient.field v.asIdeal
    rw [Ideal.inertiaDeg_eq_of_isMaximal (Ideal.span {(p : ℤ)}) v.asIdeal,
      finrank_eq_one_iff_of_nonzero (1 : 𝓞 ℚ ⧸ v.asIdeal) one_ne_zero, eq_top_iff]
    rintro y -
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, rfl⟩ := hsurj y
    rw [Submodule.mem_span_singleton]
    refine ⟨Ideal.Quotient.mk _ a, ?_⟩
    rw [Algebra.smul_def, mul_one]
    rfl
  obtain ⟨⟨P, hPp, hPl⟩⟩ := v.asIdeal.nonempty_primesOver (S := 𝓞 C)
  have hPne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P
  have hs := hspl ⟨P, hPp, hPne⟩ hPl
  haveI : P.LiesOver (Ideal.span {(p : ℤ)}) := Ideal.LiesOver.trans P v.asIdeal _
  have ht := Ideal.inertiaDeg_tower (R := ℤ) v.asIdeal P
  rw [hv1, one_mul, hs.2, IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd p C P hpN] at ht
  rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_one]
  exact orderOf_eq_one_iff.mp ht
end

section

open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.cycIne :
    ∀ (N : ℕ) [NeZero N] (C : Type) [Field C] [NumberField C] [IsCyclotomicExtension {N} ℚ C] (ζ : C) (p : ℕ), p.Prime → IsPrimitiveRoot ζ N → ∀ w : HeightOneSpectrum (𝓞 C), (p : 𝓞 C) ∈ w.asIdeal → ∀ (σ : Gal(C/ℚ)) (a : ℕ), σ ζ = ζ ^ a → (σ ∈ w.asIdeal.inertia Gal(C/ℚ) ↔ a ≡ 1 [MOD ordCompl[p] N]) ∧ (σ ∈ MulAction.stabilizer Gal(C/ℚ) w.asIdeal ↔ ∃ i : ℕ, a ≡ p ^ i [MOD ordCompl[p] N]) := by
  intro N _ C _ _ _ ζ p hp hζ w hw σ a hσ
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := w.isPrime
  haveI : w.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := by
    have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
      ((Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2
        (Nat.prime_iff_prime_int.1 hp)).isMaximal (by simpa using hp.ne_zero)
    refine ⟨hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_⟩
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_under]
    simpa using hw
  have hne : NeZero (ordCompl[p] N) := ⟨(Nat.ordCompl_pos p (NeZero.ne N)).ne'⟩
  have hmem : ∀ H : Subgroup Gal(C/ℚ), σ ∈ H ↔ IsCyclotomicExtension.Rat.galEquivZMod N C σ ∈
      H.map (IsCyclotomicExtension.Rat.galEquivZMod N C).toMonoidHom := fun H =>
    (Subgroup.mem_map_iff_mem (f := (IsCyclotomicExtension.Rat.galEquivZMod N C).toMonoidHom)
      (IsCyclotomicExtension.Rat.galEquivZMod N C).injective).symm
  have ha : ((IsCyclotomicExtension.Rat.galEquivZMod N C σ : (ZMod N)ˣ) : ZMod N) = (a : ZMod N) := by
    have h := IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq N C σ hζ.pow_eq_one
    rw [hσ, (hζ.isOfFinOrder (NeZero.ne _)).pow_inj_mod, ← hζ.eq_orderOf,
      ← ZMod.natCast_eq_natCast_iff', ZMod.natCast_zmod_val] at h
    exact h.symm
  have hb : ((ZMod.unitsMap (Nat.ordCompl_dvd N p) (IsCyclotomicExtension.Rat.galEquivZMod N C σ) :
      (ZMod (ordCompl[p] N))ˣ) : ZMod (ordCompl[p] N)) = (a : ZMod (ordCompl[p] N)) := by
    rw [ZMod.unitsMap_val, ha, ZMod.cast_natCast (Nat.ordCompl_dvd N p)]
  constructor
  · rw [hmem, KStar.Ram.map_inertia_eq p, KStar.Ram.inertiaUnits, MonoidHom.mem_ker, Units.ext_iff, hb,
      ← ZMod.natCast_eq_natCast_iff, Nat.cast_one, Units.val_one]
  · rw [hmem, KStar.Ram.map_stabilizer_eq p, KStar.Ram.decompUnits, Subgroup.mem_comap,
      ← mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff]
    refine exists_congr fun i => ?_
    rw [Units.ext_iff, hb, ← ZMod.natCast_eq_natCast_iff, Units.val_pow_eq_pow_val,
      ZMod.coe_unitOfCoprime, Nat.cast_pow, eq_comm]
end

section

open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.ineCard :
    (∀ (k L : Type) [Field k] [NumberField k] [Field L] [NumberField L] [Algebra k L] [IsGalois k L] (w : HeightOneSpectrum (𝓞 L)), Nat.card (w.asIdeal.inertia Gal(L/k)) = w.asIdeal.ramificationIdx (𝓞 k)) ∧ ∀ (L : Type) [Field L] [NumberField L] [IsGalois ℚ L] (w : HeightOneSpectrum (𝓞 L)), Nat.card (w.asIdeal.inertia Gal(L/ℚ)) = w.asIdeal.ramificationIdx ℤ := by
  refine ⟨fun k L _ _ _ _ _ _ w => ?_, fun L _ _ _ w => ?_⟩
  · rw [Ideal.card_inertia_eq_ramificationIdxIn (w.asIdeal.under (𝓞 k)) w.asIdeal,
      Ideal.ramificationIdxIn_eq_ramificationIdx (w.asIdeal.under (𝓞 k)) w.asIdeal Gal(L/k)]
  · rw [Ideal.card_inertia_eq_ramificationIdxIn (w.asIdeal.under ℤ) w.asIdeal,
      Ideal.ramificationIdxIn_eq_ramificationIdx (w.asIdeal.under ℤ) w.asIdeal Gal(L/ℚ)]
end
