module

public import Development.AutomorphicArithmetic.FrobeniusLocalisation.DiffDefs
public import Development.AutomorphicArithmetic.PrimeDiscriminants.SlopeTestRemainingChoices
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.RdArith
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.SizeDefs
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.Bundle001
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.CoprimeTwoPow
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

private theorem card_map_dvd {G G' : Type*} [Group G] [Group G'] (a : G →* G') {A B : Subgroup G} (h : A ≤ B) :
    Nat.card (B.map a) ∣ Nat.card (A.map a) * A.relIndex B := by
  have hAB : A.map a ≤ B.map a := Subgroup.map_mono h
  have hc : Nat.card (B.map a) = Nat.card (A.map a) * (A.map a).relIndex (B.map a) := by
    rw [Subgroup.relIndex, ← Subgroup.card_mul_index ((A.map a).subgroupOf (B.map a))]
    congr 1
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAB).toEquiv
  rw [hc]
  apply mul_dvd_mul_left
  rw [← Subgroup.relIndex_comap]
  exact Subgroup.relIndex_dvd_of_le_left B (Subgroup.le_comap_map a A)

private theorem index_unitsOne {φ : Frame} (H : HostRaw φ) {f : ℕ} (hf : f ∣ H.condN) :
    (H.unitsOne f).index = f.totient := by
  have hN : H.condN ≠ 0 := H.condN_ne_zero
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hN (zero_dvd_iff.1 hf)
  have hg : Nat.gcd f H.condN = f := Nat.gcd_eq_left hf
  haveI : NeZero (Nat.gcd f H.condN) := ⟨by rw [hg]; exact hf0⟩
  unfold HostRaw.unitsOne
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 (ZMod.unitsMap_surjective _), Subgroup.card_top,
    Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, hg]

theorem UpperTheory.HF.card_imgOne_dvd :
    ∀ {φ : Frame} (H : HostRaw φ) {f g : ℕ}, f ∣ g → g ∣ H.condN → Nat.card (H.imgOne f) ∣ Nat.card (H.imgOne g) * (g.totient / f.totient) := by
  intro φ H f g hfg hg
  have hf : f ∣ H.condN := hfg.trans hg
  have hle : H.unitsOne g ≤ H.unitsOne f := by
    intro u hu
    rw [H.mem_unitsOne hg] at hu
    rw [H.mem_unitsOne hf]
    exact Nat.ModEq.of_dvd hfg hu
  have hd := card_map_dvd H.art hle
  have hidx := Subgroup.relIndex_mul_index hle
  rw [index_unitsOne H hf, index_unitsOne H hg] at hidx
  have hf0 : 0 < f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · exfalso
      subst h0
      exact H.condN_ne_zero (zero_dvd_iff.1 hf)
    · exact h0
  have htot : 0 < f.totient := Nat.totient_pos.2 hf0
  have hr : g.totient / f.totient = (H.unitsOne g).relIndex (H.unitsOne f) := by
    rw [← hidx, Nat.mul_div_cancel _ htot]
  rw [hr]
  exact hd
end

section

open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

private theorem exists_unit {N l : ℕ} (hN : N ≠ 0) (hl : l.Prime) :
    ∃ u : (ZMod N)ˣ, (u : ZMod N).val ≡ l [MOD ordCompl[l] N] ∧ (u : ZMod N).val ≡ 1 [MOD ordProj[l] N] := by
  have hcl : Nat.Coprime l (ordCompl[l] N) := Nat.coprime_ordCompl hl hN
  have hcop : Nat.Coprime (ordCompl[l] N) (ordProj[l] N) := (Nat.Coprime.pow_left _ hcl).symm
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hcop l 1
  have hc1 : Nat.Coprime k (ordCompl[l] N) := by
    unfold Nat.Coprime
    rw [Nat.ModEq.gcd_eq hk1]
    exact hcl
  have hc2 : Nat.Coprime k (ordProj[l] N) := by
    unfold Nat.Coprime
    rw [Nat.ModEq.gcd_eq hk2]
    simp
  have hco : Nat.Coprime k N := by
    have h := Nat.Coprime.mul_right hc2 hc1
    rwa [Nat.ordProj_mul_ordCompl_eq_self] at h
  refine ⟨ZMod.unitOfCoprime k hco, ?_, ?_⟩
  · rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
    exact ((Nat.mod_modEq k N).of_dvd (Nat.ordCompl_dvd N l)).trans hk1
  · rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
    exact ((Nat.mod_modEq k N).of_dvd (Nat.ordProj_dvd N l)).trans hk2

private theorem unit_unique {N l : ℕ} (hN : N ≠ 0) (hl : l.Prime) {u v : (ZMod N)ˣ}
    (h1 : (u : ZMod N).val ≡ (v : ZMod N).val [MOD ordCompl[l] N])
    (h2 : (u : ZMod N).val ≡ (v : ZMod N).val [MOD ordProj[l] N]) : u = v := by
  have hcop : Nat.Coprime (ordProj[l] N) (ordCompl[l] N) :=
    Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hl hN)
  have h := (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨h2, h1⟩
  rw [Nat.ordProj_mul_ordCompl_eq_self] at h
  haveI : NeZero N := ⟨hN⟩
  apply Units.ext
  apply ZMod.val_injective
  have hu := ZMod.val_lt (u : ZMod N)
  have hv := ZMod.val_lt (v : ZMod N)
  unfold Nat.ModEq at h
  rwa [Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt hv] at h

private theorem val_iff {N f : ℕ} [NeZero N] (hf : f ∣ N) (u : (ZMod N)ˣ) (a : ℕ) :
    (u : ZMod N).val ≡ a [MOD f] ↔ ((ZMod.unitsMap hf u : (ZMod f)ˣ) : ZMod f) = (a : ZMod f) := by
  rw [ZMod.unitsMap_val, ZMod.cast_eq_val, ZMod.natCast_eq_natCast_iff]

theorem UpperTheory.HF.artL_spec :
    ∀ {φ : Frame} (H : HostRaw φ) {l : ℕ}, l.Prime → (∃ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ l [MOD ordCompl[l] H.condN] ∧ (u : ZMod H.condN).val ≡ 1 [MOD ordProj[l] H.condN] ∧ H.artL l = H.art u) ∧ (∀ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ l [MOD ordCompl[l] H.condN] → (u : ZMod H.condN).val ≡ 1 [MOD ordProj[l] H.condN] → H.art u = H.artL l) ∧ ∀ g : φ.GG, g ∈ H.decG l ↔ ∃ (u : (ZMod H.condN)ˣ) (k : ℕ), (u : ZMod H.condN).val ≡ l ^ k [MOD ordCompl[l] H.condN] ∧ g = H.art u := by
  intro φ H l hl
  haveI : NeZero H.condN := ⟨H.condN_ne_zero⟩
  have hN : H.condN ≠ 0 := H.condN_ne_zero
  have hex := exists_unit hN hl
  have hart : H.artL l = H.art hex.choose := by
    unfold UpperTheory.HF.Formalism.HC.HostRaw.artL
    rw [dite_eq_left hex]
  obtain ⟨hc1, hc2⟩ := hex.choose_spec
  have part2 : ∀ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ l [MOD ordCompl[l] H.condN] →
      (u : ZMod H.condN).val ≡ 1 [MOD ordProj[l] H.condN] → H.art u = H.artL l := by
    intro u hu1 hu2
    rw [hart, unit_unique hN hl (hu1.trans hc1.symm) (hu2.trans hc2.symm)]
  refine ⟨⟨hex.choose, hc1, hc2, hart⟩, part2, ?_⟩
  have hA : ordCompl[l] H.condN ∣ H.condN := Nat.ordCompl_dvd _ _
  haveI : NeZero (ordCompl[l] H.condN) :=
    ⟨fun h => hN (Nat.eq_zero_of_zero_dvd (h ▸ hA))⟩
  obtain ⟨lA, hlA⟩ : ∃ w : (ZMod (ordCompl[l] H.condN))ˣ, (w : ZMod (ordCompl[l] H.condN)) = (l : ZMod _) :=
    ⟨ZMod.unitOfCoprime l (Nat.coprime_ordCompl hl hN), ZMod.coe_unitOfCoprime _ _⟩
  have key : ∀ (u : (ZMod H.condN)ˣ) (k : ℕ),
      (u : ZMod H.condN).val ≡ l ^ k [MOD ordCompl[l] H.condN] ↔ ZMod.unitsMap hA u = lA ^ k := by
    intro u k
    rw [val_iff hA u (l ^ k), Units.ext_iff, Units.val_pow_eq_pow_val, hlA, Nat.cast_pow]
  let T : Subgroup φ.GG := ((Subgroup.zpowers lA).comap (ZMod.unitsMap hA)).map H.art
  have memT : ∀ g, g ∈ T ↔ ∃ (u : (ZMod H.condN)ˣ) (k : ℕ),
      (u : ZMod H.condN).val ≡ l ^ k [MOD ordCompl[l] H.condN] ∧ g = H.art u := by
    intro g
    simp only [T, Subgroup.mem_map, Subgroup.mem_comap, ← mem_powers_iff_mem_zpowers,
      Submonoid.mem_powers_iff]
    constructor
    · rintro ⟨u, ⟨k, hk⟩, rfl⟩
      exact ⟨u, k, (key u k).mpr hk.symm, rfl⟩
    · rintro ⟨u, k, hk, rfl⟩
      exact ⟨u, ⟨k, ((key u k).mp hk).symm⟩, rfl⟩
  have hle1 : UpperTheory.HF.Formalism.HC.HostRaw.decG H l ≤ T := by
    unfold UpperTheory.HF.Formalism.HC.HostRaw.decG
    refine sup_le ?_ ?_
    · intro g hg
      obtain ⟨u, hu, rfl⟩ := (UpperTheory.HF.Formalism.HC.HostRaw.mem_inertG H l g).mp hg
      exact (memT _).mpr ⟨u, 0, by simpa using hu, rfl⟩
    · rw [Subgroup.zpowers_le, hart]
      exact (memT _).mpr ⟨hex.choose, 1, by simpa using hc1, rfl⟩
  have hu1 : ZMod.unitsMap hA hex.choose = lA := by
    have h := (key hex.choose 1).mp (by simpa using hc1)
    simpa using h
  have hle2 : T ≤ UpperTheory.HF.Formalism.HC.HostRaw.decG H l := by
    intro g hg
    obtain ⟨u, k, hk, rfl⟩ := (memT g).mp hg
    have hw : ((u * (hex.choose ^ k)⁻¹ : (ZMod H.condN)ˣ) : ZMod H.condN).val ≡ 1
        [MOD ordCompl[l] H.condN] := by
      have h := (key (u * (hex.choose ^ k)⁻¹) 0).mpr
        (by rw [map_mul, map_inv, map_pow, hu1, (key u k).mp hk]; simp)
      simpa using h
    have hmem : H.art (u * (hex.choose ^ k)⁻¹) ∈ UpperTheory.HF.Formalism.HC.HostRaw.inertG H l :=
      (UpperTheory.HF.Formalism.HC.HostRaw.mem_inertG H l _).mpr ⟨_, hw, rfl⟩
    have heq : H.art u = H.art (u * (hex.choose ^ k)⁻¹) * H.artL l ^ k := by
      rw [hart, map_mul, map_inv, map_pow, inv_mul_cancel_right]
    rw [heq]
    unfold UpperTheory.HF.Formalism.HC.HostRaw.decG
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hmem)
      (Subgroup.pow_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)) _)
  intro g
  rw [show UpperTheory.HF.Formalism.HC.HostRaw.decG H l = T from le_antisymm hle1 hle2]
  exact memT g
end

section

open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

theorem UpperTheory.HF.log_rd_sum :
    ∀ {φ : Frame} (H : HostAx φ), Real.log H.rd = ∑ l ∈ H.ram, H.vdH l * Real.log l ∧ Real.log H.rd = ∑ l ∈ H.condN.primeFactors, H.vdH l * Real.log l ∧ H.ram ⊆ H.condN.primeFactors ∧ 0 < H.rd := by
  intro φ H
  have hd : discr H.E ≠ 0 := discr_ne_zero H.E
  have hd' : (discr H.E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 hd
  have habs : |(discr H.E : ℝ)| = ((discr H.E).natAbs : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hpos : 0 < |(discr H.E : ℝ)| := abs_pos.2 (Int.cast_ne_zero.2 hd)
  have h1 : Real.log H.rd = ∑ l ∈ H.ram, H.vdH l * Real.log l := by
    unfold HostRaw.rd HostRaw.ram HostRaw.vdH
    rw [Real.log_rpow hpos, habs, Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [Nat.factorization_def _ (Nat.prime_of_mem_primeFactors hl)]
    rw [Nat.padicValNat_def]
    ring
  have h3 : H.ram ⊆ H.condN.primeFactors := by
    intro l hl
    have h := Nat.mem_primeFactors.1 hl
    exact Nat.mem_primeFactors.2 ⟨h.1, H.der.discr_primes.1 l h.1 (Int.natCast_dvd.2 h.2.1), H.condN_ne_zero⟩
  refine ⟨h1, ?_, h3, Real.rpow_pos_of_pos hpos _⟩
  rw [h1]
  refine Finset.sum_subset h3 fun l hl hn => ?_
  have hp := Nat.prime_of_mem_primeFactors hl
  have : ¬ l ∣ (discr H.E).natAbs := fun h => hn (Nat.mem_primeFactors.2 ⟨hp, h, hd'⟩)
  unfold HostRaw.vdH
  rw [Nat.padicValNat_def, multiplicity_eq_zero_of_not_dvd this]
  simp
end

section

open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

theorem UpperTheory.HF.rho_art :
    ∀ {φ : Frame} (H : HostRaw φ) {f : ℕ}, f ∣ H.condN → Formalism.HC.Der.Rd.rho H.art.ker f = 1 - 1 / (Nat.card (H.imgOne f) : ℝ) := by
  intro φ H f hf
  classical
  rw [Formalism.HC.Der.Rd.rho_eq _ hf]
  have h1 := (H.art.ker.subgroupOf (H.unitsOne f)).card_mul_index
  have h2 : (H.art.ker.subgroupOf (H.unitsOne f)).index = Nat.card (H.imgOne f) :=
    Subgroup.relIndex_ker (H.unitsOne f) H.art
  have h3 : Nat.card (H.unitsOne f) = (Formalism.HC.Der.Rd.KK H.condN f).card := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun u => by
      rw [Formalism.HC.Der.Rd.mem_KK, H.mem_unitsOne hf])
  have h4 : Nat.card (H.art.ker.subgroupOf (H.unitsOne f)) =
      ((Formalism.HC.Der.Rd.KK H.condN f).filter fun u => u ∈ H.art.ker).card := by
    rw [← Nat.card_eq_finsetCard]
    refine Nat.card_congr ((Equiv.subtypeSubtypeEquivSubtypeInter (fun u => u ∈ H.unitsOne f)
      (fun u => u ∈ H.art.ker)).trans (Equiv.subtypeEquivRight fun u => ?_))
    rw [Finset.mem_filter, Formalism.HC.Der.Rd.mem_KK, H.mem_unitsOne hf]
  rw [h2, h3, h4] at h1
  have h5 := Formalism.HC.Der.Rd.card_KK hf
  rw [← h1] at h5
  have h6 := congrArg (Nat.cast : ℕ → ℝ) h5
  push_cast at h6
  have hN : (H.condN.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos H.condN)).ne'
  have hI : (Nat.card (H.imgOne f) : ℝ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  congr 1
  rw [div_eq_div_iff hN hI, one_mul, ← h6]
  rw [mul_right_comm]
  congr!
end

section

open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

theorem UpperTheory.HF.imgOne_gcd :
    ∀ {φ : Frame} (H : HostRaw φ) {f g : ℕ}, f ∣ H.condN → g ∣ H.condN → H.imgOne (Nat.gcd f g) = H.imgOne f ⊔ H.imgOne g := by
  intro φ H f g hf hg
  have hgcd : Nat.gcd f g ∣ H.condN := (Nat.gcd_dvd_left f g).trans hf
  apply le_antisymm
  · rintro x hx
    rw [H.mem_imgOne hgcd] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    have key := Der.Rd.KK_gcd (N := H.condN) ((H.imgOne f ⊔ H.imgOne g).comap H.art) hf hg
      (fun v hv => Subgroup.mem_sup_left ((H.mem_imgOne hf _).2 ⟨v, Der.Rd.mem_KK.1 hv, rfl⟩))
      (fun v hv => Subgroup.mem_sup_right ((H.mem_imgOne hg _).2 ⟨v, Der.Rd.mem_KK.1 hv, rfl⟩))
      u (Der.Rd.mem_KK.2 hu)
    exact key
  · exact sup_le (H.imgOne_anti (Nat.gcd_dvd_left f g) hf) (H.imgOne_anti (Nat.gcd_dvd_right f g) hg)
end

section

open UpperTheory.HF

open NumberField IntermediateField Ideal Formalism.FrobeniusOrbits Formalism.HC
open scoped Pointwise

private theorem two_pow_dvd_sq_pm_one_iff_of_odd (a : ℤ) (ha : Odd a) (k : ℕ) :
    ((2:ℤ) ^ (k + 1 + 1) ∣ a ^ 2 - 1 ∨ (2:ℤ) ^ (k + 1 + 1) ∣ a ^ 2 + 1) ↔
      ((2:ℤ) ^ (k + 1) ∣ a - 1 ∨ (2:ℤ) ^ (k + 1) ∣ a + 1) := by
  obtain ⟨t, rfl⟩ := ha
  constructor
  · rintro (h | h)
    · have e1 : (2 * t + 1) ^ 2 - 1 = 2 ^ 2 * (t * (t + 1)) := by ring
      have e2 : (2:ℤ) ^ (k + 1 + 1) = 2 ^ 2 * 2 ^ k := by ring
      rw [e1, e2] at h
      have h' : (2:ℤ) ^ k ∣ t * (t + 1) := (mul_dvd_mul_iff_left (by norm_num)).1 h
      rcases Int.even_or_odd t with ⟨r, hr⟩ | ⟨r, hr⟩
      · have hc : IsCoprime ((2:ℤ) ^ k) (t + 1) := by
          apply IsCoprime.pow_left
          exact ⟨-r, 1, by rw [hr]; ring⟩
        obtain ⟨c, hc'⟩ := hc.dvd_of_dvd_mul_right h'
        exact Or.inl ⟨c, by rw [hc']; ring⟩
      · have hc : IsCoprime ((2:ℤ) ^ k) t := by
          apply IsCoprime.pow_left
          exact ⟨-r, 1, by rw [hr]; ring⟩
        rw [mul_comm] at h'
        obtain ⟨c, hc'⟩ := hc.dvd_of_dvd_mul_right h'
        exact Or.inr ⟨c, by linear_combination 2 * hc'⟩
    · exfalso
      have h4 : (4:ℤ) ∣ (2:ℤ) ^ (k + 1 + 1) := ⟨2 ^ k, by ring⟩
      have h5 := dvd_trans h4 h
      have e1 : (2 * t + 1) ^ 2 + 1 = 4 * (t ^ 2 + t) + 2 := by ring
      rw [e1] at h5
      generalize t ^ 2 + t = s at h5
      omega
  · rintro (⟨c, hc⟩ | ⟨c, hc⟩)
    · exact Or.inl ⟨c * (2 ^ k * c + 1), by linear_combination (2 * t + 2 ^ (k + 1) * c + 2) * hc⟩
    · exact Or.inl ⟨c * (2 ^ k * c - 1), by linear_combination (2 * t + 2 ^ (k + 1) * c) * hc⟩

private theorem two_pow_dvd_pow_two_pow_sub_or_add_iff (j : ℕ) : ∀ (a : ℤ), Odd a → ∀ k : ℕ,
    ((2:ℤ) ^ (k + 1 + j) ∣ a ^ (2 ^ j) - 1 ∨ (2:ℤ) ^ (k + 1 + j) ∣ a ^ (2 ^ j) + 1) ↔
      ((2:ℤ) ^ (k + 1) ∣ a - 1 ∨ (2:ℤ) ^ (k + 1) ∣ a + 1) := by
  induction j with
  | zero => intro a _ k; simp
  | succ j ih =>
    intro a ha k
    have h1 : (a ^ 2) ^ (2 ^ j) = a ^ (2 ^ (j + 1)) := by rw [← pow_mul, ← pow_succ']
    have h2 : k + 1 + (j + 1) = (k + 1) + 1 + j := by omega
    rw [← h1, h2, ih (a ^ 2) ha.pow (k + 1)]
    exact two_pow_dvd_sq_pm_one_iff_of_odd a ha k

private theorem cast_eq_one_or_neg_one_iff_dvd (n : ℕ) (a : ℤ) :
    ((a : ZMod n) = 1 ∨ (a : ZMod n) = -1) ↔ ((n : ℤ) ∣ a - 1 ∨ (n : ℤ) ∣ a + 1) := by
  have e1 : ((a : ZMod n) = 1) ↔ (((a - 1 : ℤ) : ZMod n) = 0) := by
    push_cast; exact sub_eq_zero.symm
  have e2 : ((a : ZMod n) = -1) ↔ (((a + 1 : ℤ) : ZMod n) = 0) := by
    push_cast; exact eq_neg_iff_add_eq_zero
  rw [e1, e2, ZMod.intCast_zmod_eq_zero_iff_dvd, ZMod.intCast_zmod_eq_zero_iff_dvd]

theorem UpperTheory.HF.frob_h_order :
    ∀ (φ : Frame) (H : HostAx φ) (p : ℕ), p.Prime → ¬ p ∣ H.condN →
      (∀ j : ℕ, orderOf (φ.hH (H.frobG p).2) ≤ 2 ^ j ↔
        ((p : ZMod (2 ^ (φ.e + 2 - j))) = 1 ∨ (p : ZMod (2 ^ (φ.e + 2 - j))) = -1)) ∧
      (∃ j ≤ φ.e, orderOf (φ.hH (H.frobG p).2) = 2 ^ j) ∧
      2 ^ (φ.e + 2) ≤ (p + 1) * orderOf (φ.hH (H.frobG p).2) ∧
      (φ.hH (H.frobG p).2 = 1 ↔ ((p : ZMod (2 ^ (φ.e + 2))) = 1 ∨ (p : ZMod (2 ^ (φ.e + 2))) = -1)) := by
  intro φ H p hp hpN
  haveI := Fact.mk hp
  obtain ⟨-, -, -, -, -, v, hv, hx⟩ := frobG_spec φ H p hpN
  rw [hx]
  set x := hcl φ.e v with hxdef
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact hpN (HostRaw.two_dvd_condN _)
  have hodd : Odd (p : ℤ) := (Int.odd_coe_nat p).2 (hp.odd_of_ne_two hp2)
  have key : ∀ k : ℕ, x ^ k = 1 ↔
      ((2:ℤ) ^ (φ.e + 2) ∣ (p : ℤ) ^ k - 1 ∨ (2:ℤ) ^ (φ.e + 2) ∣ (p : ℤ) ^ k + 1) := by
    intro k
    rw [hxdef, Group.hcl_pow_eq_one]
    simp only [Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, hv]
    have hc := cast_eq_one_or_neg_one_iff_dvd (2 ^ (φ.e + 2)) ((p : ℤ) ^ k)
    push_cast at hc
    exact hc
  have hx4 : x ^ (2 ^ φ.e) = 1 := by
    rw [key]
    have h := (two_pow_dvd_pow_two_pow_sub_or_add_iff φ.e (p : ℤ) hodd 1).2 (by
      obtain ⟨t, ht⟩ := hodd
      rw [ht]
      have : (2:ℤ) ^ (1 + 1) = 4 := by norm_num
      rw [this]
      omega)
    rwa [show 1 + 1 + φ.e = φ.e + 2 by omega] at h
  obtain ⟨i, hi, hord⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hx4)
  have cl1 : ∀ j : ℕ, orderOf x ≤ 2 ^ j ↔
      ((p : ZMod (2 ^ (φ.e + 2 - j))) = 1 ∨ (p : ZMod (2 ^ (φ.e + 2 - j))) = -1) := by
    intro j
    by_cases hj : j ≤ φ.e + 1
    · obtain ⟨m, hm⟩ : ∃ m, φ.e + 2 - j = m + 1 := ⟨φ.e + 1 - j, by omega⟩
      rw [hm]
      have hc := cast_eq_one_or_neg_one_iff_dvd (2 ^ (m + 1)) (p : ℤ)
      push_cast at hc
      rw [hc, ← two_pow_dvd_pow_two_pow_sub_or_add_iff j (p : ℤ) hodd m, show m + 1 + j = φ.e + 2 by omega, ← key,
        ← orderOf_dvd_iff_pow_eq_one, hord, Nat.pow_dvd_pow_iff_le_right (by norm_num),
        Nat.pow_le_pow_iff_right (by norm_num)]
    · have h0 : φ.e + 2 - j = 0 := by omega
      rw [h0, hord]
      haveI : Subsingleton (ZMod (2 ^ 0)) := ZMod.subsingleton_iff.2 (by norm_num)
      constructor
      · intro _
        exact Or.inl (Subsingleton.elim _ _)
      · intro _
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
  refine ⟨cl1, ⟨i, hi, hord⟩, ?_, ?_⟩
  · have h := (cl1 i).1 (le_of_eq hord)
    have hc := cast_eq_one_or_neg_one_iff_dvd (2 ^ (φ.e + 2 - i)) (p : ℤ)
    push_cast at hc
    have h2p := hp.two_le
    have hb : ((2 ^ (φ.e + 2 - i) : ℕ) : ℤ) ≤ (p : ℤ) + 1 := by
      push_cast
      rcases hc.1 h with hd | hd
      · have := Int.le_of_dvd (by omega) hd
        linarith
      · exact Int.le_of_dvd (by omega) hd
    have hb' : 2 ^ (φ.e + 2 - i) ≤ p + 1 := by exact_mod_cast hb
    calc 2 ^ (φ.e + 2) = 2 ^ (φ.e + 2 - i) * 2 ^ i := by
          rw [← pow_add]
          congr 1
          omega
      _ ≤ (p + 1) * 2 ^ i := Nat.mul_le_mul_right _ hb'
      _ = (p + 1) * orderOf x := by rw [hord]
  · have h := key 1
    simp only [pow_one] at h
    rw [h]
    have hc := cast_eq_one_or_neg_one_iff_dvd (2 ^ (φ.e + 2)) (p : ℤ)
    push_cast at hc
    rw [hc]
end
