module

public import Development.AutomorphicArithmetic.PrimitiveCosets.RecH
public import Development.AutomorphicArithmetic.PrimitiveCosets.ToEBij
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
public import Formalism.SizeWindowBrackets.ChainSlopeWindows.GaloisMapComplexConjugation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.Lemma
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
import Development.AutomorphicArithmetic.DedekindLFunctions.SplitInertia
import Formalism.SizeWindowBrackets.Bundle002

@[expose] public section

section

open UpperTheory.Comparison₂ Formalism Formalism.HC Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.LHost NumberField Ideal

private theorem UpperTheory.GL.df_modEq_iff {N M : ℕ} [NeZero N] (x : ZMod N) (a : ℕ) :
    x.val ≡ a [MOD M] ↔ (x.cast : ZMod M) = (a : ZMod M) := by
  rw [← ZMod.natCast_val, ZMod.natCast_eq_natCast_iff]

private theorem UpperTheory.GL.df_mem_local {N : ℕ} [NeZero N] (p : ℕ) (u : (ZMod N)ˣ) :
    u ∈ Formalism.LFunctionChainParameters.LHost.localUnits N p ↔ (u : ZMod N).val ≡ 1 [MOD ordCompl[p] N] := by
  rw [UpperTheory.GL.df_modEq_iff, Nat.cast_one, Formalism.LFunctionChainParameters.LHost.localUnits, MonoidHom.mem_ker, Units.ext_iff,
    ZMod.unitsMap_val, Units.val_one]

private theorem UpperTheory.GL.df_mem_frob {N : ℕ} [NeZero N] (p : ℕ) (hp : p.Prime) (u : (ZMod N)ˣ) :
    u * (frobUnit N p)⁻¹ ∈ Formalism.LFunctionChainParameters.LHost.localUnits N p ↔ (u : ZMod N).val ≡ p [MOD ordCompl[p] N] := by
  have hw := (frobenius_unit_spec N p (NeZero.ne N) hp).1.1
  rw [UpperTheory.GL.df_modEq_iff, Formalism.LFunctionChainParameters.LHost.localUnits, MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one,
    Units.ext_iff, ZMod.unitsMap_val, ZMod.unitsMap_val, hw]

private theorem UpperTheory.GL.df_inertia {φ : Frame} (H : HostRaw φ) (p : ℕ) (g : φ.GG) :
    (toE φ g).toAdd ∈ (arith H).inertia p ↔ ∃ u ∈ Formalism.LFunctionChainParameters.LHost.localUnits H.condN p, g = H.art u := by
  show Multiplicative.ofAdd (toE φ g).toAdd ∈ Subgroup.map (recH H) (Formalism.LFunctionChainParameters.LHost.localUnits H.condN p) ↔ _
  rw [Subgroup.mem_map]
  have hinj := ((UpperTheory.Comparison₂.toE_bij φ).1).1
  constructor
  · rintro ⟨u, hu, h⟩
    refine ⟨u, hu, hinj ?_⟩
    exact h.symm
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, rfl⟩

theorem UpperTheory.GL.dataField :
    ∀ {φ : Frame} (H : HostAx φ) (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E),
      ((∀ x : 𝓞 H.E, σ • x - x ∈ P) ↔ (toE φ (H.gal σ)).toAdd ∈ (arith H.toHostRaw).inertia p) ∧
      (IsArithFrobAt ℤ σ P ↔ (toE φ (H.gal σ)).toAdd - (arith H.toHostRaw).frob p ∈ (arith H.toHostRaw).inertia p) := by
  intro φ H p _ P _ _ σ
  have hp : p.Prime := Fact.out
  haveI : NeZero H.condN := ⟨(Nat.mul_pos (Nat.mul_pos H.QS_pos H.hyp.1.pos) H.hyp.2.1.pos).ne'⟩
  constructor
  · rw [H.der.inertia p P σ, UpperTheory.GL.df_inertia]
    simp only [UpperTheory.GL.df_mem_local]
  · have hfr : (arith H.toHostRaw).frob p =
        (toE φ (H.art (Formalism.LFunctionChainParameters.LHost.frobUnit H.condN p))).toAdd := rfl
    rw [hfr, ← toAdd_div, ← map_div, UpperTheory.GL.df_inertia, H.der.frob_any p P σ]
    constructor
    · rintro ⟨u, hu, he⟩
      refine ⟨u * (Formalism.LFunctionChainParameters.LHost.frobUnit H.condN p)⁻¹, (UpperTheory.GL.df_mem_frob p hp u).2 hu, ?_⟩
      rw [he, map_mul, map_inv, div_eq_mul_inv]
    · rintro ⟨v, hv, he⟩
      refine ⟨v * Formalism.LFunctionChainParameters.LHost.frobUnit H.condN p, (UpperTheory.GL.df_mem_frob p hp _).1 (by rwa [mul_inv_cancel_right]), ?_⟩
      rw [map_mul, ← he, div_mul_cancel]
end

section

open UpperTheory.Comparison₂ Formalism Formalism.HC Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.LHost NumberField Ideal

theorem UpperTheory.GL.rec_surj :
    ∀ {φ : Frame} (H : HostAx φ), Function.Surjective (recH H.toHostRaw) ∧ Function.Injective (dirChar (recH H.toHostRaw)) := by
  intro φ H
  have hs : Function.Surjective (recH H.toHostRaw) :=
    (toE_bij φ).1.2.comp H.der.art_surj
  refine ⟨hs, ?_⟩
  intro ψ₁ ψ₂ h
  ext x
  obtain ⟨u, hu⟩ := hs (Multiplicative.ofAdd x)
  have h2 := congrArg (fun χ : DirichletCharacter ℂ H.toHostRaw.condN => χ (u : ZMod H.toHostRaw.condN)) h
  simp only [dirChar_unit, hu, toAdd_ofAdd] at h2
  exact h2
end

section

open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LHost NumberField Ideal

private lemma notInPhi_iff {φ : Frame} (H : HostAx φ) {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (hd : p ≠ H.d) :
    ¬ Formalism.D5.InPhi ((arith H.toHostRaw).frob p) ↔ jacobiSym (-(H.d : ℤ)) p = -1 := by
  have hdp := H.toHostRaw.d_prime
  have hN0 : H.condN ≠ 0 := by
    simp only [HostRaw.condN]
    exact Nat.mul_ne_zero (Nat.mul_ne_zero H.QS_ne_zero H.q_prime.ne_zero) hdp.ne_zero
  haveI : NeZero H.condN := ⟨hN0⟩
  set u := frobUnit H.condN p with hu
  obtain ⟨h1, -⟩ := frobUnit_modEq (N := H.condN) hp
  have hcop : Nat.Coprime (p ^ H.condN.factorization p) H.d :=
    Nat.Coprime.pow_left _ ((Nat.coprime_primes hp hdp).mpr hd)
  have hdm : H.d ∣ H.condN / p ^ H.condN.factorization p := by
    have hsplit := Nat.ordProj_mul_ordCompl_eq_self H.condN p
    have : H.d ∣ p ^ H.condN.factorization p * (H.condN / p ^ H.condN.factorization p) := by
      rw [hsplit]; exact H.d_dvd_condN
    exact (Nat.Coprime.symm hcop).dvd_of_dvd_mul_left this
  have hmod : (u : ZMod H.condN).val ≡ p [MOD H.d] := Nat.ModEq.of_dvd hdm h1
  have hJ : jacobiSym (((u : ZMod H.condN).val : ℕ) : ℤ) H.d = jacobiSym (-(H.d : ℤ)) p := by
    rw [jacobi_congr hmod]
    have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two h2)
    exact (jacobi_neg_recip H.d_mod_four hodd).symm
  have hart := H.der.art_ch u
  rw [hJ] at hart
  show ¬ (Multiplicative.toAdd (LFunctionChainParameters.LHost.sgn2 (H.art u).1.2) = 0) ↔ _
  rw [sgn2_toAdd_eq_zero_iff, ← hart]
  rcases Int.units_eq_one_or (H.art u).1.2 with hs | hs
  · rw [hs]; simp
  · rw [hs]; simp

theorem UpperTheory.GL.isInert_iff :
    ∀ {φ : Frame} (H : HostAx φ) (p : ℕ), IsInert (arith H.toHostRaw) p ↔ p.Prime ∧ ¬ p ∣ H.condN ∧ jacobiSym (-(H.d : ℤ)) p = -1 := by
  intro φ H p
  constructor
  · rintro ⟨hp, h2, -, hd, h⟩
    have hj := (notInPhi_iff H hp h2 hd).1 h
    exact ⟨hp, H.not_dvd_condN_of_inert hp h2 hj, hj⟩
  · rintro ⟨hp, hN, hj⟩
    exact ⟨hp, HostRaw.ne_two_of_not_dvd hN, HostRaw.ne_q_of_not_dvd hN, HostRaw.ne_d_of_not_dvd hN,
      (notInPhi_iff H hp (HostRaw.ne_two_of_not_dvd hN) (HostRaw.ne_d_of_not_dvd hN)).2 hj⟩
end

section

open UpperTheory.Comparison₂ Formalism Formalism.HC Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.LHost NumberField Ideal

theorem UpperTheory.GL.unram :
    ∀ {φ : Frame} (H : HostRaw φ) (p : ℕ) (hc : p.Coprime H.condN), p.Prime →
      (arith H).inertia p = ⊥ ∧ (arith H).frob p = (recH H (ZMod.unitOfCoprime p hc)).toAdd := by
  intro φ H p hc hp
  have hN : H.condN ≠ 0 := (Nat.mul_pos (Nat.mul_pos H.QS_pos H.hyp.1.pos) H.hyp.2.1.pos).ne'
  have hnd : ¬ p ∣ H.condN := fun h => hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hc h)
  obtain ⟨hloc, hfrob⟩ := Formalism.LFunctionChainParameters.LHost.unramified_spec H.condN p hN hp hnd
  constructor
  · show Subgroup.toAddSubgroup' (Subgroup.map (recH H) (Formalism.LFunctionChainParameters.LHost.localUnits H.condN p)) = ⊥
    rw [hloc, Subgroup.map_bot]
    exact Subgroup.toAddSubgroup'.map_bot
  · show (recH H (Formalism.LFunctionChainParameters.LHost.frobUnit H.condN p)).toAdd = _
    have he : Formalism.LFunctionChainParameters.LHost.frobUnit H.condN p = ZMod.unitOfCoprime p hc :=
      Units.ext (by rw [hfrob, ZMod.coe_unitOfCoprime])
    rw [he]
end
