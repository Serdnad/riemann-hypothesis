module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle064
public import Formalism.LocalRingCardinality.DataDIV
public import Mathlib.Algebra.MvPolynomial.Cardinal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle527
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle006
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle003
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle167
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle151
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle150
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle152
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
public import Mathlib.FieldTheory.IsAlgClosed.Classification
public import Mathlib.FieldTheory.PrimeField
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Algebraic.Cardinality
public import Mathlib.RingTheory.Localization.Cardinality
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform

@[expose] public section

section

set_option autoImplicit false

open Formalism.BasicNotions NumberField

namespace GlobalTheory.WittFracComplex


open Cardinal in
theorem nonempty_ringHom_complex_of_le_continuum (K : Type) [Field K] [CharZero K] (hK : #K ≤ 𝔠) :
    Nonempty (K →+* ℂ) := by
  apply _root_.GlobalTheory.FGFieldEmb.nonempty_ringHom_complex_of_mk_le <;> assumption

theorem charZero_wittVector (p : ℕ) [hp : Fact p.Prime] (k : Type) [Field k] [CharP k p] :
    CharZero (WittVector p k) := by
  obtain ⟨q, hq⟩ := CharP.exists (WittVector p k)
  have h1 : ((q : ℕ) : k) = 0 := by
    have := congrArg (WittVector.constantCoeff : WittVector p k →+* k) (CharP.cast_eq_zero (WittVector p k) q)
    rwa [map_natCast, map_zero] at this
  have h2 : p ∣ q := (CharP.cast_eq_zero_iff k p q).1 h1
  rcases CharP.char_is_prime_or_zero (WittVector p k) q with h | h
  · have h3 : p = q := (Nat.prime_dvd_prime_iff_eq hp.out h).1 h2
    subst h3
    exact absurd (CharP.cast_eq_zero (WittVector p k) p) (WittVector.p_nonzero p k)
  · subst h
    exact CharP.charP_to_charZero _


open Cardinal in
theorem mk_wittVector_le (p : ℕ) (k : Type) (hk : #k ≤ ℵ₀) : #(WittVector p k) ≤ 𝔠 := by
  have h : Function.Injective (WittVector.coeff : WittVector p k → ℕ → k) :=
    fun x y h => WittVector.ext (fun n => congrFun h n)
  refine (Cardinal.mk_le_of_injective h).trans ?_
  rw [← Cardinal.power_def, Cardinal.mk_nat, ← Cardinal.aleph0_power_aleph0]
  exact Cardinal.power_le_power_right hk


open Cardinal in
theorem nonempty_ringHom_complex : ∀ (p : ℕ) [Fact p.Prime], Nonempty (DV.KW p →+* ℂ) := by
  intro p _
  have hk : #(AlgebraicClosure (ZMod p)) ≤ ℵ₀ := by
    have := Algebra.IsAlgebraic.cardinalMk_le_max (ZMod p) (AlgebraicClosure (ZMod p))
    rwa [max_eq_right (Cardinal.lt_aleph0_of_finite _).le] at this
  have := charZero_wittVector p (AlgebraicClosure (ZMod p))
  have : CharZero (DV.KW p) :=
    (RingHom.charZero_iff (IsFractionRing.injective (WittVector p (AlgebraicClosure (ZMod p))) (DV.KW p))).1 this
  refine nonempty_ringHom_complex_of_le_continuum _ ?_
  rw [Cardinal.mk_fractionRing]
  exact mk_wittVector_le p _ hk

end GlobalTheory.WittFracComplex
end

section

noncomputable section

open Polynomial

namespace GlobalTheory.Compare.TeichmullerRoots

open Formalism.BasicNotions Formalism.CyclotomicNorms GlobalTheory.IndefiniteRowSideFullHecke.FactorSeriesSupport

section Roots

variable {g : ℕ} [Fact g.Prime]

theorem zero_mem_rootsBar {f : (ZMod g)[X]} (hf : f.Monic) : 0 ∈ rootsBar f ↔ f.coeff 0 = 0 := by
  unfold rootsBar
  rw [mem_roots (hf.map _).ne_zero, IsRoot, ← coeff_zero_eq_eval_zero, coeff_map]
  exact map_eq_zero_iff _ (RingHom.injective _)

theorem exists_monic_of_stable (S : Multiset (Fbar g)) (hS : S.map (fun x => x ^ g) = S) :
    ∃ f : (ZMod g)[X], f.Monic ∧ rootsBar f = S := by
  set P : (Fbar g)[X] := (S.map fun x => X - C x).prod with hP
  have hm : P.Monic := monic_multiset_prod_of_monic _ _ fun x _ => monic_X_sub_C x
  have hfix : P.map (frobenius (Fbar g) g) = P := by
    rw [hP, Polynomial.map_multiset_prod, Multiset.map_map]
    conv_rhs => rw [← hS, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro x _
    simp [frobenius_def]
  have hl : P ∈ lifts (algebraMap (ZMod g) (Fbar g)) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    have h1 : P.coeff n ^ g = P.coeff n := by
      have := congrArg (fun q => q.coeff n) hfix
      simpa [frobenius_def] using this
    have h2 : P.coeff n ∈ (⊥ : Subfield (Fbar g)) := (Subfield.mem_bot_iff_pow_eq_self _ g).2 h1
    rw [Subfield.bot_eq_of_zMod_algebra g] at h2
    exact h2
  obtain ⟨q, hq, -, hqm⟩ := lifts_and_natDegree_eq_and_monic hl hm
  refine ⟨q, hqm, ?_⟩
  unfold rootsBar
  rw [hq, hP, roots_multiset_prod_X_sub_C]

theorem root_pow_rootExp {N : ℕ} {f : (ZMod g)[X]} (hf : IsLabel N f) {x : Fbar g} (hx : x ∈ rootsBar f) :
    x ^ rootExp N g = 1 := by
  have hx0 : x ≠ 0 := fun h => hf.2.2 ((zero_mem_rootsBar hf.1).1 (h ▸ hx))
  have hint : IsIntegral (ZMod g) x := Algebra.IsIntegral.isIntegral x
  have hroot : aeval x f = 0 := by
    have := (mem_roots (hf.1.map _).ne_zero).1 hx
    rwa [IsRoot, eval_map_algebraMap] at this
  have hd : (minpoly (ZMod g) x).natDegree ≤ N := by
    rw [← hf.2.1]
    exact natDegree_le_of_dvd (minpoly.dvd _ _ hroot) hf.1.ne_zero
  have hd1 : 1 ≤ (minpoly (ZMod g) x).natDegree := minpoly.natDegree_pos hint
  set K := IntermediateField.adjoin (ZMod g) ({x} : Set (Fbar g))
  haveI : FiniteDimensional (ZMod g) K := IntermediateField.adjoin.finiteDimensional hint
  haveI : Finite K := Module.finite_of_finite (ZMod g)
  letI : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = g ^ (minpoly (ZMod g) x).natDegree := by
    rw [Module.card_eq_pow_finrank (K := ZMod g), ZMod.card, IntermediateField.adjoin.finrank hint]
  let y : K := ⟨x, IntermediateField.mem_adjoin_simple_self _ x⟩
  have hy : y ≠ 0 := fun h => hx0 (congrArg Subtype.val h)
  have h1 := FiniteField.pow_card_sub_one_eq_one y hy
  rw [hc] at h1
  have h2 : x ^ (g ^ (minpoly (ZMod g) x).natDegree - 1) = 1 := by
    have := congrArg Subtype.val h1
    simpa [y] using this
  obtain ⟨c, hc⟩ : g ^ (minpoly (ZMod g) x).natDegree - 1 ∣ rootExp N g :=
    Finset.dvd_lcm (f := fun d => g ^ d - 1) (Finset.mem_Icc.2 ⟨hd1, hd⟩)
  rw [hc, pow_mul, h2, one_pow]

theorem roots_reverse_prod {F : Type} [Field F] (S : Multiset F) (hS : 0 ∉ S) :
    ((S.map fun x => X - C x).prod.reverse).roots = S.map fun x => x⁻¹ := by
  apply GlobalTheory.DualLabel.roots_reverse_prod <;> assumption

theorem dual_spec {f : (ZMod g)[X]} (hm : f.Monic) (h0 : f.coeff 0 ≠ 0) :
    (C (f.coeff 0)⁻¹ * f.reverse).Monic ∧ IsPowLabel (-1) f (C (f.coeff 0)⁻¹ * f.reverse) := by
  constructor
  · apply monic_C_mul_of_mul_leadingCoeff_eq_one
    rw [reverse_leadingCoeff, trailingCoeff_eq_coeff_zero h0, inv_mul_cancel₀ h0]
  · have e : f.map (algebraMap (ZMod g) (Fbar g)) = ((rootsBar f).map fun x => X - C x).prod :=
      (Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq (hm.map _)
        (IsAlgClosed.card_roots_eq_natDegree)).symm
    have e2 : f.reverse.map (algebraMap (ZMod g) (Fbar g)) = (f.map (algebraMap (ZMod g) (Fbar g))).reverse := by
      rw [reverse, reverse, natDegree_map, reflect_map]
    unfold IsPowLabel
    simp only [zpow_neg_one]
    rw [← roots_reverse_prod _ (fun h => h0 ((zero_mem_rootsBar hm).1 h)), ← e, ← e2]
    unfold rootsBar
    rw [Polynomial.map_mul, map_C, roots_C_mul]
    exact (_root_.map_ne_zero _).2 (inv_ne_zero h0)

theorem teich_injective (t : Fbar g →* ℂ) (ht : ∀ x y, x ≠ 0 → y ≠ 0 → t x = t y → x = y) :
    Function.Injective t := by
  have hne : ∀ x, x ≠ 0 → t x ≠ 0 := fun x hx => ((IsUnit.mk0 x hx).map t).ne_zero
  have h0 : t 0 = 0 := by
    classical
    obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset (Fbar g))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy
    by_contra h
    have : t 0 * t y = t 0 * t 1 := by rw [← map_mul, ← map_mul, zero_mul, zero_mul]
    exact hy.2 (ht _ _ hy.1 one_ne_zero (mul_left_cancel₀ h this))
  intro x y h
  by_cases hx : x = 0
  · by_cases hy : y = 0
    · rw [hx, hy]
    · exact absurd (by rw [← h, hx, h0]) (hne y hy)
  · by_cases hy : y = 0
    · exact absurd (by rw [h, hy, h0]) (hne x hx)
    · exact ht x y hx hy h

theorem teich_zpow (t : Fbar g →* ℂ) {x : Fbar g} (hx : x ≠ 0) (a : ℤ) : t (x ^ a) = t x ^ a := by
  have h1 : t ((Units.mk0 x hx ^ a : (Fbar g)ˣ) : Fbar g) = ((Units.map t (Units.mk0 x hx) ^ a : ℂˣ) : ℂ) := by
    rw [← map_zpow]; rfl
  rw [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val] at h1
  exact h1

end Roots

variable (D : D7)

theorem labAct_eq (k : Fin 2) (α : ℂ ≃+* ℂ) (a : ℤ)
    (ha : ∀ ζ : ℂ, ζ ^ rootExp D.R.r (D.host.g k) = 1 → α ζ = ζ ^ a)
    {f f' : (ZMod (D.host.g k))[X]} (hf : IsLabel D.R.r f) (hm : f'.Monic)
    (hp : haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; IsPowLabel a f f') :
    Formalism.MainNotions.ArithmeticCylinders.labAct D α k f = f' := by
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have hinj := teich_injective (D.ntypes.teichC k) (D.ntypes.teichC_inj k)
  have e : (rootsBar f).map
      (fun x => Function.invFun (D.ntypes.teichC k) (α (D.ntypes.teichC k x))) =
      (rootsBar f).map fun x => x ^ a := by
    apply Multiset.map_congr rfl
    intro x hx
    have hx0 : x ≠ 0 := fun h => hf.2.2 ((zero_mem_rootsBar hf.1).1 (h ▸ hx))
    rw [ha _ (by rw [← map_pow, root_pow_rootExp hf hx, map_one]), ← teich_zpow _ hx0]
    exact Function.leftInverse_invFun hinj _
  have hs := Classical.epsilon_spec (p := fun q : (ZMod (D.host.g k))[X] => q.Monic ∧
    rootsBar q = (rootsBar f).map
      (fun x => Function.invFun (D.ntypes.teichC k) (α (D.ntypes.teichC k x))))
    ⟨f', hm, hp.trans e.symm⟩
  exact IsPowLabel.unique (a := a) (f := f) (hs.2.trans e) hp hs.1 hm

end GlobalTheory.Compare.TeichmullerRoots

end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions

namespace GlobalTheory.Proof.dvr_of_reflects_facts

theorem dvr_of_reflects {O A : Type} [CommRing O] [IsDomain O] [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] (g : O →+* A) (hg : Function.Injective g)
    (hd : ∀ x y, g x ∣ g y → x ∣ y) (t : O) (ht0 : t ≠ 0) (ht : ¬ IsUnit t) :
    IsDiscreteValuationRing O := by
  haveI : ValuationRing O := ValuationRing.iff_dvd_total.2
    ⟨fun x y => (ValuationRing.dvd_total (g x) (g y)).imp (hd x y) (hd y x)⟩
  haveI : WfDvdMonoid O := by
    refine Subrelation.wf (r := InvImage DvdNotUnit g) ?_ (InvImage.wf g wellFounded_dvdNotUnit)
    rintro x y ⟨hx, c, hc, rfl⟩
    refine ⟨fun h => hx (hg (by simpa using h)), g c, fun h => hc ?_, by simp⟩
    exact isUnit_of_dvd_one (hd c 1 (by simpa using h.dvd))
  haveI : IsPrincipalIdealRing O := ((IsBezout.tfae (R := O)).out 4 2).1 ‹WfDvdMonoid O›
  refine { not_a_field' := fun h => ht0 ?_ }
  have : t ∈ IsLocalRing.maximalIdeal O := ht
  rw [h] at this
  simpa using this

theorem common_of_field {O₀ A B K : Type} [CommRing O₀] [IsDomain O₀] [IsDiscreteValuationRing O₀]
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Field K]
    (fA : O₀ →+* A) (fB : O₀ →+* B) (hAi : fA.IsIntegral) (hB : Function.Injective fB)
    (hBl : IsLocalHom fB) (f₀ : O₀ →+* K) (jA : K →+* FractionRing A) (jB : K →+* FractionRing B)
    (hjA : ∀ c, jA (f₀ c) = algebraMap A _ (fA c)) (hjB : ∀ c, jB (f₀ c) = algebraMap B _ (fB c)) :
    ∃ (O₁ : Subring K) (_ : IsDiscreteValuationRing O₁) (f : O₀ →+* O₁) (gA : O₁ →+* A) (gB : O₁ →+* B),
      (∀ x, x ∈ O₁ ↔ ∃ a, algebraMap A _ a = jA x) ∧
      (∀ x, algebraMap A _ (gA x) = jA x) ∧ (∀ x, algebraMap B _ (gB x) = jB x) ∧
      Function.Injective gA ∧ Function.Injective gB ∧ IsLocalHom gA ∧ IsLocalHom gB ∧
      gA.comp f = fA ∧ gB.comp f = fB := by
  have iA := IsFractionRing.injective A (FractionRing A)
  have iB := IsFractionRing.injective B (FractionRing B)
  let O₁ : Subring K := (algebraMap A (FractionRing A)).range.comap jA
  have hmem : ∀ x, x ∈ O₁ ↔ ∃ a, algebraMap A _ a = jA x := fun x => Iff.rfl
  let f : O₀ →+* O₁ := f₀.codRestrict O₁ (fun c => (hmem _).2 ⟨fA c, (hjA c).symm⟩)
  have hf : ∀ c, (f c : K) = f₀ c := fun c => rfl
  have lift : ∀ {C : Type} [CommRing C] [IsDomain C] (j : K →+* FractionRing C),
      (∀ x : O₁, ∃ a, algebraMap C _ a = j x) → ∃ g : O₁ →+* C, ∀ x, algebraMap C _ (g x) = j x := by
    intro C _ _ j h
    have iC := IsFractionRing.injective C (FractionRing C)
    choose g hg using h
    exact ⟨{ toFun := g
             map_one' := iC (by simp [hg])
             map_mul' := fun x y => iC (by simp [hg])
             map_zero' := iC (by simp [hg])
             map_add' := fun x y => iC (by simp [hg]) }, hg⟩
  obtain ⟨gA, hgA⟩ := lift jA (fun x => (hmem x).1 x.2)
  have gAi : Function.Injective gA := fun x y h =>
    Subtype.ext (jA.injective (by rw [← hgA, ← hgA, h]))
  have cA : gA.comp f = fA := RingHom.ext fun c => iA (by rw [RingHom.comp_apply, hgA, hf, hjA])
  have hint : ∀ x : O₁, ∃ a, algebraMap B _ a = jB x := by
    intro x
    obtain ⟨p, hp, hpx⟩ := hAi (gA x)
    have h1 : p.eval₂ f x = 0 := gAi (by rw [Polynomial.hom_eval₂, cA, hpx, map_zero])
    have h2 := congrArg (jB.comp O₁.subtype) h1
    rw [Polynomial.hom_eval₂, map_zero] at h2
    refine IsIntegrallyClosed.algebraMap_eq_of_integral ⟨p.map fB, hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have e : (algebraMap B (FractionRing B)).comp fB = (jB.comp O₁.subtype).comp f :=
      RingHom.ext fun c => (hjB c).symm
    rw [e]
    exact h2
  obtain ⟨gB, hgB⟩ := lift jB hint
  have gBi : Function.Injective gB := fun x y h =>
    Subtype.ext (jB.injective (by rw [← hgB, ← hgB, h]))
  have cB : gB.comp f = fB := RingHom.ext fun c => iB (by rw [RingHom.comp_apply, hgB, hf, hjB])
  have hd : ∀ x y, gA x ∣ gA y → x ∣ y := by
    rintro x y ⟨c, hc⟩
    by_cases hx : x = 0
    · have : y = 0 := gAi (by rw [hc, hx]; simp)
      simp [this]
    have hx' : (x : K) ≠ 0 := fun h => hx (Subtype.ext h)
    have hx'' : jA x ≠ 0 := by simpa using hx'
    refine ⟨⟨y / x, (hmem _).2 ⟨c, ?_⟩⟩, Subtype.ext ?_⟩
    · rw [map_div₀, eq_div_iff hx'', ← hgA, ← hgA, hc, map_mul, mul_comm]
    · simp [mul_div_cancel₀ _ hx']
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O₀
  have hcB : ∀ c, gB (f c) = fB c := fun c => by rw [← cB]; rfl
  have hnu : ¬ IsUnit (gB (f ϖ)) := fun h => hϖ.not_isUnit (hBl.map_nonunit _ (hcB ϖ ▸ h))
  have ht0 : f ϖ ≠ 0 := fun h => hϖ.ne_zero (hB (by rw [← hcB, h, map_zero, map_zero]))
  haveI hD : IsDiscreteValuationRing O₁ :=
    dvr_of_reflects gA gAi hd (f ϖ) ht0 (fun h => hnu (h.map gB))
  refine ⟨O₁, hD, f, gA, gB, hmem, hgA, hgB, gAi, gBi,
    ⟨fun x h => isUnit_of_dvd_one (hd x 1 (by simpa using h.dvd))⟩, ⟨fun x h => ?_⟩, cA, cB⟩
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O₁
  by_contra hx
  have hπx : π ∣ x := by
    have : x ∈ IsLocalRing.maximalIdeal O₁ := hx
    rwa [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at this
  have hu : IsUnit (gB π) := isUnit_of_dvd_unit (map_dvd gB hπx) h
  obtain ⟨n, u, hn⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ht0 hπ
  apply hnu
  rw [hn, map_mul, map_pow]
  exact (u.isUnit.map gB).mul (hu.pow n)

theorem common : ∀ (Γ O₀ A B : Type) [Group Γ] [CommRing O₀] [IsDomain O₀] [IsDiscreteValuationRing O₀] [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] (fA : O₀ →+* A) (fB : O₀ →+* B), Function.Injective fA → fA.IsIntegral → Function.Injective fB → IsLocalHom fB → ∀ (ψA : Γ →* Aˣ) (ψB : Γ →* Bˣ), SameChar fA fB ψA ψB → ∃ (O₁ : Type) (_ : CommRing O₁) (_ : IsDomain O₁) (_ : IsDiscreteValuationRing O₁) (f : O₀ →+* O₁) (gA : O₁ →+* A) (gB : O₁ →+* B) (ψ : Γ →* O₁ˣ), Function.Injective gA ∧ Function.Injective gB ∧ IsLocalHom gA ∧ IsLocalHom gB ∧ gA.comp f = fA ∧ gB.comp f = fB ∧ (Units.map gA.toMonoidHom).comp ψ = ψA ∧ (Units.map gB.toMonoidHom).comp ψ = ψB := by
  intro Γ O₀ A B _ _ _ _ _ _ _ _ _ _ fA fB _ hAi hB hBl ψA ψB hS
  have iA := IsFractionRing.injective A (FractionRing A)
  have iB := IsFractionRing.injective B (FractionRing B)
  letI : Algebra O₀ A := fA.toAlgebra
  letI : Algebra O₀ B := fB.toAlgebra
  let αA : MonoidAlgebra O₀ Γ →+* A :=
    (MonoidAlgebra.lift O₀ A Γ ((Units.coeHom A).comp ψA)).toRingHom
  let αB : MonoidAlgebra O₀ Γ →+* B :=
    (MonoidAlgebra.lift O₀ B Γ ((Units.coeHom B).comp ψB)).toRingHom
  have hker : ∀ F, αA F = 0 ↔ αB F = 0 := by
    intro F
    simp only [αA, αB, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MonoidAlgebra.lift_apply, Algebra.smul_def]
    exact hS _
  have aA : ∀ c, αA (algebraMap O₀ _ c) = fA c := fun c => AlgHom.commutes _ c
  have aB : ∀ c, αB (algebraMap O₀ _ c) = fB c := fun c => AlgHom.commutes _ c
  have oA : ∀ g, αA (MonoidAlgebra.of O₀ Γ g) = ψA g := fun g => MonoidAlgebra.lift_of _ g
  have oB : ∀ g, αB (MonoidAlgebra.of O₀ Γ g) = ψB g := fun g => MonoidAlgebra.lift_of _ g
  let R : Subring A := αA.range
  let q : MonoidAlgebra O₀ Γ →+* R := αA.rangeRestrict
  have hq : Function.Surjective q := αA.rangeRestrict_surjective
  let φ : R →+* B := q.liftOfSurjective hq ⟨αB, fun F hF =>
    (hker F).1 (congrArg Subtype.val (RingHom.mem_ker.1 hF))⟩
  have hφ : ∀ F, φ (q F) = αB F := fun F => RingHom.liftOfRightInverse_comp_apply _ _ _ _ F
  have φi : Function.Injective φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro r hr
    obtain ⟨F, rfl⟩ := hq r
    exact Subtype.ext ((hker F).2 (by rw [← hφ, hr]))
  let K := FractionRing R
  let jA : K →+* FractionRing A := IsFractionRing.lift (g := (algebraMap A _).comp R.subtype)
    (iA.comp Subtype.val_injective)
  let jB : K →+* FractionRing B := IsFractionRing.lift (g := (algebraMap B _).comp φ)
    (iB.comp φi)
  let p : MonoidAlgebra O₀ Γ →+* K := (algebraMap R K).comp q
  have pA : ∀ F, jA (p F) = algebraMap A _ (αA F) := fun F => IsFractionRing.lift_algebraMap _ _
  have pB : ∀ F, jB (p F) = algebraMap B _ (αB F) := fun F => by
    rw [← hφ]; exact IsFractionRing.lift_algebraMap _ _
  obtain ⟨O₁, hD, f, gA, gB, hmem, hgA, hgB, gAi, gBi, lA, lB, cA, cB⟩ :=
    common_of_field fA fB hAi hB hBl (p.comp (algebraMap O₀ _)) jA jB
      (fun c => by rw [RingHom.comp_apply, pA, aA]) (fun c => by rw [RingHom.comp_apply, pB, aB])
  let p₁ : MonoidAlgebra O₀ Γ →+* O₁ := p.codRestrict O₁ (fun F => (hmem _).2 ⟨_, (pA F).symm⟩)
  let ψ : Γ →* O₁ˣ := (p₁.toMonoidHom.comp (MonoidAlgebra.of O₀ Γ)).toHomUnits
  refine ⟨O₁, inferInstance, inferInstance, hD, f, gA, gB, ψ, gAi, gBi, lA, lB, cA, cB, ?_, ?_⟩
  · ext g
    apply iA
    rw [← oA, ← pA]
    exact hgA _
  · ext g
    apply iB
    rw [← oB, ← pB]
    exact hgB _

end GlobalTheory.Proof.dvr_of_reflects_facts
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.exists_conjugate_family_of_injective : ∀ (g : ℂ ≃+* ℂ) (ι : Type) [Fintype ι] (act act' : ι → SL(2, ℤ) → ι) (m k N : ℕ) (t t' F : ι → ℍ → ℂ), 0 < N → ActBij act → ActBij act' → IsFam act m t → IsFam act' m t' → IsFam act k F → Function.Injective t → (∀ i, QConj g N (t i) (t' i)) → (∀ i, ∃ a, HasQ N (F i) a) → ∃ F' : ι → ℍ → ℂ, IsFam act' k F' ∧ ∀ i, QConj g N (F i) (F' i) := by
  first | exact @GlobalTheory.FN.Lag.conj_family_of_injective | exact GlobalTheory.FN.Lag.conj_family_of_injective | (intros; apply GlobalTheory.FN.Lag.conj_family_of_injective <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem adjugate_mem_intMatricesDetLowerLeftDvd {L q : ℕ} {δ : M2} (h : δ ∈ DT L q) : δ.adjugate ∈ DT L q := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · rw [Matrix.det_adjugate]; simpa using h1
  · rw [Matrix.adjugate_fin_two]; simpa using h2

theorem intMatrixTwo_adjugate_adjugate (δ : M2) : δ.adjugate.adjugate = δ := by
  rw [Matrix.adjugate_fin_two, Matrix.adjugate_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem rrep_DT_adj_repT : ∀ L q : ℕ, q.Prime → ¬ q ∣ L →
    RRep L (DT L q) (fun i => (repT q i).adjugate) := by
  intro L q hq hqL
  have hL := GlobalTheory.T.isLeftGamma0CosetDecomposition_heckeRepTOperator L q hq hqL
  unfold LRep at hL
  unfold RRep
  let φ : Option (Fin q) × Gamma0 L → Gamma0 L × Option (Fin q) := fun p => (p.2⁻¹, p.1)
  have hφ : Set.BijOn φ Set.univ Set.univ := by
    rw [Set.bijOn_univ]
    refine ⟨fun a b h => ?_, fun b => ⟨(b.2, b.1⁻¹), by simp [φ]⟩⟩
    simp only [φ, Prod.mk.injEq, inv_inj] at h
    exact Prod.ext h.2 h.1
  have hA : Set.BijOn (fun δ : M2 => δ.adjugate) (DT L q) (DT L q) :=
    Set.InvOn.bijOn ⟨fun δ _ => intMatrixTwo_adjugate_adjugate δ, fun δ _ => intMatrixTwo_adjugate_adjugate δ⟩
      (fun δ h => adjugate_mem_intMatricesDetLowerLeftDvd h) (fun δ h => adjugate_mem_intMatricesDetLowerLeftDvd h)
  have hc := hA.comp (hL.comp hφ)
  convert hc using 1
  funext p
  dsimp only [Function.comp_apply, φ]
  rw [Matrix.adjugate_mul_distrib]
  congr 1
  rw [Subgroup.coe_inv, ← Matrix.SpecialLinearGroup.coe_inv, inv_inv]

end GlobalTheory.EisM
end
