module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle020
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle021
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle366
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle109
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle016
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle341
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle011
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle357
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle362
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle360
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle009
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HermitianCodeWordWeilElementMemQuadraticField
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle182
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.Bundle004
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.UnitsMapSurjOfZmod
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle365
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UntwistedRepresentationOrdinaryTriangularShape
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsZetaDerivationInertiaCyclotomicAlgebra
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardPrimePowTorsionSelmerClassesModPrimePowBound
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle355
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle368
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
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
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle018
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Matrix

namespace GlobalTheory.Ord2

theorem bk_unr_gr : Loc.LocalPublishedTheorems → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ z ∈ Z1 (Loc.colRep W), IsBK l (Loc.colRep W) z → Unr W z ∧ Gr W A z := by
  intro hP l _ Ω _ _ _ e S A W hN z hz hbk
  have hcol : ∀ s x, Loc.colRep W s x = mat W s *ᵥ x := fun s x => by
    simp [Loc.colRep, Matrix.toLin'_apply]
  refine ⟨fun w hw => ?_, ?_⟩
  · obtain ⟨B, hB, x, hx⟩ := hbk.away w hw
    exact ⟨B, hB, x, fun s hs => by rw [hx s hs, hcol]⟩
  obtain ⟨ι, hιc, hιD, hιS, hιI, hιcyc, hιZ⟩ := GlobalTheory.T.crystallineClass_restrict_decompositionGroup l Ω W A hN.atL z hz hbk
  have hup : ∀ σ, mat W (ι σ) 1 0 = 0 := fun σ => hN.upper _ (hιD σ)
  let k0 : GQ l →* Qbar l :=
    { toFun := fun σ => mat W (ι σ) 1 1
      map_one' := by simp [mat]
      map_mul' := fun σ τ => by
        have h := hup σ
        simp only [mat] at h
        simp only [mat, map_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, h, zero_mul, zero_add] }
  let κ : GQ l →* (Qbar l)ˣ := k0.toHomUnits
  have hκ : ∀ σ, (κ σ : Qbar l) = mat W (ι σ) 1 1 := fun σ => rfl
  have hκc : Continuous fun σ => (κ σ : Qbar l) :=
    ((Units.continuous_val.comp (hN.cont.comp hιc)).matrix_elem 1 1)
  let f : (Fin 2 → Qbar l) →ₗ[ℚ_[l]] Qbar l := LinearMap.proj (R := ℚ_[l]) (φ := fun _ : Fin 2 => Qbar l) 1
  have hf : ∀ σ x, f (((Loc.colRep W).comp ι) σ x) = Loc.chRep κ σ (f x) := fun σ x => by
    have h := hup σ
    simp only [mat] at h
    simp [f, Loc.chRep, hcol, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hκ, mat, h]
  have hc := Loc.z1fCoef (MonoidHom.id (GQ l)) _ _ f (continuous_apply 1) hf _ hιZ
  obtain ⟨c, hcO⟩ := hN.int
  obtain ⟨m, hm1, hm⟩ := hN.wt
  have hw : Loc.HasWeight (MonoidHom.id (GQ l)) κ (-(e : ℤ)) := by
    refine GlobalTheory.T.hasWeight_neg_of_cyclotomic_pow_on_inertia l κ hκc e (2 * m) (by omega) fun σ hσ => ?_
    have hs := hιI σ hσ
    have h0 := hm _ hs
    have hd : (dt W (ι σ) : Qbar l) ^ 2 = 1 := by
      have := congrArg (fun u : G ℚ Ω →* (Qbar l)ˣ => ((u (ι σ) : (Qbar l)ˣ) : Qbar l)) hN.det2
      simpa using this
    have hdet : (dt W (ι σ) : Qbar l) = mat W (ι σ) 0 0 * mat W (ι σ) 1 1 := by
      have h := hup σ
      simp only [mat] at h
      simp [dt, Matrix.det_fin_two, mat, h]
    have hcy : (Loc.cycA l l (Qbar l) σ : Qbar l) = eps l (ι σ) := by
      simp only [Loc.cycA, eps, cycBar, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, hιcyc, RingHom.coe_comp, Function.comp_apply]
      rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l)]
      rfl
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, Units.val_mul, Units.val_zpow_eq_zpow_val, zpow_natCast, Units.val_one, hκ, hcy]
    rw [hdet] at hd
    calc (mat W (ι σ) 1 1 * eps l (ι σ) ^ e) ^ (2 * m) = (mat W (ι σ) 1 1) ^ (2 * m) * (eps l (ι σ) ^ (e * m)) ^ 2 := by ring
      _ = ((mat W (ι σ) 0 0 * mat W (ι σ) 1 1) ^ 2) ^ m := by rw [← h0]; ring
      _ = 1 := by rw [hd, one_pow]
  obtain ⟨x, hx⟩ := GlobalTheory.T.crystallineCocycle_coboundary_of_negative_weight hP l κ hκc c (fun σ => hcO _ 1 1) (-(e : ℤ)) (by have := hN.e_pos; omega) hw _ hc
  refine ⟨x, fun s hs => ?_⟩
  obtain ⟨σ, rfl⟩ := hιS s hs
  have := hx σ
  simpa [f, hκ] using this

end GlobalTheory.Ord2
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.PrimeChar

theorem normV_prime (v : Pl) : (normV v).Prime := by
  haveI := v.isPrime
  haveI := v.isMaximal
  haveI : Finite (𝓞 ℚ ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  have hp : (ringChar (𝓞 ℚ ⧸ v.asIdeal)).Prime := CharP.char_is_prime (𝓞 ℚ ⧸ v.asIdeal) _
  haveI : Fact (ringChar (𝓞 ℚ ⧸ v.asIdeal)).Prime := ⟨hp⟩
  have hs : Function.Surjective (ZMod.castHom (dvd_refl (ringChar (𝓞 ℚ ⧸ v.asIdeal))) (𝓞 ℚ ⧸ v.asIdeal)) := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨n, rfl⟩ := Rat.ringOfIntegersEquiv.symm.surjective x
    exact ⟨(n : ZMod _), by simp⟩
  have hb := Nat.card_eq_of_bijective _ ⟨RingHom.injective _, hs⟩
  rw [normV, ← hb, Nat.card_zmod]
  exact hp

theorem normV_mem (v : Pl) : ((normV v : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
  have h : Nat.card (𝓞 ℚ ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  change ((Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℕ) : 𝓞 ℚ) ∈ v.asIdeal
  rw [h]
  exact Ideal.absNorm_mem _

theorem val_normV_lt_one {Ω : Type} [Field Ω] [Algebra ℚ Ω] {B : ValuationSubring Ω} {v : Pl}
    (h : IsPlaceOver B v) : B.valuation ((normV v : ℕ) : Ω) < 1 := by
  have := (h _).2 (normV_mem v)
  simpa using this

theorem eq_of_normV_eq {v w : Pl} (h : normV v = normV w) : v = w := by
  have hp := normV_prime w
  have hpr : Prime ((normV w : ℕ) : 𝓞 ℚ) := by
    have h1 : Prime ((normV w : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hp
    have e : ((normV w : ℕ) : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm ((normV w : ℕ) : ℤ) := by simp
    rw [e]
    exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr h1
  have hI : (Ideal.span {((normV w : ℕ) : 𝓞 ℚ)}).IsMaximal :=
    Ideal.IsPrime.isMaximal ((Ideal.span_singleton_prime hpr.ne_zero).mpr hpr)
      (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hpr.ne_zero)
  have hv : Ideal.span {((normV w : ℕ) : 𝓞 ℚ)} = v.asIdeal :=
    hI.eq_of_le v.isPrime.ne_top (by rw [Ideal.span_singleton_le_iff_mem, ← h]; exact normV_mem v)
  have hw : Ideal.span {((normV w : ℕ) : 𝓞 ℚ)} = w.asIdeal :=
    hI.eq_of_le w.isPrime.ne_top (by rw [Ideal.span_singleton_le_iff_mem]; exact normV_mem w)
  exact HeightOneSpectrum.ext (hv.symm.trans hw)

theorem exists_surj (p N : ℕ) [Fact p.Prime] (h : N ∣ p - 1) :
    ∃ f : (ZMod p)ˣ →* Multiplicative (ZMod N), Function.Surjective f := by
  have hc : IsCyclic (ZMod p)ˣ := inferInstance
  have hcard : N ∣ Nat.card (ZMod p)ˣ := by rw [Nat.card_eq_fintype_card, ZMod.card_units]; exact h
  let c : ZMod (Nat.card (ZMod p)ˣ) →+ ZMod N := (ZMod.castHom hcard (ZMod N)).toAddMonoidHom
  refine ⟨(AddMonoidHom.toMultiplicative c).comp (zmodCyclicMulEquiv hc).symm.toMonoidHom, ?_⟩
  intro y
  obtain ⟨x, hx⟩ := ZMod.castHom_surjective hcard (Multiplicative.toAdd y)
  refine ⟨zmodCyclicMulEquiv hc (Multiplicative.ofAdd x), ?_⟩
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
  show Multiplicative.ofAdd (c x) = y
  exact hx

theorem pow_self_eq_one (N : ℕ) (a : Multiplicative (ZMod N)) : a ^ N = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one, nsmul_eq_mul, ZMod.natCast_self, zero_mul]

end GlobalTheory.Ord2.PrimeChar

namespace GlobalTheory.Ord2.PrimeChar

theorem exists_prime_char : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ) (w : Pl),
    1 ≤ n → l ^ n ∣ normV w - 1 → ∃ ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n)), KillsMu (normV w) ψ ∧
      Function.Surjective ψ ∧ (∀ B : ValuationSubring Ω, IsPlaceOver B w → ∃ τ ∈ Ine (F := ℚ) B, (ψ τ).toAdd = 1) ∧
      ∀ v : Pl, v ≠ w → (∃ x : ZMod (normV w), x ^ (l ^ n) = (normV v : ZMod (normV w))) →
        ∀ B : ValuationSubring Ω, IsPlaceOver B v → Dec (F := ℚ) B ≤ ψ.ker := by
  intro l _ Ω _ _ _ n w _ hdiv
  have hp := normV_prime w
  haveI : Fact (normV w).Prime := ⟨hp⟩
  haveI : NeZero (normV w) := ⟨hp.ne_zero⟩
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨f, hf⟩ := exists_surj (normV w) (l ^ n) hdiv

  have hine : ∀ B : ValuationSubring Ω, IsPlaceOver B w →
      ∃ τ ∈ Ine (F := ℚ) B, (f.comp (Chr.cls ℚ Ω (normV w)) τ).toAdd = 1 := by
    intro B hB
    have hBp := val_normV_lt_one hB
    obtain ⟨g0, hg0⟩ := hf (Multiplicative.ofAdd 1)
    have hd : normV w ^ 1 ∣ normV w := by rw [pow_one]
    obtain ⟨w0, hw0⟩ := KStar.TotallyRealRoots.redPow_surjective (l := normV w) 1 (ZMod.unitsMap hd g0)
    obtain ⟨σ, hσ, hσw⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω (normV w) B hBp w0
    refine ⟨σ, hσ, ?_⟩
    haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
    haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
    haveI : NeZero ((normV w : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hp.ne_zero⟩
    have hX : PadicInt.toZModPow 1 (w0 : ℤ_[normV w]) = (((g0 : ZMod (normV w)).val : ℕ) : ZMod (normV w ^ 1)) := by
      have h2 := congrArg (fun u : (ZMod (normV w ^ 1))ˣ => (u : ZMod (normV w ^ 1))) hw0
      simp only [ZMod.unitsMap_val] at h2
      rw [← ZMod.cast_natCast (R := ZMod (normV w ^ 1)) hd ((g0 : ZMod (normV w)).val), ZMod.natCast_zmod_val]
      exact h2
    have hcls : Chr.cls ℚ Ω (normV w) σ = g0 := by
      refine (Chr.clsFacts ℚ Ω (normV w)).2.2.1 σ g0 fun ζ hζ => ?_
      have hζ' : ζ ^ (normV w ^ 1) = 1 := by rw [pow_one]; exact hζ
      have hspec : σ ζ = ζ ^ (PadicInt.toZModPow 1 ((cycZ ℚ Ω (normV w) σ : ℤ_[normV w]ˣ) : ℤ_[normV w])).val :=
        cyclotomicCharacter.spec (L := Ω) (normV w) (MulSemiringAction.toRingAut (G ℚ Ω) Ω σ) ζ hζ'
      rw [hspec, hσw, hX, ZMod.val_natCast, ← pow_eq_pow_mod _ hζ']
    rw [MonoidHom.comp_apply, hcls, hg0, toAdd_ofAdd]
  refine ⟨f.comp (Chr.cls ℚ Ω (normV w)), fun s hs => ?_, fun y => ?_, hine, fun v hvw hx B hB => ?_⟩
  ·
    have h1 : Chr.cls ℚ Ω (normV w) s = 1 := (Chr.clsFacts ℚ Ω (normV w)).2.2.1 s 1 fun ζ hζ => by
      rw [Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 hζ, pow_one]
      exact hs ζ hζ
    rw [MonoidHom.comp_apply, h1, map_one]
  ·
    obtain ⟨B, hB⟩ := exists_isPlaceOver Ω w
    obtain ⟨τ, -, hτ⟩ := hine B hB
    refine ⟨τ ^ (Multiplicative.toAdd y).val, ?_⟩
    apply Multiplicative.toAdd.injective
    rw [map_pow, toAdd_pow, hτ, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
  ·
    have hq := normV_prime v
    haveI : Fact (normV v).Prime := ⟨hq⟩
    have hne : normV v ≠ normV w := fun h => hvw (eq_of_normV_eq h)
    have hcop : (normV w).Coprime (normV v) := (Nat.coprime_primes hp hq).2 (Ne.symm hne)
    have hBq := val_normV_lt_one hB
    obtain ⟨x, hx⟩ := hx
    have hq0 : ((normV v : ℕ) : ZMod (normV w)) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff (ZMod (normV w)) (normV w)]
      exact fun h => hne ((Nat.prime_dvd_prime_iff_eq hp hq).1 h).symm
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)] at hx
      exact hq0 hx.symm
    let uq : (ZMod (normV w))ˣ := ZMod.unitOfCoprime (normV v) hcop.symm
    have huq : uq = Units.mk0 x hx0 ^ (l ^ n) := by
      ext
      simp [uq, hx]
    have hfq : f uq = 1 := by rw [huq, map_pow, pow_self_eq_one]
    intro g hg
    obtain ⟨k, hk⟩ := UpperTheory.V.LDataCardLeFinrank.decActRoots ℚ Ω (normV v) B hBq (normV w) hcop g hg
    have hcls : Chr.cls ℚ Ω (normV w) g = uq ^ k := by
      refine (Chr.clsFacts ℚ Ω (normV w)).2.2.1 g (uq ^ k) fun ζ hζ => ?_
      rw [hk ζ hζ, Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ZMod.val_natCast,
        ← pow_eq_pow_mod _ hζ]
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hcls, map_pow, hfq, one_pow]

end GlobalTheory.Ord2.PrimeChar
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem galoisRepRankTwoTateDual_exists_no_eigenvalue_one_alt : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∃ g, (mat (dual1 W) g - 1).det ≠ 0 := by
  intro l _ Ω _ _ _ e S A W h
  obtain ⟨φ, hφ, hd⟩ := GlobalTheory.T.exists_commutator_det_nonzero l Ω e S A W h
  have hφ' : φ ∈ H0g W := (Subgroup.commutator_le.2 (fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb))) hφ
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hφ'
  rw [MonoidHom.mem_ker] at h1 h2
  have hχ : (cycBar ℚ Ω l * (dt W)⁻¹) φ = 1 := by
    simp [h1, h2]
  refine ⟨φ, ?_⟩
  have : mat (dual1 W) φ = mat W φ := by
    unfold dual1
    generalize (cycBar ℚ Ω l * (dt W)⁻¹) = χ at hχ
    simp [mat, _root_.UpperTheory.V.Af.tw, hχ]
  rw [this]; exact hd

end GlobalTheory.Ord2
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.CyclotomicQExpansion
open scoped Matrix MatrixGroups

theorem _root_.GlobalTheory.T.untwisted_representation_ordinary_triangular_shape : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (S : Finset Pl)
    (A : ValuationSubring Ω) (W : R2 Ω l) (g : Newform (2 * e + 1)) (ψ : ZMod l → Qbar l),
  Nf e S A W → SrcUr ι e A W g →
  (∃ χ : G ℚ Ω →* (Qbar l)ˣ, KillsMu l χ ∧
    (∀ s ∈ Ine (F := ℚ) A, mat W s 1 1 * (cycBar ℚ Ω l s : Qbar l) ^ (e : ℤ) * ((dt W s : Qbar l)⁻¹ * (χ s : Qbar l)) = 1) ∧
    ∀ s : G ℚ Ω, (χ s : Qbar l) = ψ ((((cycMod (F := ℚ) (Ω := Ω) l 1 s : ZMod (l ^ 1))).val : ℕ) : ZMod l)) →
  ∃ ρ : (Ω ≃ₐ[ℚ] Ω) →* GL (Fin 2) (Qbar l),
    (∀ s, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) = rhoK W e ψ s) ∧ Continuous ρ ∧
    (∀ s ∈ Dec (F := ℚ) A, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 0 = 0) ∧
    (∀ s ∈ Ine (F := ℚ) A, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 1 = 1) ∧
    ∃ F : Finset Ω, ∀ s ∈ Ine (F := ℚ) A, (∀ y ∈ F, s y = y) →
      (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 0 0 = ((cycZ ℚ Ω l s : ℤ_[l]) : Qbar l) ^ (2 * e) := by
  first | (exact @GlobalTheory.RhoAdm.rho_ordinary_shape) | (exact GlobalTheory.RhoAdm.rho_ordinary_shape) | (intros; apply GlobalTheory.RhoAdm.rho_ordinary_shape  <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA
open scoped Matrix MatrixGroups

namespace GlobalTheory.K4

theorem zetaSystem_exponent_raise_of_prime_pow_smul : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε)
  (pr : X.Fn l → Fin 2 → Qbar l) (W : R2 Ω l) (e : ℕ) (ψ : ZMod l → Qbar l) (N : ℕ) [NeZero N] (x : ZMod N)
  (c d k : ℕ) (g : (ZMod l)ˣ → SL(2, ℤ)) (cf : Coef l) (c₀ m : ℕ)
  (Y : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l),
  (∀ b b', pr (b + b') = pr b + pr b') →
  (∀ (a : ℤ_[l]) b, pr (a • b) = algebraMap ℚ_[l] (Qbar l) (a : ℚ_[l]) • pr b) →
  IsZetaSystemFixedExponent X l pr W e ψ N x c d k g cf c₀ Y →
  IsZetaSystemFixedExponent X l pr W e ψ N x c d k g cf (c₀ + m) (fun r s y => ((l : Qbar l) ^ m) • Y r s y) := by
  intro l _ Ω _ _ ε X pr W e ψ N _ x c d k g cf c₀ m Y hadd hsmul hZ r n
  obtain ⟨bB, hB, b, hb, hY⟩ := hZ r n
  have hl : ‖((l : ℕ) : Qbar l)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ l
  have hlm : ‖((l : ℕ) : Qbar l) ^ m‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hl
  have hpr : ∀ v : X.Fn l, pr (((l : ℤ_[l]) ^ m) • v) = ((l : ℕ) : Qbar l) ^ m • pr v := by
    intro v
    rw [hsmul]
    congr 1
    simp
  refine ⟨fun σ => ((l : ℤ_[l]) ^ m) • bB σ, ?_, fun y => ((l : ℕ) : Qbar l) ^ m • b y, ?_, ?_⟩
  · intro σ hσ
    obtain ⟨h1, h2⟩ := hB σ hσ
    refine ⟨Submodule.smul_mem _ _ h1, fun u => ?_⟩
    have : (((l : ℤ_[l]) ^ m) • bB σ) u - ((l : ℤ_[l]) ^ (c₀ + m)) • clsBmu X l n r N x c d k g σ u
        = ((l : ℤ_[l]) ^ m) • (bB σ u - ((l : ℤ_[l]) ^ c₀) • clsBmu X l n r N x c d k g σ u) := by
      rw [smul_sub, smul_smul, ← pow_add, add_comm m c₀]
      rfl
    rw [this, LinearMap.map_smul, h2 u, smul_zero]
  · intro y i
    simp only [Pi.smul_apply, smul_eq_mul]
    exact cf.O.mul_mem (cf.O.pow_mem (cf.O.natCast_mem l) m) (hb y i)
  · intro s y
    have hYf : YfB X l pr W e ψ n r N (fun σ => ((l : ℤ_[l]) ^ m) • bB σ) s y
        = ((l : ℕ) : Qbar l) ^ m • YfB X l pr W e ψ n r N bB s y := by
      unfold YfB GlobalTheory.KA.push
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      simp only [hpr, Matrix.mulVec_smul]
    rw [hYf]
    intro i
    have h := hY s y i
    unfold Cg at h ⊢
    have hrw : ((l : ℕ) : Qbar l) ^ m • Y r s y i -
        (((l : ℕ) : Qbar l) ^ m • YfB X l pr W e ψ n r N bB s y +
          (rhoK W e ψ s *ᵥ (((l : ℕ) : Qbar l) ^ m • b (y * (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹)) -
            ((l : ℕ) : Qbar l) ^ m • b y)) i
        = ((l : ℕ) : Qbar l) ^ m * (Y r s y i - (YfB X l pr W e ψ n r N bB s y +
          (rhoK W e ψ s *ᵥ b (y * (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹) - b y)) i) := by
      simp only [Matrix.mulVec_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    show ‖_‖ ≤ _
    simp only [Pi.smul_apply, smul_eq_mul] at hrw ⊢
    rw [hrw, norm_mul]
    calc _ ≤ 1 * ‖Y r s y i - (YfB X l pr W e ψ n r N bB s y +
          (rhoK W e ψ s *ᵥ b (y * (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹) - b y)) i‖ :=
          mul_le_mul_of_nonneg_right hlm (norm_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact h

end GlobalTheory.K4
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4
open scoped Matrix MatrixGroups

namespace GlobalTheory.LambdaValuationPowers.AllRoots

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem pres_of_vanish (A : ValuationSubring Ω) (c : Coef l) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) (m : ℕ) (ζ : Ω)
    (hζ : IsPrimitiveRoot ζ (l ^ m)) (hZ : ∀ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l m s = 1 → Z m s 1 = 0) :
    ∃ (ι : Type) (_ : Fintype ι) (P : ι → Polynomial Ω) (o : ι → Qbar l), HTPresNuOfPolys A c m 0 Z ζ P o := by
  refine ⟨Empty, inferInstance, fun i => i.elim, fun i => i.elim, hζ, fun i => i.elim, fun i => i.elim, fun i => i.elim, ?_⟩
  have h := GlobalTheory.Col.kumPres_empty A (n := m - 0) (r := m) (ζ := ζ ^ l ^ 0) (by simpa using hζ) (by omega) (Z m) hZ
  convert h using 2 <;> exact Empty.elim ‹_›

theorem continuous_of_cg [Algebra.IsAlgebraic ℚ Ω] (f : G ℚ Ω → Qbar l)
    (h : ∀ n : ℕ, ∃ E0 : Finset Ω, ∀ s s' : G ℚ Ω, (∀ z ∈ E0, s' z = z) → Cg n (f (s * s')) (f s)) : Continuous f := by
  have hnl : ‖(l : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
    have : (l : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
    rw [this, norm_algebraMap', Padic.norm_p]
  have hlt1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  rw [continuous_iff_continuousAt]
  intro s
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hlt1
  obtain ⟨E0, hE⟩ := h n
  have hopen : ∀ᶠ t in nhds (1 : G ℚ Ω), ∀ z ∈ E0, t z = z := by
    rw [Filter.eventually_all_finset]
    intro z _
    have ho := stabilizer_isOpen_of_isIntegral (K := ℚ) (L := Ω) z
    exact ho.mem_nhds (one_mem _)
  have hcont : Filter.Tendsto (fun t : G ℚ Ω => s⁻¹ * t) (nhds s) (nhds 1) := by
    have := (continuous_const_mul s⁻¹).tendsto s
    rwa [inv_mul_cancel] at this
  filter_upwards [hcont.eventually hopen] with t ht
  have := hE s (s⁻¹ * t) ht
  rw [mul_inv_cancel_left, Cg, norm_pow, hnl] at this
  rw [dist_eq_norm]
  exact this.trans_lt hn

end GlobalTheory.LambdaValuationPowers.AllRoots
end
end

section

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

theorem _root_.GlobalTheory.T.maxSlope_dual_sum_weyl_lattices_le : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (v₀ : InfinitePlace K), IsConjAt v₀ → ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (R : ℝ), 1 ≤ R → SpreadLe lam R → ∀ (G : ι → Matrix (Fin n) (Fin n) K), (∀ τ, IsDefGram (G τ)) → ∀ (C : Type) [Nonempty C] (M : C → ι → Submodule (𝓞 K) (Fin n → K)), (∀ c τ, IsSelfDualK (G τ) (M c τ)) → ∀ (N : ℕ) (e : Fin N ≃ C × VVIdx lam) (X : InfinitePlace K → Matrix (Fin N) (Fin N) ℂ), IsMetric ((sumGram lam e G)⁻¹)ᵀ X → TestLatticeCondition N X (dualFr (sumLat lam e fun c => delK lam (M c))) (bound (Fintype.card ι) n R) := by
  first | exact @GlobalTheory.TestLat.testLatticeCondition_dualFr_sumLat_delK | exact GlobalTheory.TestLat.testLatticeCondition_dualFr_sumLat_delK | (intros; apply GlobalTheory.TestLat.testLatticeCondition_dualFr_sumLat_delK <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal

theorem _root_.GlobalTheory.T.exists_zeta_derivation_inertia_cyclotomic_algebra : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (N : ℕ) (z : A), IsPrimitiveRoot (z : Ω) (l ^ N) → ∃ D : A → FracA A, IsDerOn (cycAlg l A) D ∧ D z = Submodule.Quotient.mk ((z : Ω) * (l : Ω) / (l : Ω) ^ N) := by
  first | (exact @GlobalTheory.RecOne.zeta_derivation_cyc) | (exact GlobalTheory.RecOne.zeta_derivation_cyc) | (intros; apply GlobalTheory.RecOne.zeta_derivation_cyc  <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem _root_.GlobalTheory.T.card_primePowTorsion_selmerClassesModPrimePow_bounded : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ c : Coef l, (∀ s i j, mat W s i j ∈ c.O) → (∀ n : ℕ, ∃ B : ℕ, ∀ (N : ℕ) (z : Fin N → G ℚ Ω → Fin 2 → Qbar l), (∀ i, Coc1 c n (dual1 W) ⊤ (z i) ∧ ∀ a ∈ (toGS Ω (S : Set Pl)).ker, Cv n (z i a) 0) → (∀ i j, i ≠ j → ¬ Cob1 c n (dual1 W) ⊤ (z i - z j)) → N ≤ B) → ∀ m : ℕ, ∃ B : ℕ, ∀ (n N : ℕ) (z : Fin N → G ℚ Ω → Fin 2 → Qbar l), (∀ i, GwCount.SelN c n S A (dual1 W) (z i)) → (∀ i j, i ≠ j → ¬ Cob1 c n (dual1 W) ⊤ (z i - z j)) → (∀ i, Cob1 c n (dual1 W) ⊤ (fun s => ((l : ℕ) : Qbar l) ^ m • z i s)) → N ≤ B := by
  first | exact @GlobalTheory.Ord2.TorsBound.tors_bound | exact GlobalTheory.Ord2.TorsBound.tors_bound | (intros; apply GlobalTheory.Ord2.TorsBound.tors_bound <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA GlobalTheory.InertCoh
open scoped Matrix

theorem _root_.GlobalTheory.T.fg_inertiaCocycles_mod_coboundaries_coefRing : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : R2 Ω l) (c : Coef l) (I : Subgroup (G ℚ Ω)) (P : Set (G ℚ Ω)) (γ : G ℚ Ω), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → (∀ z ∈ coc W c I, ∃ v : Fin 2 → Qbar l, (∀ i, v i ∈ c.O) ∧ ∀ σ ∈ P, z σ = mat W σ *ᵥ v - v) → (∀ z ∈ coc W c I, (∀ σ ∈ P, z σ = 0) → z γ = 0 → ∀ s ∈ I, z s = 0) → ((coc W c I).map (cob W c I).mkQ).FG := by
  first | exact @GlobalTheory.InertCoh.fg_coc_mod_cob | exact GlobalTheory.InertCoh.fg_coc_mod_cob | (intros; apply GlobalTheory.InertCoh.fg_coc_mod_cob <;> assumption)
end
