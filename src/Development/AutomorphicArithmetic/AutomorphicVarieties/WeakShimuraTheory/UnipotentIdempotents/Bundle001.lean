module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCyclotomicBlockCocyclesLeSha
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
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
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle001
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.TCont
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

local instance (priority := 2000) ratFieldIsTorsionFreeForUnipotentIdempotents (Ω : Type) [Field Ω] [Algebra ℚ Ω] :
    Module.IsTorsionFree ℚ Ω := DivisionSemiring.to_moduleIsTorsionFree

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

theorem UpperTheory.V.Ws.Lk.noMu :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c}, D.Good → ∀ (L : IntermediateField ℚ Ω) (g : G L Ω), Raw.bar D.om (resQ L g) ≠ 1 → ¬ ∃ ζ : L, IsPrimitiveRoot ζ l := by
  intro Ω _ _ _ l _ c D hD L g hbar hroot
  obtain ⟨ζ, hζ⟩ := hroot
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  haveI := c.fin
  haveI : IsLocalHom (algebraMap ℤ_[l] c.O) := (UpperTheory.V.Base.dvrFacts l c.O).2.2.1
  have hl : 1 < l := (Fact.out : l.Prime).one_lt
  have hζΩ : IsPrimitiveRoot (ζ : Ω) l := hζ.map_of_injective (L.val : L →+* Ω).injective
  set σ : G ℚ Ω := resQ L g with hσ
  set χ : ℤ_[l] := ((cycZ ℚ Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) with hχ
  have hfix : (MulSemiringAction.toRingAut (G ℚ Ω) Ω σ) (ζ : Ω) = (ζ : Ω) := g.commutes ζ
  have hspec := cyclotomicCharacter.spec (L := Ω) l (n := 1)
    (MulSemiringAction.toRingAut (G ℚ Ω) Ω σ) (ζ : Ω) (by rw [pow_one]; exact hζΩ.pow_eq_one)
  rw [hfix] at hspec
  have hmod : PadicInt.toZModPow 1 χ = 1 := by
    haveI : Fact (1 < l ^ 1) := ⟨by rw [pow_one]; exact hl⟩
    apply ZMod.val_injective
    rw [ZMod.val_one]
    have hlt : (PadicInt.toZModPow 1 χ).val < l :=
      lt_of_lt_of_eq (ZMod.val_lt (PadicInt.toZModPow 1 χ)) (pow_one l)
    apply hζΩ.pow_inj hlt hl
    exact hspec.symm.trans (pow_one _).symm
  have hmem : χ - 1 ∈ IsLocalRing.maximalIdeal ℤ_[l] := by
    rw [PadicInt.maximalIdeal_eq_span_p, ← pow_one (l : ℤ_[l]), ← PadicInt.ker_toZModPow,
      RingHom.mem_ker, map_sub, hmod, map_one, sub_self]
  have hnu : algebraMap ℤ_[l] c.O (χ - 1) ∈ IsLocalRing.maximalIdeal c.O := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact (IsLocalRing.mem_maximalIdeal _).1 hmem (IsUnit.of_map (algebraMap ℤ_[l] c.O) _ hu)
  apply hbar
  rw [hD.om_bar]
  change IsLocalRing.residue c.O (algebraMap ℤ_[l] c.O χ) = 1
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_sub, map_one] at hnu
  exact sub_eq_zero.mp hnu
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk
open scoped Pointwise

namespace UpperTheory.V.Ws.Lk.BetaCyclotomicPlace

variable (l : ℕ) [hl : Fact l.Prime]

private theorem prime_l : Prime ((l : ℕ) : 𝓞 ℚ) := by
  have h : Prime ((l : ℤ)) := Nat.prime_iff_prime_int.1 hl.out
  have h2 := (MulEquiv.prime_iff (Rat.ringOfIntegersEquiv.symm : ℤ ≃* 𝓞 ℚ)).2 h
  simpa using h2

private noncomputable def vQ : HeightOneSpectrum (𝓞 ℚ) where
  asIdeal := Ideal.span {((l : ℕ) : 𝓞 ℚ)}
  isPrime := (Ideal.span_singleton_prime (prime_l l).ne_zero).mpr (prime_l l)
  ne_bot := by rw [Ne, Ideal.span_singleton_eq_bot]; exact (prime_l l).ne_zero

variable {l} {Ω : Type} [Field Ω]

private theorem isPlaceOver_vQ [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω)
    (hA : A.valuation ((l : ℕ) : Ω) < 1) : IsPlaceOver (F := ℚ) A (vQ l) := by
  intro x
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, x = (n : 𝓞 ℚ) :=
    ⟨Rat.ringOfIntegersEquiv x, by rw [← map_intCast Rat.ringOfIntegersEquiv.symm, Int.cast_id, RingEquiv.symm_apply_apply]⟩
  have hcast : algebraMap ℚ Ω (((n : 𝓞 ℚ)) : ℚ) = (n : Ω) := by simp
  rw [hcast]
  show _ ↔ (n : 𝓞 ℚ) ∈ Ideal.span {((l : ℕ) : 𝓞 ℚ)}
  rw [Ideal.mem_span_singleton]
  have hle : ∀ m : ℤ, A.valuation (m : Ω) ≤ 1 := fun m => (A.valuation_le_one_iff _).2 (intCast_mem A m)
  have hdvd : ((l : ℕ) : 𝓞 ℚ) ∣ (n : 𝓞 ℚ) ↔ (l : ℤ) ∣ n := by
    rw [show ((l : ℕ) : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm (l : ℤ) by simp,
      show (n : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm n by simp, map_dvd_iff]
  rw [hdvd]
  constructor
  · intro hv
    by_contra hnd
    have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.1 hl.out
    haveI : IsPrincipalIdealRing ℤ := EuclideanDomain.instIsPrincipalIdealRing
    haveI : IsBezout ℤ := IsBezout.of_isPrincipalIdealRing ℤ
    obtain ⟨a, b, hab⟩ := (Irreducible.coprime_iff_not_dvd hp.irreducible).2 hnd
    have h1 : A.valuation ((a * l + b * n : ℤ) : Ω) < 1 := by
      push_cast
      apply lt_of_le_of_lt (A.valuation.map_add _ _)
      apply max_lt
      · rw [map_mul]
        calc A.valuation (a : Ω) * A.valuation ((l : ℕ) : Ω) ≤ 1 * A.valuation ((l : ℕ) : Ω) :=
              mul_le_mul' (hle a) le_rfl
          _ < 1 := by rw [one_mul]; exact hA
      · rw [map_mul]
        calc A.valuation (b : Ω) * A.valuation (n : Ω) ≤ 1 * A.valuation (n : Ω) := mul_le_mul' (hle b) le_rfl
          _ < 1 := by rw [one_mul]; exact hv
    rw [hab, Int.cast_one, map_one] at h1
    exact (lt_irrefl _ h1).elim
  · rintro ⟨y, rfl⟩
    push_cast
    rw [map_mul]
    calc A.valuation ((l : ℕ) : Ω) * A.valuation (y : Ω) ≤ A.valuation ((l : ℕ) : Ω) * 1 :=
          mul_le_mul' le_rfl (hle y)
      _ < 1 := by rw [mul_one]; exact hA

end UpperTheory.V.Ws.Lk.BetaCyclotomicPlace

open UpperTheory.V.Ws.Lk.BetaCyclotomicPlace in
theorem UpperTheory.V.Ws.Lk.betaCyc :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ Ω) [NumberField K], Module.finrank ℚ K = 2 → ∀ A₀ : ValuationSubring Ω, A₀.valuation (l : Ω) < 1 → ∀ β : G K Ω →* (PadicAlgCl l)ˣ, (∀ σ ∉ K.fixingSubgroup, ∀ s s' : G K Ω, resQ K s' = σ * resQ K s * σ⁻¹ → β s * β s' = 1) → ∀ U : Subgroup (G K Ω), IsOpen (U : Set (G K Ω)) → (∀ B : ValuationSubring Ω, (∀ x ∈ K, x ∈ B ↔ x ∈ A₀) → ∀ s ∈ U ⊓ Ine (F := K) B, (β s : PadicAlgCl l) ^ 2 = algebraMap ℤ_[l] (PadicAlgCl l) (cycZ K Ω l s : ℤ_[l])) → ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∃ (b : ℤ) (k : ℕ), 0 < k ∧ Odd b ∧ ∀ s ∈ Ine (F := K) A, (β s ^ 2 * cycBar K Ω l s ^ (-b)) ^ k = 1 := by
  intro Ω _ _ _ l _ K _ hK A₀ hA₀ β hconj U hU hcyc A hA
  have hn : U.index ≠ 0 := by
    haveI : Finite (G K Ω ⧸ U) := U.quotient_finite_of_isOpen hU
    exact Subgroup.index_ne_zero_of_finite
  have hpow : ∀ s : G K Ω, s ^ U.index.factorial ∈ U := fun s =>
    Subgroup.pow_mem_of_index_ne_zero_of_dvd hn s (fun m h1 h2 => Nat.dvd_factorial h1 h2)
  have hkpos : 0 < U.index.factorial := Nat.factorial_pos _
  have hval : ∀ t : G K Ω, ((cycBar K Ω l t : (Qbar l)ˣ) : PadicAlgCl l) =
      algebraMap ℤ_[l] (PadicAlgCl l) (cycZ K Ω l t : ℤ_[l]) := fun t => rfl
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver (isPlaceOver_vQ A₀ hA₀) (isPlaceOver_vQ A hA)
  by_cases hσK : σ ∈ K.fixingSubgroup
  · refine ⟨1, U.index.factorial, hkpos, odd_one, ?_⟩
    have hB : ∀ x ∈ K, x ∈ A ↔ x ∈ A₀ := by
      intro x hx
      rw [← hσ, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      have hfix : σ⁻¹ • x = x := (K.fixingSubgroup.inv_mem hσK) ⟨x, hx⟩
      rw [hfix]
    intro s hs
    have ht : s ^ U.index.factorial ∈ U ⊓ Ine (F := K) A := ⟨hpow s, pow_mem hs _⟩
    have h1 : β (s ^ U.index.factorial) ^ 2 = cycBar K Ω l (s ^ U.index.factorial) :=
      Units.ext (by push_cast; rw [hcyc A hB _ ht, hval])
    have e1 : (β s ^ 2 * cycBar K Ω l s ^ (-1 : ℤ)) ^ U.index.factorial =
        β (s ^ U.index.factorial) ^ 2 * (cycBar K Ω l (s ^ U.index.factorial))⁻¹ := by
      rw [map_pow, map_pow, zpow_neg, zpow_one]
      simp only [mul_pow, inv_pow, ← pow_mul]
      rw [mul_comm 2]
    rw [e1, h1, mul_inv_cancel]
  · refine ⟨-1, U.index.factorial, hkpos, ⟨-1, by norm_num⟩, ?_⟩
    haveI hN : K.fixingSubgroup.Normal := by
      refine (InfiniteGalois.normal_iff_isGalois K).2 ?_
      haveI : Algebra.IsQuadraticExtension ℚ K := ⟨hK⟩
      exact isGalois_iff.2 ⟨Algebra.IsSeparable.of_integral _ _, Algebra.IsQuadraticExtension.normal ℚ K⟩
    intro s hs
    have hg : resQ K s ∈ Ine (F := ℚ) A := (resQ_Ine K A s).1 hs
    have hlift : IsLift (RingEquiv.refl ℚ) (σ : Ω ≃+* Ω) := fun y => by simp
    have hg' : conjGal hlift (resQ K s) ∈ Ine (F := ℚ) A₀ := by
      refine conjGal_mem_Ine hlift (fun x => ?_) hg
      rw [← hσ, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      show σ⁻¹ • σ • x ∈ A₀ ↔ x ∈ A₀
      rw [inv_smul_smul]
    have heq : conjGal hlift (resQ K s) = σ⁻¹ * resQ K s * σ := by
      ext x
      rfl
    have hmem : σ⁻¹ * resQ K s * σ ∈ K.fixingSubgroup := by
      have h' := hN.conj_mem _ (resQ_mem K s) σ⁻¹
      rwa [inv_inv] at h'
    obtain ⟨s', hs'⟩ := exists_resQ hmem
    have hs'I : s' ∈ Ine (F := K) A₀ := (resQ_Ine K A₀ s').2 (by rw [hs', ← heq]; exact hg')
    have hσ' : σ⁻¹ ∉ K.fixingSubgroup := fun h' => hσK (by simpa using K.fixingSubgroup.inv_mem h')
    have hbb : β s * β s' = 1 := hconj σ⁻¹ hσ' s s' (by rw [hs', inv_inv])
    have hcy : cycBar K Ω l s' = cycBar K Ω l s := by
      show Units.map _ (cycZ K Ω l s') = Units.map _ (cycZ K Ω l s)
      have hz : cycZ ℚ Ω l (σ⁻¹ * resQ K s * σ) = cycZ ℚ Ω l (resQ K s) := by
        rw [map_mul, map_mul, map_inv, mul_comm (cycZ ℚ Ω l σ)⁻¹, inv_mul_cancel_right]
      rw [← resQ_cyc, ← resQ_cyc, hs', hz]
    have ht' : s' ^ U.index.factorial ∈ U ⊓ Ine (F := K) A₀ := ⟨hpow s', pow_mem hs'I _⟩
    have h1 : β (s' ^ U.index.factorial) ^ 2 = cycBar K Ω l (s' ^ U.index.factorial) :=
      Units.ext (by push_cast; rw [hcyc A₀ (fun _ _ => Iff.rfl) _ ht', hval])
    have hbs : β s = (β s')⁻¹ := eq_inv_of_mul_eq_one_left hbb
    have e2 : (β s ^ 2 * cycBar K Ω l s ^ (-(-1) : ℤ)) ^ U.index.factorial =
        (β (s' ^ U.index.factorial) ^ 2)⁻¹ * cycBar K Ω l (s' ^ U.index.factorial) := by
      rw [neg_neg, zpow_one, hbs, ← hcy, map_pow, map_pow]
      simp only [mul_pow, inv_pow, ← pow_mul]
      rw [mul_comm 2]
    rw [e2, h1, inv_mul_cancel]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

theorem UpperTheory.V.Ws.Lk.polar :
    ∀ {l : ℕ} [Fact l.Prime] (F : W.GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (χ : Fin n → F.G₀ →* Rˣ) (π : Equiv.Perm (Fin n)), (∀ i g, χ i (F.conj g) * χ (π i) g * F.eps O R g ^ ((n : ℤ) - 1) = 1) → F.IsPolar O (W.GDet.ofRep (W.diagRep χ)) := by
  intro l _ F O _ _ R _ _ n χ π hχ B _ _ _ _ y
  let Ψ : Fin n → MonoidAlgebra B F.G₀ →ₐ[B] B := fun i =>
    MonoidAlgebra.lift B B F.G₀ ((Units.coeHom B).comp (W.pushCh (algebraMap R B) (χ i)))
  have hrep : ∀ z, W.GDet.repAlg (W.diagRep χ) B z = Matrix.diagonal (fun i => Ψ i z) := by
    intro z
    induction z using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb =>
      rw [map_add (f := _), ha, hb, Matrix.diagonal_add]
      congr 1
      funext i
      rw [map_add (f := _)]
    | single g b =>
      simp only [W.GDet.repAlg, MonoidAlgebra.lift_single, Ψ]
      ext i j
      simp [W.diagRep, W.pushCh, Matrix.diagonal_apply]
  have hst : ∀ i z, Ψ i (F.star O B n z) = Ψ (π i) z := by
    intro i z
    induction z using MonoidAlgebra.induction_linear with
    | zero => simp [W.GFrame.star]
    | add a b ha hb =>
      simp only [W.GFrame.star, map_add (f := _), MulOpposite.unop_add] at ha hb ⊢
      rw [ha, hb]
    | single g b =>
      simp only [W.GFrame.star, W.GFrame.starOp, MonoidAlgebra.lift_single, Ψ]
      simp only [MonoidHom.coe_mk, OneHom.coe_mk, MulOpposite.unop_smul, MulOpposite.unop_op, map_smul,
        MonoidAlgebra.lift_single, MonoidHom.comp_apply, Units.coeHom_apply, W.pushCh, Units.coe_map,
        smul_eq_mul]
      congr 1
      have he : F.eps O B g = Units.map (algebraMap R B : R →* B) (F.eps O R g) := by
        ext
        simp [W.GFrame.eps, W.pushCh, IsScalarTower.algebraMap_apply O R B]
      have key : F.eps O R g ^ (1 - (n : ℤ)) * χ i (F.conj g)⁻¹ = χ (π i) g := by
        have h := hχ i g
        have hb : χ (π i) g = ((χ i) (F.conj g) * F.eps O R g ^ ((n : ℤ) - 1))⁻¹ := by
          rw [eq_inv_iff_mul_eq_one, mul_left_comm, ← mul_assoc]
          exact h
        rw [hb, mul_inv, show (1 : ℤ) - n = -((n : ℤ) - 1) by ring, zpow_neg, map_inv, mul_comm]
      rw [he, ← map_zpow, Units.coe_map, ← key, Units.val_mul]
      simp
  show Matrix.det (W.GDet.repAlg (W.diagRep χ) B (F.star O B n y)) =
    Matrix.det (W.GDet.repAlg (W.diagRep χ) B y)
  rw [hrep, hrep, Matrix.det_diagonal, Matrix.det_diagonal]
  simp only [hst]
  exact Equiv.prod_comp π (fun i => Ψ i y)
end
