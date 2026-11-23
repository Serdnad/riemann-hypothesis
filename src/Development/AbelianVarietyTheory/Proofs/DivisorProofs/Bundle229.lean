module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Discriminant
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle121
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleOfEtaleAtHeightOnePrimes
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle119
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle120
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
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open TensorProduct IsLocalRing

namespace GlobalTheory

theorem tensorLift_injective_of_flat {R S A K L : Type} [CommRing R] [CommRing S] [IsDomain S]
    [CommRing A] [Field K] [Field L] [Algebra R S] [Module.Flat R S] [Algebra R A] [Algebra R K]
    [IsFractionRing R K] [Algebra S L] [IsFractionRing S L] (i : A →ₐ[R] K)
    (hi : Function.Injective i) (f : K →+* L)
    (hf : ∀ r, f (algebraMap R K r) = algebraMap S L (algebraMap R S r)) (g : A ⊗[R] S →+* L)
    (hg : ∀ a s, g (a ⊗ₜ s) = f (i a) * algebraMap S L s) : Function.Injective g := by
  letI : Algebra R L := ((algebraMap S L).comp (algebraMap R S)).toAlgebra
  haveI : IsScalarTower R S L := .of_algebraMap_eq fun _ => rfl
  let fK : K →ₐ[R] L := { toRingHom := f, commutes' := hf }
  let H : K ⊗[R] S →ₐ[R] L :=
    Algebra.TensorProduct.lift fK (IsScalarTower.toAlgHom R S L) (fun _ _ => Commute.all _ _)
  have hH : ∀ k s, H (k ⊗ₜ s) = f k * algebraMap S L s := fun k s => by
    rw [Algebra.TensorProduct.lift_tmul]; rfl
  have hgH : ∀ x, g x = H (LinearMap.rTensor S i.toLinearMap x) := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a s => rw [hg, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, hH]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]
  have hloc : IsLocalizedModule (nonZeroDivisors R) (TensorProduct.mk R K S 1) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors R) K _).mpr (TensorProduct.isBaseChange R S K)
  haveI : Nontrivial R := (algebraMap R K).domain_nontrivial
  have hHinj : Function.Injective H := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨⟨s, r⟩, hr⟩ := IsLocalizedModule.surj (nonZeroDivisors R) (TensorProduct.mk R K S 1) y
    have hs : s = 0 := by
      have h1 : H (r • y) = 0 := by
        rw [Submonoid.smul_def, show H (r.1 • y) = r.1 • H y from H.toLinearMap.map_smul r.1 y, hy, smul_zero]
      rw [hr, TensorProduct.mk_apply, hH, map_one, one_mul] at h1
      exact IsFractionRing.injective S L (h1.trans (map_zero _).symm)
    have ha : algebraMap R K r.1 ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors r.2
    have h2 : algebraMap R K r.1 • y = 0 := by
      rw [algebraMap_smul, ← Submonoid.smul_def, hr, hs, TensorProduct.mk_apply, TensorProduct.tmul_zero]
    rw [← one_smul K y, ← inv_mul_cancel₀ ha, mul_smul, h2, smul_zero]
  intro x y hxy
  rw [hgH, hgH] at hxy
  exact Module.Flat.rTensor_preserves_injective_linearMap (M := S) i.toLinearMap hi (hHinj hxy)

def rangeValuationSubring {B L : Type} [CommRing B] [IsDomain B] [ValuationRing B] [Field L]
    (j : B →+* L) (hj : ∀ x : L, ∃ a b : B, j b ≠ 0 ∧ x = j a / j b) : ValuationSubring L where
  toSubring := j.range
  mem_or_inv_mem' x := by
    obtain ⟨a, b, hb, rfl⟩ := hj x
    obtain ⟨c, hc | hc⟩ := ValuationRing.cond a b
    · right
      have ha : j a ≠ 0 := fun h => hb (by rw [← hc, map_mul, h, zero_mul])
      exact ⟨c, by rw [inv_div, ← hc, map_mul, mul_div_cancel_left₀ _ ha]⟩
    · left
      exact ⟨c, by rw [← hc, map_mul, mul_div_cancel_left₀ _ hb]⟩

theorem exists_valuationSubring_extend_of_formallyEtale : ∀ {K K' R S : Type} [Field K] [Field K']
    [CommRing R] [CommRing S] [IsDomain R] [IsDomain S] [IsLocalRing R] [IsLocalRing S] [Algebra R K]
    [Algebra S K'] [IsFractionRing R K] [IsFractionRing S K'] (φ : K →+* K') (σ : R →+* S)
    [IsLocalHom σ], σ.Flat → σ.FormallyEtale → σ.EssFiniteType →
    φ.comp (algebraMap R K) = (algebraMap S K').comp σ → ∀ V : ValuationSubring K,
    IsDiscreteValuationRing V → (∀ a, algebraMap R K a ∈ V) →
    ∃ (V' : ValuationSubring K') (h : ∀ x ∈ V, φ x ∈ V'), IsDiscreteValuationRing V' ∧
      (∀ b, algebraMap S K' b ∈ V') ∧ (∀ x, φ x ∈ V' → x ∈ V) ∧
      (φ.restrict V V' h).FormallyEtale ∧ (φ.restrict V V' h).EssFiniteType := by
  intro K K' R S _ _ _ _ _ _ _ _ _ _ _ _ φ σ _ hfl het hef hc V hV hRV
  letI : Algebra R S := σ.toAlgebra
  haveI : Module.Flat R S := hfl
  haveI : Algebra.FormallyEtale R S := het
  haveI : Algebra.EssFiniteType R S := hef
  haveI : IsLocalHom (algebraMap R S) := ‹IsLocalHom σ›
  haveI : Module.FaithfullyFlat R S := .of_flat_of_isLocalHom
  letI : Algebra R V := ((algebraMap R K).codRestrict V hRV).toAlgebra
  letI : Algebra R K' := ((algebraMap S K').comp σ).toAlgebra
  haveI : IsScalarTower R S K' := .of_algebraMap_eq fun _ => rfl
  let fV : V →ₐ[R] K' := { toRingHom := φ.comp V.subtype, commutes' := fun r => RingHom.congr_fun hc r }
  let iV : V →ₐ[R] K := { toRingHom := V.subtype, commutes' := fun _ => rfl }
  let g : V ⊗[R] S →ₐ[R] K' :=
    Algebra.TensorProduct.lift fV (IsScalarTower.toAlgHom R S K') (fun _ _ => Commute.all _ _)
  have hg' : ∀ (a : V) (s : S), g (a ⊗ₜ s) = φ a * algebraMap S K' s := fun a s => by
    rw [Algebra.TensorProduct.lift_tmul]; rfl
  have hg1 : ∀ s : S, g (1 ⊗ₜ s) = algebraMap S K' s := fun s => by
    rw [hg']; simp
  have hg : Function.Injective g :=
    tensorLift_injective_of_flat (S := S) (L := K') iV Subtype.val_injective φ (RingHom.congr_fun hc) g.toRingHom hg'
  let C := V ⊗[R] S
  haveI : IsDomain C := Function.Injective.isDomain g.toRingHom hg
  obtain ⟨⟨Q, hQ⟩, hQm⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := V) (B := C)
    ⟨maximalIdeal V, inferInstance⟩
  have hQm' : Q.comap (algebraMap V C) = maximalIdeal V := congrArg PrimeSpectrum.asIdeal hQm
  let B := Localization.AtPrime Q
  haveI : Module.Flat V B := Module.Flat.trans V C B
  haveI : Algebra.EssFiniteType V B := .comp V C B
  haveI : Algebra.FormallyEtale V B := .comp V C B
  have hQB : ∀ c : C, IsUnit (algebraMap C B c) ↔ c ∉ Q := fun c =>
    IsLocalization.AtPrime.isUnit_to_map_iff B Q c
  haveI : IsLocalHom (algebraMap V B) := ⟨fun v hv => by
    by_contra hn
    have h1 : algebraMap V C v ∈ Q := by rw [← Ideal.mem_comap, hQm']; exact hn
    rw [IsScalarTower.algebraMap_apply V C B] at hv
    exact (hQB _).mp hv h1⟩
  obtain ⟨_, hB⟩ := exists_isDiscreteValuationRing_of_unramified V B
  have hunit : ∀ y : Q.primeCompl, IsUnit (g.toRingHom y) := fun y => by
    refine Ne.isUnit fun h0 => y.2 ?_
    rw [hg (h0.trans (map_zero g).symm)]
    exact Q.zero_mem
  let j : B →+* K' := IsLocalization.lift (M := Q.primeCompl) (S := B) hunit
  have hjC : ∀ c, j (algebraMap C B c) = g c := IsLocalization.lift_eq (M := Q.primeCompl) (S := B) hunit
  have hj : Function.Injective j := IsLocalization.injective_of_map_algebraMap_zero (M := Q.primeCompl) B j fun x hx => by
    rw [hjC] at hx
    rw [hg (hx.trans (map_zero g).symm), map_zero]
  have hgen : ∀ x : K', ∃ a b : B, j b ≠ 0 ∧ x = j a / j b := fun x => by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := S) x
    refine ⟨algebraMap C B (1 ⊗ₜ a), algebraMap C B (1 ⊗ₜ b), ?_, ?_⟩
    · rw [hjC, hg1]
      exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    · rw [hjC, hjC, hg1, hg1]
  let V' := rangeValuationSubring j hgen
  have hVV' : ∀ x ∈ V, φ x ∈ V' := fun x hx =>
    ⟨algebraMap C B (⟨x, hx⟩ ⊗ₜ 1), by rw [hjC, hg', map_one, mul_one]⟩
  let e₀ : B →+* V' := j.codRestrict V' fun b => ⟨b, rfl⟩
  have he₀ : Function.Bijective e₀ :=
    ⟨fun a b h => hj (congrArg Subtype.val h), fun y => by
      obtain ⟨b, hb⟩ := y.2
      exact ⟨b, Subtype.ext hb⟩⟩
  let e : B ≃+* V' := RingEquiv.ofBijective e₀ he₀
  have he : ∀ b, (e b : K') = j b := fun _ => rfl
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible V
  have htQ : algebraMap V C t ∈ Q := by
    rw [← Ideal.mem_comap, hQm']
    exact (mem_maximalIdeal _).mpr ht.not_isUnit
  have htB : ¬ IsUnit (algebraMap C B (algebraMap V C t)) := fun h => (hQB _).mp h htQ
  have hφt : φ t ≠ 0 := by
    rw [map_ne_zero]
    exact fun h => ht.ne_zero (Subtype.ext h)
  have hjt : j (algebraMap C B (algebraMap V C t)) = φ t := by
    rw [hjC, Algebra.TensorProduct.algebraMap_apply, hg']
    simp
  have key : (φ t)⁻¹ ∉ V' := by
    rintro ⟨b, hb⟩
    refine htB (IsUnit.of_mul_eq_one b (hj ?_))
    rw [map_mul, hb, map_one, hjt, mul_inv_cancel₀ hφt]
  refine ⟨V', hVV', ?_, fun b => ⟨algebraMap C B (1 ⊗ₜ b), by rw [hjC, hg1]⟩, ?_, ?_⟩
  · obtain ⟨b, hbm, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (IsDiscreteValuationRing.not_a_field B)
    exact
      { toIsPrincipalIdealRing := IsPrincipalIdealRing.of_surjective e.toRingHom e.surjective
        toIsLocalRing := inferInstance
        not_a_field' := fun h => by
          have h1 : e b ∈ maximalIdeal V' := fun hu => hbm (by simpa using hu.map e.symm.toRingHom)
          rw [h] at h1
          exact hb0 (e.injective (by simpa using h1)) }
  · intro x hx
    by_contra hxV
    have hinv : x⁻¹ ∈ V := (V.mem_or_inv_mem x).resolve_left hxV
    have hx0 : x ≠ 0 := fun h => hxV (h ▸ V.zero_mem)
    obtain ⟨n, u, hn⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨x⁻¹, hinv⟩ : V)) (fun h => inv_ne_zero hx0 (congrArg Subtype.val h)) ht
    have hn' : x⁻¹ = (u : K) * (t : K) ^ n := congrArg Subtype.val hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
      refine Nat.exists_eq_add_one.mpr (Nat.pos_of_ne_zero fun h0 => hxV ?_)
      have h2 : ((u : V) : K) * (((u⁻¹ : Vˣ) : V) : K) = 1 := by
        exact_mod_cast congrArg Subtype.val u.mul_inv
      have hn0 : x⁻¹ = (u : K) := by rw [hn', h0, pow_zero, mul_one]
      have : x = (((u⁻¹ : Vˣ) : V) : K) := by
        rw [← inv_inv x, hn0]
        exact inv_eq_of_mul_eq_one_right h2
      exact this ▸ Subtype.property _
    apply key
    have ht0 : (t : K) ≠ 0 := fun h => ht.ne_zero (Subtype.ext h)
    have : (φ t)⁻¹ = φ ((t ^ m * u : V) : K) * φ x := by
      rw [← map_inv₀, ← map_mul]
      congr 1
      have hu0 : ((u : V) : K) ≠ 0 := fun h => u.ne_zero (Subtype.ext h)
      have hx' : x = ((u : K) * (t : K) ^ (m + 1))⁻¹ := by rw [← hn', inv_inv]
      rw [hx']
      push_cast
      field_simp
      ring
    rw [this]
    exact mul_mem (hVV' _ (t ^ m * u : V).2) hx
  · letI : Algebra V V' := (φ.restrict V V' hVV').toAlgebra
    let eA : B ≃ₐ[V] V' := AlgEquiv.ofRingEquiv (f := e) fun v => Subtype.ext (by
      rw [he, IsScalarTower.algebraMap_apply V C B, hjC, Algebra.TensorProduct.algebraMap_apply,
        hg']
      simp
      rfl)
    exact ⟨Algebra.FormallyEtale.of_equiv eA, Algebra.EssFiniteType.of_surjective eA.toAlgHom eA.surjective⟩

end GlobalTheory
end

section

open IsLocalRing

theorem _root_.GlobalTheory.T.eq_map_maximalIdeal_of_ringKrullDim_eq_one' : ∀ (R A : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing A] [IsDomain A] [Algebra R A] [Module.Flat R A] (p : Ideal A) [p.IsPrime], (maximalIdeal R).map (algebraMap R A) ≤ p → ringKrullDim (Localization.AtPrime p) = 1 → IsDomain (A ⧸ (maximalIdeal R).map (algebraMap R A)) → p = (maximalIdeal R).map (algebraMap R A) := by
  first | exact @GlobalTheory.eq_map_maximalIdeal_of_ringKrullDim_eq_one | exact GlobalTheory.eq_map_maximalIdeal_of_ringKrullDim_eq_one | (intros; apply GlobalTheory.eq_map_maximalIdeal_of_ringKrullDim_eq_one <;> assumption)
end

section

open Polynomial

namespace GlobalTheory

theorem exists_dvr_localization_of_minimal_prime : ∀ {κ : Type} [Field κ] (R : Subring κ)
    [IsNoetherianRing R] [IsIntegrallyClosed R] [IsFractionRing R κ] (Q : Ideal R) [Q.IsPrime],
    Q ≠ ⊥ → (∀ p : Ideal R, p.IsPrime → p ≠ ⊥ → p ≤ Q → p = Q) →
    ∃ W : ValuationSubring κ, IsDiscreteValuationRing W ∧ (∀ r : R, (r : κ) ∈ W) ∧
      (∀ r : R, r ∉ Q → (r : κ)⁻¹ ∈ W) ∧ (∀ r : R, r ∈ Q → r ≠ 0 → (r : κ)⁻¹ ∉ W) ∧
      (∀ w ∈ W, ∃ b s : R, s ∉ Q ∧ w = b / s) := by
  first
  | exact @_root_.GlobalTheory.AuxiliaryLemmaSecond.main
  | exact _root_.GlobalTheory.AuxiliaryLemmaSecond.main
  | (apply _root_.GlobalTheory.AuxiliaryLemmaSecond.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.AuxiliaryLemmaSecond.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AuxiliaryLemmaSecond.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AuxiliaryLemmaSecond.main ..)

end GlobalTheory
end

section


theorem _root_.GlobalTheory.T.isDVR_of_principal_prime_localization : ∀ {L : Type} [Field L] (A : Subring L) (t : A), IsNoetherianRing A → (t : L) ≠ 0 →
    (Ideal.span {t}).IsPrime → (∀ f : L, ∃ a ∈ A, ∃ b ∈ A, b ≠ 0 ∧ f * b = a) →
    ∃ (V : ValuationSubring L) (hA : ∀ a ∈ A, a ∈ V),
      IsDiscreteValuationRing V ∧ Irreducible (⟨t, hA _ t.2⟩ : V) ∧
      (∀ s : A, s ∉ Ideal.span {t} → IsUnit (⟨s, hA _ s.2⟩ : V)) ∧
      (∀ f : V, ∃ a s : A, s ∉ Ideal.span {t} ∧ (f : L) * s = a) ∧
      (A.subtype.codRestrict V fun a => hA _ a.2).EssFiniteType := by
  first | exact @GlobalTheory.dvr_loc_principal_prime | exact GlobalTheory.dvr_loc_principal_prime | (intros; apply GlobalTheory.dvr_loc_principal_prime <;> assumption)
end

section

open IsLocalRing

namespace GlobalTheory

theorem exists_mul_isIntegralElem_of_forall_discreteValuationSubring :
    ∀ (C B : Type) [CommRing C] [IsDomain C] [IsNoetherianRing C] [CommRing B] (e : C →+* B),
      Function.Injective e → (∀ b : B, ∃ c s : C, IsUnit (e s) ∧ b * e s = e c) →
      ∀ (p : Ideal C), p.IsPrime → ∀ f : B,
        (∀ (F : Type) [Field F] (β : B →+* F) (V : ValuationSubring F), IsDiscreteValuationRing V →
          (∀ c, β (e c) ∈ V) → (∀ c ∈ p, β (e c) ∈ V.nonunits) → β f ∈ V) →
        ∃ d : C, d ∉ p ∧ e.IsIntegralElem (e d * f) := by
  intro C B _ _ _ _ e he hloc p hp f hf
  haveI : Nontrivial B := ⟨⟨e 0, e 1, fun h => zero_ne_one (he h)⟩⟩
  haveI : NoZeroDivisors B := ⟨fun {a b} hab => by
    obtain ⟨c₁, s₁, u₁, h₁⟩ := hloc a
    obtain ⟨c₂, s₂, u₂, h₂⟩ := hloc b
    have hc : c₁ * c₂ = 0 := he (by
      rw [map_mul, ← h₁, ← h₂, map_zero,
        show a * e s₁ * (b * e s₂) = (a * b) * (e s₁ * e s₂) by ring, hab, zero_mul])
    rcases mul_eq_zero.1 hc with h | h
    · left
      rw [h, map_zero] at h₁
      exact u₁.mul_left_eq_zero.1 h₁
    · right
      rw [h, map_zero] at h₂
      exact u₂.mul_left_eq_zero.1 h₂⟩
  haveI : IsDomain B := NoZeroDivisors.to_isDomain B
  let L := FractionRing B
  let β : B →+* L := algebraMap B L
  have hβ : Function.Injective β := IsFractionRing.injective B L
  letI : Algebra C L := (β.comp e).toAlgebra
  have hCL : ∀ c, algebraMap C L c = β (e c) := fun _ => rfl
  have hinj : Function.Injective (algebraMap C L) := hβ.comp he
  haveI : FaithfulSMul C L := (faithfulSMul_iff_algebraMap_injective C L).2 hinj
  have hne : ∀ s : C, IsUnit (e s) → β (e s) ≠ 0 := fun s hs => ((hs.map β).ne_zero)
  haveI : IsFractionRing C L := IsFractionRing.of_field C L fun z => by
    obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := B) z
    obtain ⟨cx, sx, ux, hx⟩ := hloc x
    obtain ⟨cy, sy, uy, hy'⟩ := hloc y
    refine ⟨cx * sy, cy * sx, ?_⟩
    have hy0 : β y ≠ 0 := by
      rw [map_ne_zero_iff _ hβ]; exact nonZeroDivisors.ne_zero hy
    show β x / β y = _
    simp only [hCL, map_mul]
    rw [← hx, ← hy']
    simp only [map_mul]
    rw [div_eq_div_iff hy0 (mul_ne_zero (mul_ne_zero hy0 (hne sy uy)) (hne sx ux))]
    ring
  let Cp := Localization.AtPrime p
  haveI : IsNoetherianRing Cp := IsLocalization.isNoetherianRing p.primeCompl Cp inferInstance
  have hunit : ∀ y : p.primeCompl, IsUnit (algebraMap C L y) := fun y => by
    refine isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ hinj).2 ?_)
    intro h0
    exact y.2 (h0 ▸ p.zero_mem)
  letI : Algebra Cp L := (IsLocalization.lift (M := p.primeCompl) (S := Cp) hunit).toAlgebra
  haveI : IsScalarTower C Cp L :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.lift_eq hunit x).symm
  haveI : IsFractionRing Cp L := IsFractionRing.isFractionRing_of_isLocalization p.primeCompl Cp L
    p.primeCompl_le_nonZeroDivisors
  haveI : Algebra.EssFiniteType Cp L := Algebra.EssFiniteType.of_isLocalization L (nonZeroDivisors Cp)
  have hint : IsIntegral Cp (β f) := by
    by_contra hn
    obtain ⟨V, hV, hd, hfV⟩ := exists_discreteValuationSubring_dominating_notMem hn
    obtain ⟨h1, h2⟩ := (localSubring_range_le_valuationSubring_iff _ V).1 hd
    apply hfV
    refine hf L β V hV (fun c => ?_) (fun c hc => ?_)
    · have := h1 (algebraMap C Cp c)
      rwa [← IsScalarTower.algebraMap_apply] at this
    · have := h2 (algebraMap C Cp c)
        ((IsLocalization.AtPrime.to_map_mem_maximal_iff Cp p c).2 hc)
      rwa [← IsScalarTower.algebraMap_apply] at this
  obtain ⟨⟨d, hd⟩, hdi⟩ := IsIntegral.exists_multiple_integral_of_isLocalization p.primeCompl (β f) hint
  refine ⟨d, hd, ?_⟩
  obtain ⟨q, hq, hq0⟩ := hdi
  refine ⟨q, hq, hβ ?_⟩
  rw [Polynomial.hom_eval₂, map_zero, ← hq0, Submonoid.smul_def, Algebra.smul_def, hCL, map_mul]
  rfl

end GlobalTheory
end

section

open IsLocalRing

open TensorProduct

namespace GlobalTheory.EtaleCoker

theorem discr_isUnit (S A : Type) [CommRing S] [IsLocalRing S] [CommRing A] [Algebra S A]
    [Algebra.Etale S A] {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι S A) :
    IsUnit (Algebra.discr S b) := by
  have h := GlobalTheory.PurityDisc.discr_ne_zero_of_etale (ResidueField S) (ResidueField S ⊗[S] A)
    (Algebra.TensorProduct.basis (ResidueField S) b)
  rw [GlobalTheory.PurityDisc.discr_baseChange] at h
  by_contra hn
  exact h ((residue_eq_zero_iff _).mpr ((mem_maximalIdeal _).mpr hn))

end GlobalTheory.EtaleCoker
end

section

open IsLocalRing TensorProduct

theorem _root_.GlobalTheory.T.exists_surj_localization_mvPolynomial_of_essFiniteType_local : ∀ (Λ R : Type) [CommRing Λ] [CommRing R] [IsLocalRing R] [Algebra Λ R] [Algebra.EssFiniteType Λ R], ∃ (n : ℕ) (P : Ideal (MvPolynomial (Fin n) Λ)) (_ : P.IsPrime) (φ : Localization.AtPrime P →ₐ[Λ] R), Function.Surjective φ := by
  first | exact @GlobalTheory.exists_surj_localization_mvPolynomial_of_essFiniteType | exact GlobalTheory.exists_surj_localization_mvPolynomial_of_essFiniteType | (intros; apply GlobalTheory.exists_surj_localization_mvPolynomial_of_essFiniteType <;> assumption)
end

section


theorem _root_.GlobalTheory.T.etale_prod_of_etale : ∀ (B A₁ A₂ : Type) [CommRing B] [CommRing A₁] [CommRing A₂] [Algebra B A₁] [Algebra B A₂], Algebra.Etale B A₁ → Algebra.Etale B A₂ → Algebra.Etale B (A₁ × A₂) := by
  first | (exact @GlobalTheory.etale_prod) | (exact GlobalTheory.etale_prod) | (intros; apply GlobalTheory.etale_prod <;> assumption)
end

section


theorem _root_.GlobalTheory.T.etale_unique_prime_le_map_maximal : ∀ (B A : Type) [CommRing B] [CommRing A] [Algebra B A] [Algebra.Etale B A] (P : Ideal B), P.IsMaximal → ∀ (Q : Ideal A), (∀ Q' : Ideal A, Q'.IsPrime → P.map (algebraMap B A) ≤ Q' → Q' = Q) → Q ≤ P.map (algebraMap B A) := by
  first | (exact @GlobalTheory.etale_prime_le_map_of_unique) | (exact GlobalTheory.etale_prime_le_map_of_unique) | (intros; apply GlobalTheory.etale_prime_le_map_of_unique <;> assumption)
end

section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.directedSystem_etale_baseChange_polynomial : ∀ (T : Type) [CommRing T] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)]
    (𝒜 : ι → Subring T) (hA : Monotone 𝒜), (∀ x : T, ∃ i, x ∈ 𝒜 i) →
    ∀ (i₀ : ι), (∀ k, i₀ ≤ k) →
    ∀ (E : Type) [CommRing E] [Algebra (Polynomial T) E]
      (E₀ : Type) [CommRing E₀] [Algebra (Polynomial (𝒜 i₀)) E₀] [Algebra.Etale (Polynomial (𝒜 i₀)) E₀],
      (letI : Algebra (Polynomial (𝒜 i₀)) (Polynomial T) :=
          (Polynomial.mapRingHom (𝒜 i₀).subtype).toAlgebra
       Nonempty (TensorProduct (Polynomial (𝒜 i₀)) (Polynomial T) E₀ ≃ₐ[Polynomial T] E)) →
    ∃ (Ek : ι → Type) (_ : ∀ k, CommRing (Ek k)) (_ : ∀ k, Algebra (Polynomial (𝒜 k)) (Ek k))
      (_ : ∀ k, Algebra (𝒜 k) (Ek k)) (_ : ∀ k, IsScalarTower (𝒜 k) (Polynomial (𝒜 k)) (Ek k))
      (_ : ∀ k, Algebra.Etale (Polynomial (𝒜 k)) (Ek k))
      (e : ∀ k, Ek k →+* E) (h : ∀ k l, k ≤ l → Ek k →+* Ek l),
      (∀ k, (e k).comp (algebraMap (Polynomial (𝒜 k)) (Ek k)) =
          (algebraMap (Polynomial T) E).comp (Polynomial.mapRingHom (𝒜 k).subtype)) ∧
      (∀ k l (hkl : k ≤ l) (a : 𝒜 k), h k l hkl (algebraMap (𝒜 k) (Ek k) a) =
          algebraMap (𝒜 l) (Ek l) (Subring.inclusion (hA hkl) a)) ∧
      (∀ k l (hkl : k ≤ l) (y : Ek k), e l (h k l hkl y) = e k y) ∧
      (∀ k (hkk : k ≤ k) (y : Ek k), h k k hkk y = y) ∧
      (∀ k l m (hkl : k ≤ l) (hlm : l ≤ m) (hkm : k ≤ m) (y : Ek k),
          h k m hkm y = h l m hlm (h k l hkl y)) ∧
      (∀ k, Function.Injective (e k)) ∧
      (∀ x : E, ∃ k y, e k y = x) := by
  first | (exact @GlobalTheory.directedSystem_etaleBaseChange) | (exact GlobalTheory.directedSystem_etaleBaseChange) | (intros; apply GlobalTheory.directedSystem_etaleBaseChange <;> assumption)
end

section

open TensorProduct

theorem _root_.GlobalTheory.T.etale_adjoin_baseChange_image' : ∀ (R S B : Type) [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra S B] [Algebra R B] [IsScalarTower R S B] (A₀ : Subalgebra R S) (B₀ : Type) [CommRing B₀] [Algebra A₀ B₀] [Algebra.Etale A₀ B₀] (e : B ≃ₐ[S] S ⊗[A₀] B₀) (S' : Subalgebra R S), A₀ ≤ S' → ∃ (_ : Algebra S' ↥(Algebra.adjoin R ((algebraMap S B) '' (S' : Set S) ∪ Set.range (fun b : B₀ => e.symm (1 ⊗ₜ b))))) (_ : IsScalarTower R S' ↥(Algebra.adjoin R ((algebraMap S B) '' (S' : Set S) ∪ Set.range (fun b : B₀ => e.symm (1 ⊗ₜ b))))), Algebra.Etale S' ↥(Algebra.adjoin R ((algebraMap S B) '' (S' : Set S) ∪ Set.range (fun b : B₀ => e.symm (1 ⊗ₜ b)))) := by
  first | exact @GlobalTheory.etale_adjoin_baseChange_image | exact GlobalTheory.etale_adjoin_baseChange_image | (intros; apply GlobalTheory.etale_adjoin_baseChange_image <;> assumption)
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.formallyEtale_baseChange_eval_hom : ∀ {k R B : Type} [CommRing k] [CommRing R] [CommRing B] [Algebra k R] [Algebra k B] {r : ℕ} (τ : Fin r → B),
  (MvPolynomial.eval₂Hom (algebraMap k B) τ).FormallyEtale →
  (MvPolynomial.eval₂Hom (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[k] B)
      (fun i => (1 : R) ⊗ₜ[k] τ i)).FormallyEtale := by
  first | exact @GlobalTheory.formallyEtale_mvPolynomial_eval₂_tensor | exact GlobalTheory.formallyEtale_mvPolynomial_eval₂_tensor | (intros; apply GlobalTheory.formallyEtale_mvPolynomial_eval₂_tensor <;> assumption)
end
