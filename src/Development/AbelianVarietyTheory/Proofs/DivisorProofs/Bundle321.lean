module

public import Mathlib.RingTheory.RingHom.Flat
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealEqBotOfFlatQuotientOfMapMaximalIdeal
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle001
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle240
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomLiftSquareZeroOfFormallyEtaleAwayDepth
public import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle241
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsIsoTermComparisonRestrictScalars
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bundle001
import ReciprocityTheory.CommutativeAlgebra.MaximalIdealSquares.RingKrullDimQuotientSpanSingletonAddOne
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.LocalRing.Module

@[expose] public section

section

open IsLocalRing TensorProduct Pointwise

namespace GlobalTheory

theorem isInteger_of_maximalIdeal_smul_isInteger (S : Type) [CommRing S] [IsRegularLocalRing S]
    (hdim : 2 ≤ ringKrullDim S) (c : FractionRing S)
    (hc : ∀ a ∈ maximalIdeal S, IsLocalization.IsInteger S (a • c)) :
    IsLocalization.IsInteger S c := by
  obtain ⟨hD, hI⟩ := GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing S
  have hinj : Function.Injective (algebraMap S (FractionRing S)) := IsFractionRing.injective S (FractionRing S)
  by_cases hA : ∀ a ∈ maximalIdeal S, ∃ y ∈ maximalIdeal S, algebraMap S (FractionRing S) y = a • c
  ·
    let N : Submodule S (FractionRing S) := Submodule.map (Algebra.linearMap S (FractionRing S)) (maximalIdeal S)
    have hne : maximalIdeal S ≠ ⊥ := by
      intro h
      have hF : IsField S := (isField_iff_maximalIdeal_eq).2 h
      have := ringKrullDim_eq_zero_of_isField hF
      rw [this] at hdim
      exact absurd hdim (by decide)
    have hN : N ≠ ⊥ := by
      intro h
      apply hne
      rw [eq_bot_iff]
      intro x hx
      have : Algebra.linearMap S (FractionRing S) x ∈ N := Submodule.mem_map_of_mem hx
      rw [h, Submodule.mem_bot] at this
      rw [Submodule.mem_bot]
      exact hinj (by simpa using this)
    have hFG : N.FG := Submodule.FG.map _ (IsNoetherian.noetherian _)
    have hint : IsIntegral S c := by
      refine isIntegral_of_smul_mem_submodule N hN hFG c ?_
      intro n hn
      obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.1 hn
      obtain ⟨y, hy, hy'⟩ := hA a ha
      refine Submodule.mem_map.2 ⟨y, hy, ?_⟩
      simp only [Algebra.linearMap_apply, smul_eq_mul]
      rw [hy', Algebra.smul_def, mul_comm]
    exact (IsIntegrallyClosed.isIntegral_iff).1 hint
  · exfalso
    push_neg at hA
    obtain ⟨a, ha, hy⟩ := hA
    obtain ⟨y, hy'⟩ := hc a ha
    have hyu : y ∉ maximalIdeal S := fun h => hy y h hy'
    have hyunit : IsUnit y := by simpa [mem_maximalIdeal, mem_nonunits_iff] using hyu
    have hspan : maximalIdeal S = Ideal.span {a} := by
      apply le_antisymm
      · intro b hb
        obtain ⟨z, hz⟩ := hc b hb
        have key : b * y = a * z := by
          apply hinj
          rw [map_mul, map_mul, hy', hz, ← Algebra.smul_def, ← Algebra.smul_def, smul_comm]
        rw [Ideal.mem_span_singleton']
        obtain ⟨u, rfl⟩ := hyunit
        refine ⟨z * ↑u⁻¹, ?_⟩
        calc z * ↑u⁻¹ * a = (a * z) * ↑u⁻¹ := by ring
          _ = (b * ↑u) * ↑u⁻¹ := by rw [key]
          _ = b := by simp [mul_assoc]
      · rw [Ideal.span_le]
        simpa using ha
    have h1 : (maximalIdeal S).spanFinrank ≤ 1 := by
      rw [hspan]
      refine (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_singleton a)).trans ?_
      simp
    have h2 := ringKrullDim_le_spanFinrank_maximalIdeal S
    have h3 : ringKrullDim S ≤ 1 := h2.trans (by exact_mod_cast h1)
    have := hdim.trans h3
    exact absurd this (by decide)

theorem isInteger_of_maximalIdeal_pow_smul_isInteger :
    ∀ (S : Type) [CommRing S] [IsRegularLocalRing S], 2 ≤ ringKrullDim S →
      ∀ (k : ℕ) (c : FractionRing S), (∀ a ∈ maximalIdeal S ^ k,
        IsLocalization.IsInteger S (a • c)) → IsLocalization.IsInteger S c := by
  intro S _ _ hdim k
  induction k with
  | zero =>
    intro c hc
    simpa using hc 1 (by simp)
  | succ k ih =>
    intro c hc
    apply isInteger_of_maximalIdeal_smul_isInteger S hdim c
    intro a ha
    apply ih
    intro b hb
    rw [smul_smul]
    apply hc
    rw [pow_succ]
    exact Ideal.mul_mem_mul hb ha

end GlobalTheory
end

section

open GlobalTheory GlobalTheory.DI

namespace GlobalTheory

theorem zmod_sq_dvd_of_mul_eq_zero (p : ℕ) [hp : Fact p.Prime] (a : ZMod (p ^ 2))
    (ha : (p : ZMod (p ^ 2)) * a = 0) : ∃ c : ZMod (p ^ 2), a = (p : ZMod (p ^ 2)) * c := by
  have h0 : ((p * a.val : ℕ) : ZMod (p ^ 2)) = 0 := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]; exact ha
  rw [ZMod.natCast_eq_zero_iff] at h0
  obtain ⟨k, hk⟩ := h0
  have h1 : a.val = p * k := by
    apply Nat.eq_of_mul_eq_mul_left hp.out.pos
    rw [hk]; ring
  refine ⟨(k : ZMod (p ^ 2)), ?_⟩
  rw [← ZMod.natCast_zmod_val a, h1, Nat.cast_mul]

theorem flat_zmod_sq_mul_p_eq_zero_iff : ∀ (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B]
    (φ : ZMod (p ^ 2) →+* B), φ.Flat → ∀ w : B, (p : B) * w = 0 ↔ ∃ v, w = p * v := by
  intro p hp B _ φ hφ w
  letI : Algebra (ZMod (p ^ 2)) B := φ.toAlgebra
  have hflat : Module.Flat (ZMod (p ^ 2)) B := hφ
  have hsmul : ∀ (r : ZMod (p ^ 2)) (b : B), r • b = φ r * b := fun r b => by
    rw [Algebra.smul_def]; rfl
  have hpB : φ (p : ZMod (p ^ 2)) = (p : B) := map_natCast φ p
  constructor
  · intro hw
    have hsum : ∑ i : Unit, (fun _ => (p : ZMod (p ^ 2))) i • (fun _ => w) i = 0 := by
      simp only [Finset.univ_unique, Finset.sum_singleton]
      rw [hsmul, hpB, hw]
    have htr := @Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (ZMod (p ^ 2)) B _ _ _ hflat Unit _ _ _ hsum
    obtain ⟨k, a, y, hy, ha⟩ := htr
    have ha' : ∀ j, (p : ZMod (p ^ 2)) * a () j = 0 := fun j => by
      simpa only [Finset.univ_unique, Finset.sum_singleton] using ha j
    choose c hc using fun j => zmod_sq_dvd_of_mul_eq_zero p (a () j) (ha' j)
    refine ⟨∑ j, φ (c j) * y j, ?_⟩
    have hw : w = ∑ j, a () j • y j := hy ()
    rw [hw, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hsmul, hc j, map_mul, hpB, mul_assoc]
  · rintro ⟨v, rfl⟩
    have h2 : (((p ^ 2 : ℕ) : ZMod (p ^ 2))) = 0 := ZMod.natCast_self _
    have : ((p ^ 2 : ℕ) : B) = 0 := by
      rw [← map_natCast φ, h2, map_zero]
    rw [← mul_assoc, ← Nat.cast_mul, ← pow_two, this, zero_mul]

end GlobalTheory
end

section

open IsLocalRing

namespace GlobalTheory

section

variable {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]

theorem isLocalHom_mk_maximalIdeal_pow_succ (n : ℕ) :
    IsLocalHom (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1))) := by
  refine ⟨fun a ha => ?_⟩
  by_contra hu
  obtain ⟨c, hc⟩ := ha.exists_right_inv
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
  rw [← map_mul, ← map_one (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1))),
    Ideal.Quotient.eq] at hc
  have h1 : a * c - 1 ∈ maximalIdeal A := Ideal.pow_le_self n.succ_ne_zero hc
  have h2 : a * c ∈ maximalIdeal A := Ideal.mul_mem_right _ _ hu
  have h3 : (1 : A) ∈ maximalIdeal A := by simpa using sub_mem h2 h1
  exact (maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).mpr h3)

theorem quotientMap_pow_bijective_of_retraction (φ : A →+* B) [IsLocalHom φ] (n : ℕ)
    (hle : maximalIdeal A ^ (n + 1) ≤ (maximalIdeal B ^ (n + 1)).comap φ)
    (ψ : B →+* A ⧸ maximalIdeal A ^ (n + 1)) (hψ : ψ.comp φ = Ideal.Quotient.mk _)
    (huniq : ∀ g₁ g₂ : B →+* B ⧸ maximalIdeal B ^ (n + 1), IsLocalHom g₁ → IsLocalHom g₂ →
      g₁.comp φ = g₂.comp φ → g₁ = g₂) :
    Function.Bijective (Ideal.quotientMap (maximalIdeal B ^ (n + 1)) φ hle) := by
  haveI hA := isLocalHom_mk_maximalIdeal_pow_succ (A := A) n
  haveI hB := isLocalHom_mk_maximalIdeal_pow_succ (A := B) n
  have hψφ : ∀ a, ψ (φ a) = Ideal.Quotient.mk _ a := fun a => RingHom.congr_fun hψ a
  have hsurj : Function.Surjective ψ := fun x => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨φ a, hψφ a⟩
  haveI : Nontrivial (A ⧸ maximalIdeal A ^ (n + 1)) :=
    Ideal.Quotient.nontrivial_iff.mpr fun h =>
      (maximalIdeal.isMaximal A).ne_top (top_le_iff.mp (h ▸ Ideal.pow_le_self n.succ_ne_zero))
  haveI hψl : IsLocalHom ψ := IsLocalHom.of_surjective ψ hsurj
  haveI hφl : IsLocalHom (Ideal.quotientMap (maximalIdeal B ^ (n + 1)) φ hle) := by
    refine ⟨fun x hx => ?_⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.quotientMap_mk] at hx
    exact (IsUnit.of_map φ _ (IsUnit.of_map (Ideal.Quotient.mk _) _ hx)).map _
  have key := huniq (Ideal.Quotient.mk _)
    ((Ideal.quotientMap (maximalIdeal B ^ (n + 1)) φ hle).comp ψ) hB inferInstance (by
      ext a
      simp [hψφ])
  refine ⟨(injective_iff_map_eq_zero _).mpr fun x hx => ?_, fun y => ?_⟩
  · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem] at hx
    have h1 : maximalIdeal B ≤ ((maximalIdeal A).map
        (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1)))).comap ψ := by
      intro b hb
      obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (ψ b)
      rw [Ideal.mem_comap, ← hc]
      refine Ideal.mem_map_of_mem _ fun hu => hb ?_
      exact IsUnit.of_map ψ _ (hc ▸ hu.map _)
    have h2 := pow_le_comap_pow_of_le h1 (n + 1) hx
    rwa [Ideal.mem_comap, ← Ideal.map_pow, Ideal.map_quotient_self, hψφ, Ideal.mem_bot] at h2
  · obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨ψ b, (RingHom.congr_fun key b).symm⟩

end

theorem flat_of_retractions_mod_pow {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B] (φ : A →+* B) [IsLocalHom φ]
    (hex : ∀ n : ℕ, ∃ ψ : B →+* A ⧸ maximalIdeal A ^ (n + 1), ψ.comp φ = Ideal.Quotient.mk _)
    (huniq : ∀ n : ℕ, ∀ g₁ g₂ : B →+* B ⧸ maximalIdeal B ^ (n + 1), IsLocalHom g₁ →
      IsLocalHom g₂ → g₁.comp φ = g₂.comp φ → g₁ = g₂) : φ.Flat := by
  have hle : maximalIdeal A ≤ (maximalIdeal B).comap φ := fun a ha => map_nonunit φ a ha
  have hbij : ∀ n : ℕ, Function.Bijective
      (Ideal.quotientMap (maximalIdeal B ^ n) φ (pow_le_comap_pow_of_le hle n)) := by
    intro n
    cases n with
    | zero =>
      haveI : Subsingleton (A ⧸ maximalIdeal A ^ 0) := Ideal.Quotient.subsingleton_iff.mpr (by simp)
      haveI : Subsingleton (B ⧸ maximalIdeal B ^ 0) := Ideal.Quotient.subsingleton_iff.mpr (by simp)
      exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩
    | succ n =>
      obtain ⟨ψ, hψ⟩ := hex n
      exact quotientMap_pow_bijective_of_retraction φ n _ ψ hψ (huniq n)
  refine ringHom_flat_of_flat_quotientMap_pow φ ?_ (maximalIdeal_le_jacobson _)
    (pow_le_comap_pow_of_le hle) fun n => RingHom.Flat.of_bijective (hbij n)
  refine le_antisymm (Ideal.map_le_of_le_comap hle)
    (Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _)
      (maximalIdeal_le_jacobson _) fun y hy => ?_)
  obtain ⟨x, hx⟩ := (hbij 2).2 (Ideal.Quotient.mk _ y)
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Ideal.quotientMap_mk, Ideal.Quotient.eq] at hx
  have hxm : x ∈ maximalIdeal A := by
    have : φ x ∈ maximalIdeal B := by
      simpa using add_mem (Ideal.pow_le_self two_ne_zero hx) hy
    exact fun hu => this (hu.map φ)
  rw [show y = φ x - (φ x - y) by ring]
  refine sub_mem (Submodule.mem_sup_left (Ideal.mem_map_of_mem _ hxm)) (Submodule.mem_sup_right ?_)
  rwa [smul_eq_mul, ← pow_two]

end GlobalTheory
end

section

open IsLocalRing TensorProduct ReciprocityTheory.AnForm.R

theorem _root_.GlobalTheory.T.geomRegFib_of_isRegularRing_tensor_essFiniteType : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B], (∀ (K : Type) [Field K] [Algebra R K] [Algebra.EssFiniteType R K], IsRegularRing (B ⊗[R] K)) → FinalTheorems.GeomRegFib R B := by
  first | exact @GlobalTheory.geomRegFib_of_isRegularRing_essFiniteType | exact GlobalTheory.geomRegFib_of_isRegularRing_essFiniteType | (intros; apply GlobalTheory.geomRegFib_of_isRegularRing_essFiniteType <;> assumption)
end

section

open IsLocalRing

namespace GlobalTheory


open Pointwise in
theorem modDepthGE_quotient_map_span_singleton :
    ∀ (R A : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing A] [Algebra R A]
      [Module.Finite R A] (f : R), f ∈ maximalIdeal R → ∀ [IsLocalRing (R ⧸ Ideal.span {f})],
      IsSMulRegular A f → ∀ n : ℕ, ReciprocityTheory.CA.ModDepthGE R A (n + 1) →
      ReciprocityTheory.CA.ModDepthGE (R ⧸ Ideal.span {f}) (A ⧸ (Ideal.span {f}).map (algebraMap R A)) n := by
  intro R A _ _ _ _ _ _ f hf _ hreg n hd
  have h1 : ReciprocityTheory.CA.ModDepthGE R (QuotSMulTop f A) n := ReciprocityTheory.CA.ModDepthGE.quotSMulTop hf hreg hd
  have heq : (f • (⊤ : Submodule R A)) =
      ((Ideal.span {f}).map (algebraMap R A)).restrictScalars R := by
    ext x
    simp [Submodule.mem_smul_pointwise_iff_exists, Ideal.map_span, Ideal.mem_span_singleton',
      Algebra.smul_def, mul_comm]
  let e : QuotSMulTop f A ≃ₗ[R] (A ⧸ (Ideal.span {f}).map (algebraMap R A)) :=
    (Submodule.quotEquivOfEq _ _ heq).trans
      (Submodule.Quotient.restrictScalarsEquiv R ((Ideal.span {f}).map (algebraMap R A)))
  obtain ⟨rs, hl, hm, hr⟩ := (ReciprocityTheory.CA.modDepthGE_congr e n).mp h1
  refine ⟨rs.map (algebraMap R (R ⧸ Ideal.span {f})), by simp [hl], ?_, ?_⟩
  · intro r hr'
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr'
    exact ReciprocityTheory.CA.mk_mem_maximalIdeal_quot _ (hm a ha)
  · exact (ReciprocityTheory.CA.isRegular_map_algebraMap_iff' rs).mpr hr

end GlobalTheory
end

section

open IsLocalRing TensorProduct Pointwise

theorem _root_.GlobalTheory.T.modDepthGE_two_of_regular_quotient_no_socle : ∀ (S : Type) [CommRing S] [IsLocalRing S] [IsNoetherianRing S] (M : Type) [AddCommGroup M] [Module S M] [Module.Finite S M] [Nontrivial M] (x : S), x ∈ maximalIdeal S → IsSMulRegular M x → (∀ u : M, (∀ a ∈ maximalIdeal S, a • u ∈ x • (⊤ : Submodule S M)) → u ∈ x • (⊤ : Submodule S M)) → ReciprocityTheory.CA.ModDepthGE S M 2 := by
  first | exact @GlobalTheory.modDepthGE_two_of_isSMulRegular_of_quotSMulTop | exact GlobalTheory.modDepthGE_two_of_isSMulRegular_of_quotSMulTop | (intros; apply GlobalTheory.modDepthGE_two_of_isSMulRegular_of_quotSMulTop <;> assumption)
end

section

open IsLocalRing TensorProduct Pointwise

namespace GlobalTheory

theorem isSMulRegular_of_etale_punctured_of_depth_pos_domain :
    ∀ (S : Type) [CommRing S] [IsLocalRing S] [IsNoetherianRing S] [IsDomain S] (A : Type)
      [CommRing A] [Algebra S A], ReciprocityTheory.CA.ModDepthGE S A 1 →
      (∀ (p : Ideal S) [p.IsPrime], p ≠ maximalIdeal S →
        Algebra.Etale (Localization.AtPrime p) (TensorProduct S (Localization.AtPrime p) A)) →
      ∀ s : S, s ≠ 0 → IsSMulRegular A s := by
  intro S _ _ _ _ A _ _ hdepth het f hf
  obtain ⟨rs, hlen, hmem, hreg⟩ := hdepth
  obtain ⟨w, hw⟩ : ∃ w, rs = [w] := List.length_eq_one_iff.mp hlen
  subst hw
  have hwm : w ∈ maximalIdeal S := hmem w (by simp)
  have hwr : IsSMulRegular A w := ((RingTheory.Sequence.isRegular_cons_iff A w []).mp hreg).1
  have hmax : maximalIdeal S ∉ associatedPrimes S A := ReciprocityTheory.CA.max_not_mem_ass_of_reg hwm hwr
  refine IsSMulRegular.of_right_eq_zero_of_smul fun a ha => ?_
  by_contra ha0
  obtain ⟨P, hP, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing S a ha0
  have hfP : f ∈ P := hle (Submodule.mem_colon_singleton.mpr (by simpa using ha))
  obtain ⟨hPprime, b, hb⟩ := Submodule.isAssociatedPrime_iff.mp hP
  haveI := hPprime
  have hPm : P ≠ maximalIdeal S := fun h => hmax (h ▸ hP)
  haveI := het P hPm
  set L := Localization.AtPrime P
  haveI : Module.Flat L (TensorProduct S L A) := inferInstance
  have hfb : f • b = 0 := by
    have : f ∈ (⊥ : Submodule S A).colon {b} := hb ▸ hfP
    simpa using Submodule.mem_colon_singleton.mp this
  have hloc : IsLocalizedModule P.primeCompl (TensorProduct.mk S L A 1) :=
    (isLocalizedModule_iff_isBaseChange P.primeCompl L _).mpr (TensorProduct.isBaseChange S A L)
  have hfL : algebraMap S L f ≠ 0 := by
    intro h0
    apply hf
    exact (IsLocalization.injective L (Ideal.primeCompl_le_nonZeroDivisors P)) (by simpa using h0)
  have h1 : (1 : L) ⊗ₜ[S] b = 0 := by
    have : algebraMap S L f • ((1 : L) ⊗ₜ[S] b) = 0 := by
      rw [algebraMap_smul, ← TensorProduct.tmul_smul, hfb, TensorProduct.tmul_zero]
    have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := TensorProduct S L A)
      (mem_nonZeroDivisors_of_ne_zero hfL)
    exact hreg (show algebraMap S L f • ((1 : L) ⊗ₜ[S] b) = algebraMap S L f • 0 by rw [this, smul_zero])
  obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff P.primeCompl (TensorProduct.mk S L A 1)).mp h1
  have htP : (t : S) ∈ P := by
    have : (t : S) ∈ (⊥ : Submodule S A).colon {b} :=
      Submodule.mem_colon_singleton.mpr (by simpa [Submonoid.smul_def] using ht)
    exact hb ▸ this
  exact t.2 htP

end GlobalTheory
end

section

open IsLocalRing

theorem _root_.GlobalTheory.T.algHom_lift_squareZero_of_formallyEtale_away_depth : ∀ (R : Type) [CommRing R] [IsLocalRing R] (A : Type) [CommRing A] [Algebra R A], (∀ g ∈ maximalIdeal R, Algebra.FormallyEtale (Localization.Away g) (TensorProduct R (Localization.Away g) A)) → ∀ (S T : Type) [CommRing S] [Algebra R S] [CommRing T] [Algebra R T], ReciprocityTheory.CA.ModDepthGE R S 2 → ReciprocityTheory.CA.ModDepthGE R T 1 → ∀ (π : S →ₐ[R] T), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (φ : A →ₐ[R] T), ∃ ψ : A →ₐ[R] S, π.comp ψ = φ := by
  first | exact @GlobalTheory.SquareZeroLift.squareZeroLift | exact GlobalTheory.SquareZeroLift.squareZeroLift | (intros; apply GlobalTheory.SquareZeroLift.squareZeroLift <;> assumption)
end

section

open IsLocalRing

namespace GlobalTheory

theorem isSMulRegular_of_etale_punctured_of_depth_pos :
    ∀ (R A : Type) [CommRing R] [IsRegularLocalRing R] [CommRing A] [Algebra R A]
      [Module.Finite R A], ReciprocityTheory.CA.ModDepthGE R A 1 →
      (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R →
        Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) →
      ∀ f : R, f ≠ 0 → IsSMulRegular A f := by
  intro R A _ _ _ _ _ hdepth het f hf

  obtain ⟨rs, hlen, hmem, hreg⟩ := hdepth
  obtain ⟨w, hw⟩ : ∃ w, rs = [w] := List.length_eq_one_iff.mp hlen
  subst hw
  have hwm : w ∈ maximalIdeal R := hmem w (by simp)
  have hwr : IsSMulRegular A w := ((RingTheory.Sequence.isRegular_cons_iff A w []).mp hreg).1
  have hmax : maximalIdeal R ∉ associatedPrimes R A := ReciprocityTheory.CA.max_not_mem_ass_of_reg hwm hwr

  refine IsSMulRegular.of_right_eq_zero_of_smul fun a ha => ?_
  by_contra ha0
  obtain ⟨P, hP, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R a ha0
  have hfP : f ∈ P := hle (Submodule.mem_colon_singleton.mpr (by simpa using ha))
  obtain ⟨hPprime, b, hb⟩ := Submodule.isAssociatedPrime_iff.mp hP
  haveI := hPprime
  have hPm : P ≠ maximalIdeal R := fun h => hmax (h ▸ hP)
  haveI := het P hPm
  set L := Localization.AtPrime P
  haveI : Module.Free L (TensorProduct R L A) := Module.free_of_flat_of_isLocalRing
  have hfb : f • b = 0 := by
    have : f ∈ (⊥ : Submodule R A).colon {b} := hb ▸ hfP
    simpa using Submodule.mem_colon_singleton.mp this
  have hloc : IsLocalizedModule P.primeCompl (TensorProduct.mk R L A 1) :=
    (isLocalizedModule_iff_isBaseChange P.primeCompl L _).mpr (TensorProduct.isBaseChange R A L)
  have hfL : algebraMap R L f ≠ 0 := by
    intro h0
    apply hf
    exact (IsLocalization.injective L (Ideal.primeCompl_le_nonZeroDivisors P)) (by simpa using h0)
  have h1 : (1 : L) ⊗ₜ[R] b = 0 := by
    have : algebraMap R L f • ((1 : L) ⊗ₜ[R] b) = 0 := by
      rw [algebraMap_smul, ← TensorProduct.tmul_smul, hfb, TensorProduct.tmul_zero]
    exact (smul_eq_zero.mp this).resolve_left hfL
  obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff P.primeCompl (TensorProduct.mk R L A 1)).mp h1
  have htP : (t : R) ∈ P := by
    have : (t : R) ∈ (⊥ : Submodule R A).colon {b} :=
      Submodule.mem_colon_singleton.mpr (by simpa [Submonoid.smul_def] using ht)
    exact hb ▸ this
  exact t.2 htP

end GlobalTheory
end

section

open NumberField

theorem _root_.GlobalTheory.T.rankOne_fg_lattice_eq_fractionalIdeal_smul_vector : ∀ {K : Type} [Field K] [NumberField K] {m : ℕ} (ell : Submodule (𝓞 K) (Fin m → K)),
    ReciprocityTheory.GeometryOfNumbersTheory.latRank K ell = 1 → ell.FG →
    ∃ v : Fin m → K, v ≠ 0 ∧ ∃ 𝔟 : Submodule (𝓞 K) K, 𝔟.FG ∧ 𝔟 ≠ ⊥ ∧
      ∀ e, e ∈ ell ↔ ∃ β ∈ 𝔟, e = β • v := by
  first | exact @GlobalTheory.latRank_one_eq_ideal_smul | exact GlobalTheory.latRank_one_eq_ideal_smul | (intros; apply GlobalTheory.latRank_one_eq_ideal_smul <;> assumption)
end

end

section

@[expose] public section

open GlobalTheory GlobalTheory.DI
theorem _root_.GlobalTheory.T.flat_mod_p_squared_torsion : ∀ (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (φ : ZMod (p ^ 2) →+* B), φ.Flat → ∀ w : B, (p : B) * w = 0 ↔ ∃ v, w = p * v := by
  first | exact @_root_.GlobalTheory.flat_zmod_sq_mul_p_eq_zero_iff | exact _root_.GlobalTheory.flat_zmod_sq_mul_p_eq_zero_iff | (intros; apply _root_.GlobalTheory.flat_zmod_sq_mul_p_eq_zero_iff <;> assumption)

end
end
