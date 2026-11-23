module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle352
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle403
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle696
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle353
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle468
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle467
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle221
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle220
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle411
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle422
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle341
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle679
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle335
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle547
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle698
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle589
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle699
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
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization

@[expose] public section

section

open IsLocalRing Polynomial

noncomputable section

namespace GlobalTheory.KeyOriginEnlarge

theorem exists_baseChange_fits : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O]
    (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T)
      (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O)
      (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    GlobalTheory.KeyOriginEnlarge.Fits T O q A i EA QA jA ψA DA actA →
    ∀ ρ : Localization.AtPrime QA →+* A, GlobalTheory.KeyOriginEnlarge.Retracts T O A i EA QA jA ρ →
    ∀ (A₁ : Type) [CommRing A₁] [IsDomain A₁] [IsLocalRing A₁] [IsNoetherianRing A₁] [IsIntegrallyClosed A₁]
      [Algebra.EssFiniteType ℤ A₁] (j : A →+* A₁) (i₁ : A₁ →+* T),
      Function.Injective j → Function.Injective i₁ → IsLocalHom i₁ → i₁.comp j = i →
    ∃ (EA₁ : Type) (_ : CommRing EA₁) (_ : Algebra (Polynomial A₁) EA₁) (_ : Algebra A₁ EA₁)
      (_ : IsScalarTower A₁ (Polynomial A₁) EA₁) (_ : Algebra.Etale (Polynomial A₁) EA₁)
      (QA₁ : Ideal EA₁) (_ : QA₁.IsPrime) (jA₁ : Localization.AtPrime QA₁ →+* O)
      (ψA₁ : GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁) →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA₁ : Type) (_ : CommRing DA₁) (_ : Algebra (GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)) DA₁)
      (actA₁ : Multiplicative (ZMod q) →* (DA₁ ≃ₐ[GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)] DA₁))
      (ρ₁ : Localization.AtPrime QA₁ →+* A₁),
      GlobalTheory.KeyOriginEnlarge.Fits T O q A₁ i₁ EA₁ QA₁ jA₁ ψA₁ DA₁ actA₁ ∧
      GlobalTheory.KeyOriginEnlarge.Retracts T O A₁ i₁ EA₁ QA₁ jA₁ ρ₁ ∧
      ∃ (β : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁))
        (h : DA →+* DA₁),
        ψA₁.comp β = ψA ∧
        h.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) =
          (algebraMap (GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)) DA₁).comp β ∧
        ∀ σ : DA →+* FractionRing A₁,
          (σ.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA)).comp
              (algebraMap (Localization.AtPrime QA) (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA))) =
            (algebraMap A₁ (FractionRing A₁)).comp (j.comp ρ) →
          ∃ σ₁ : DA₁ →+* FractionRing A₁,
            (σ₁.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)) DA₁)).comp
                (algebraMap (Localization.AtPrime QA₁) (GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁))) =
              (algebraMap A₁ (FractionRing A₁)).comp ρ₁ := by
  intro T O _ _ _ _ _ _ _ _ P _ φ hφ hSH hP q hq A _ _ _ _ _ _ i EA _ _ _ _ _ QA _ jA ψA DA _ _ actA hFits ρ hRet
    A₁ _ _ _ _ _ _ j i₁ hj hi₁ hi₁l hij
  haveI hφl : IsLocalHom φ := hSH.2.2.1
  have hX : algebraMap (Polynomial T) O Polynomial.X ∈ maximalIdeal O := by
    rw [← hφ, RingHom.comp_apply]
    apply map_nonunit φ
    refine (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P _).2 ?_
    rw [hP]; exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  have hTO : IsLocalHom (algebraMap T O) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have h1 : Polynomial.C a ∈ P := by
      rw [hP]; exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ((IsLocalRing.mem_maximalIdeal _).2 hna))
    refine (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime P) P (Polynomial.C a)).1
      (isUnit_of_map_unit φ _ ?_) h1
    rw [← RingHom.comp_apply, hφ]
    rw [IsScalarTower.algebraMap_apply T (Polynomial T) O] at ha
    exact ha
  obtain ⟨hi, hil, hqu, hQA, hjA, hψA, htors⟩ := hFits
  obtain ⟨EA₁, _, _, _, _, _, QA₁, _, jA₁, γ₀, γ, ρ', hQA₁, hjA₁, hjγ, hγ₀, hγA, hρ'γ, hρ'id, hρ'X, hρ'c, hρ'k⟩ :=
    GlobalTheory.T.exists_baseChange_retract_alt T O hTO hX A i EA QA jA ρ hQA hjA hRet A₁ j i₁ hi₁ hi₁l hij
  obtain ⟨ρ₁, hRet₁, hρ₁⟩ := GlobalTheory.T.keyOrigin_retraction_localises T O A₁ EA₁ i₁ hi₁l hTO QA₁ jA₁ ρ' hX hρ'id hρ'X hρ'c hρ'k
  have hjA₁c : jA₁.comp (algebraMap A₁ (Localization.AtPrime QA₁)) = (algebraMap T O).comp i₁ := by
    ext a
    have e1 : algebraMap A₁ (Localization.AtPrime QA₁) a =
        algebraMap (Polynomial A₁) (Localization.AtPrime QA₁) (Polynomial.C a) := by
      rw [IsScalarTower.algebraMap_apply A₁ EA₁ (Localization.AtPrime QA₁),
        IsScalarTower.algebraMap_apply A₁ (Polynomial A₁) EA₁,
        IsScalarTower.algebraMap_apply (Polynomial A₁) EA₁ (Localization.AtPrime QA₁)]
      rfl
    rw [RingHom.comp_apply, e1, ← RingHom.comp_apply, hjA₁, RingHom.comp_apply, Polynomial.coe_mapRingHom,
      Polynomial.map_C, RingHom.comp_apply, IsScalarTower.algebraMap_apply T (Polynomial T) O]
    rfl
  obtain ⟨ψA₁, β, hψA₁, hψβ, hβ⟩ := GlobalTheory.T.generic_fibre_compatibility T O A A₁ _ _ j i₁ hj hi₁ jA jA₁ γ ψA hjA₁c hγA hjγ hψA
  have hργ : ρ₁.comp γ = j.comp ρ := by
    apply IsLocalization.ringHom_ext QA.primeCompl
    rw [RingHom.comp_assoc, hγ₀, ← RingHom.comp_assoc, hρ₁, hρ'γ, RingHom.comp_assoc]
  obtain ⟨DA₁, _, _, actA₁, h, htors₁, hh, hpt⟩ :=
    GlobalTheory.T.zmodTorsor_baseChange_transport_point A A₁ _ _ j γ ρ ρ₁ β hβ hRet₁.1 hργ q hq DA actA htors
  refine ⟨EA₁, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, QA₁, inferInstance,
    jA₁, ψA₁, DA₁, inferInstance, inferInstance, actA₁, ρ₁, ⟨hi₁, hi₁l, ?_, hQA₁, hjA₁, hψA₁, htors₁⟩, hRet₁,
    β, h, hψβ, hh, hpt⟩
  have := hqu.map j
  simpa using this

end GlobalTheory.KeyOriginEnlarge
end
end

section

open ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.RankCoinv.Nbhd

section
variable {k : Type} [Field k] {Γ : Type*} [LinearOrderedCommMonoidWithZero Γ] (v : Valuation k Γ)
variable {X Y W : Type} [Fintype Y]

theorem val_mul_le {P : Matrix X Y k} {Z : Matrix Y W k} {s t : Γ} (hP : ∀ i a, v (P i a) ≤ s)
    (hZ : ∀ a j, v (Z a j) ≤ t) (i : X) (j : W) : v ((P * Z) i j) ≤ s * t := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun a _ => ?_
  rw [map_mul]; exact mul_le_mul' (hP i a) (hZ a j)
end

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem valuation_inv_pow (ϖ : kˣ) (c : ℕ) :
    valuation k (((ϖ ^ c)⁻¹ : kˣ) : k) = (valuation k (ϖ : k))⁻¹ ^ c := by
  simp [Units.val_inv_eq_inv_val, map_inv₀, map_pow, inv_pow]

theorem exists_le_inv_pow {ϖ : kˣ} (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ) (x : k) :
    ∃ c : ℕ, valuation k x ≤ valuation k (((ϖ ^ c)⁻¹ : kˣ) : k) := by
  by_cases h : valuation k x ≤ 1
  · exact ⟨0, by simpa using h⟩
  · have hx : x ≠ 0 := by rintro rfl; simp at h
    have h0 : 0 < valuation k x := zero_lt_iff.2 (by simpa using hx)
    have hy : valuation k x⁻¹ ≤ 1 := by
      rw [map_inv₀]
      calc (valuation k x)⁻¹ = (valuation k x)⁻¹ * 1 := (mul_one _).symm
        _ ≤ (valuation k x)⁻¹ * valuation k x := mul_le_mul' le_rfl (le_of_not_ge h)
        _ = 1 := inv_mul_cancel₀ h0.ne'
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (R := 𝒪[k])
      (x := ⟨x⁻¹, hy⟩) (fun h' => hx (inv_eq_zero.1 (congrArg Subtype.val h'))) hϖ.irreducible
    refine ⟨n, ?_⟩
    have h1 : valuation k (algebraMap 𝒪[k] k u) = 1 :=
      (Valuation.integer.integers (valuation k)).one_of_isUnit u.isUnit
    have h2 : valuation k x⁻¹ = valuation k (ϖ : k) ^ n := by
      have := congrArg (fun y : 𝒪[k] => valuation k (y : k)) hu
      simp only [Subring.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow] at this
      rw [this]
      have h1' : valuation k ((u : 𝒪[k]) : k) = 1 := h1
      rw [h1', one_mul]
    rw [valuation_inv_pow, inv_pow, ← h2, map_inv₀, inv_inv]

theorem exists_bound {ϖ : kˣ} (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ) {R S : Type} [Fintype R] [Fintype S]
    (H : Matrix R S k) : ∃ c : ℕ, ∀ l i, valuation k (H l i) ≤ valuation k (((ϖ ^ c)⁻¹ : kˣ) : k) := by
  choose f hf using fun p : R × S => exists_le_inv_pow hϖ (H p.1 p.2)
  refine ⟨Finset.univ.sup f, fun l i => (hf (l, i)).trans ?_⟩
  rw [valuation_inv_pow, valuation_inv_pow]
  have hle : valuation k (ϖ : k) ≤ 1 := hϖ.mem
  have h0 : valuation k (ϖ : k) ≠ 0 := by simp
  have h1 : 1 ≤ (valuation k (ϖ : k))⁻¹ :=
    calc (1 : _) = valuation k (ϖ : k) * (valuation k (ϖ : k))⁻¹ := (mul_inv_cancel₀ h0).symm
      _ ≤ 1 * (valuation k (ϖ : k))⁻¹ := mul_le_mul' hle le_rfl
      _ = _ := one_mul _
  exact pow_le_pow_right₀ h1 (Finset.le_sup (f := f) (Finset.mem_univ (l, i)))

theorem exists_int_inv_one_add {n : Type} [Fintype n] [DecidableEq n] (E : Matrix n n k)
    (hE : ∀ i j, valuation k (E i j) < 1) :
    ∃ N : Matrix n n k, (∀ i j, N i j ∈ 𝒪[k]) ∧ (1 + E) * N = 1 := by
  have hI : ∀ i j, (1 + E) i j ∈ 𝒪[k] := fun i j => by
    rw [Valuation.mem_integer_iff, Matrix.add_apply]
    refine Valuation.map_add_le _ ?_ (hE i j).le
    rw [Matrix.one_apply]; split_ifs <;> simp
  have hEI : ∀ i j, E i j ∈ 𝒪[k] := fun i j => (Valuation.mem_integer_iff _ _).2 (hE i j).le
  let M : Matrix n n 𝒪[k] := fun i j => ⟨(1 + E) i j, hI i j⟩
  have hres : (IsLocalRing.residue 𝒪[k]).mapMatrix M = 1 := by
    ext i j
    simp only [RingHom.mapMatrix_apply, map_apply]
    have : M i j - (1 : Matrix n n 𝒪[k]) i j = ⟨E i j, hEI i j⟩ := by
      apply Subtype.ext
      by_cases h : i = j <;> simp [M, Matrix.one_apply, h]
    have hm : M i j - (1 : Matrix n n 𝒪[k]) i j ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
      rw [this, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one]
      exact hE i j
    have e2 : (IsLocalRing.residue 𝒪[k]) (M i j) = (IsLocalRing.residue 𝒪[k]) ((1 : Matrix n n 𝒪[k]) i j) := by
      rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]; exact hm
    rw [e2]; by_cases h : i = j <;> simp [Matrix.one_apply, h]
  have hdet : IsUnit M.det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, hres, det_one]
    exact one_ne_zero
  refine ⟨(algebraMap 𝒪[k] k).mapMatrix M⁻¹, fun i j => (M⁻¹ i j).2, ?_⟩
  have hM : (algebraMap 𝒪[k] k).mapMatrix M = 1 + E := rfl
  rw [← hM, ← map_mul, Matrix.mul_nonsing_inv M hdet, map_one]

end GlobalTheory.RankCoinv.Nbhd

namespace GlobalTheory.RankCoinv.Nbhd
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]

theorem inv_mul_mem_box_iff {g : GL A k} (hg : g ∈ KO k A) (ϖ : kˣ) (C X : Matrix A D k) (m : ℕ) :
    (g⁻¹).val * X ∈ box ϖ C (fun _ => m) ↔ X ∈ box ϖ (g.val * C) (fun _ => m) := by
  obtain ⟨h1, h2⟩ := (mem_KO_iff g).1 hg
  have h1' : ∀ i a, valuation k (g.val i a) ≤ 1 := fun i a => (Valuation.mem_integer_iff _ _).1 (h1 i a)
  have h2' : ∀ i a, valuation k ((g⁻¹).val i a) ≤ 1 := fun i a => (Valuation.mem_integer_iff _ _).1 (h2 i a)
  simp only [box, Set.mem_setOf_eq]
  constructor
  · intro hZ i j
    have e : X i j - (g.val * C) i j = (g.val * ((g⁻¹).val * X - C)) i j := by
      rw [Matrix.mul_sub, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.sub_apply]
    rw [e]
    exact (val_mul_le (valuation k) h1' (fun a j => by rw [Matrix.sub_apply]; exact hZ a j) i j).trans_eq (one_mul _)
  · intro hZ i j
    have e : ((g⁻¹).val * X) i j - C i j = ((g⁻¹).val * (X - g.val * C)) i j := by
      rw [Matrix.mul_sub, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.sub_apply]
    rw [e]
    exact (val_mul_le (valuation k) h2' (fun a j => by rw [Matrix.sub_apply]; exact hZ a j) i j).trans_eq (one_mul _)

theorem omA_boxFn {g : GL A k} (hg : g ∈ KO k A) (ν β : kˣ →* ℂˣ) (ϖ : kˣ) (C : Matrix A D k) (m : ℕ) :
    ∃ s : ℂ, omA ν β g 1 (boxFn ϖ C (fun _ => m)) = s • boxFn ϖ (g.val * C) (fun _ => m) := by
  refine ⟨(((ν (gdet g))⁻¹ : ℂˣ) : ℂ) * apow (gdet g) (-(Fintype.card D : ℂ) / 2), funext fun X => ?_⟩
  rw [omA_one_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  by_cases h : X ∈ box ϖ (g.val * C) (fun _ => m)
  · simp only [boxFn]
    rw [Set.indicator_of_mem h, Set.indicator_of_mem ((inv_mul_mem_box_iff hg ϖ C X m).2 h)]
    rfl
  · simp only [boxFn]
    rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h ((inv_mul_mem_box_iff hg ϖ C X m).1 h'))]

end GlobalTheory.RankCoinv.Nbhd


open GlobalTheory.RankCoinv.Nbhd GlobalTheory.SplitFlip GlobalTheory.SplitWeil in
theorem GlobalTheory.RankCoinv.exists_boxFn_mem_lowRank_sup_twistSpan : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (ν β : kˣ →* ℂˣ), (∀ x, ‖(ν x : ℂ)‖ = 1) → ν ϖ ≠ 1 → ∀ (r : ℕ) (X₀ : Matrix A D k), X₀.rank = r → r < Fintype.card A → ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ C ∈ GlobalTheory.RankCoinv.box ϖ X₀ (fun _ => m₀), GlobalTheory.RankCoinv.boxFn ϖ C (fun _ => m) ∈ GlobalTheory.RankCoinv.lowRank (r + 1) ⊔ GlobalTheory.RankCoinv.twistSpan ν β := by
  intro k _ _ _ _ A D _ _ _ _ ϖ hϖ ν β hν hνϖ r X₀ hrank hr
  obtain ⟨g, hg, i₀, hi₀⟩ := GlobalTheory.T.rank_deficient_integral_row_reduction k A D X₀ (hrank ▸ hr)
  have hgint := (GlobalTheory.SplitFlip.mem_KO_iff g).1 hg
  have hg1 : ∀ i a, valuation k (g.val i a) ≤ 1 := fun i a => (Valuation.mem_integer_iff _ _).1 (hgint.1 i a)
  have hYr : (g.val * X₀).rank = r := by
    rw [← hrank]
    exact Matrix.rank_mul_eq_right_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit)
  obtain ⟨H₁, Q₁, hHQ⟩ : ∃ (H₁ : Matrix (Fin r) A k) (Q₁ : Matrix D (Fin r) k), H₁ * (g.val * X₀) * Q₁ = 1 := by
    rw [← hYr]; exact GlobalTheory.T.matrix_rank_normal_form k A D _
  let H₂ : Matrix (Fin r) A k := Matrix.of fun l i => if i = i₀ then 0 else H₁ l i
  have hH₂Y : H₂ * (g.val * X₀) = H₁ * (g.val * X₀) := by
    ext l j
    rw [Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [H₂, Matrix.of_apply]
    split_ifs with h
    · rw [h, hi₀ j, zero_mul, mul_zero]
    · rfl
  obtain ⟨h, Q₀, hhY, hQ₀, hhYQ⟩ := GlobalTheory.T.integral_right_inverse_normalization k D r (H₂ * (g.val * X₀)) Q₁ (by rw [hH₂Y, hHQ])
  let H := h * H₂
  have hHi₀ : ∀ l, H l i₀ = 0 := fun l => by simp [H, H₂, Matrix.mul_apply]
  obtain ⟨c, hc⟩ := exists_bound hϖ H
  refine ⟨c + 1, fun m hm C hC => ?_⟩
  have hϖ0 : valuation k (ϖ : k) ≠ 0 := by simp
  have hϖlt : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  have hCX : ∀ a j, valuation k ((C - X₀) a j) ≤ valuation k (ϖ : k) ^ (c + 1) := fun a j => by
    rw [Matrix.sub_apply]; simpa using hC a j
  have hgCX : ∀ i j, valuation k ((g.val * (C - X₀)) i j) ≤ valuation k (ϖ : k) ^ (c + 1) := fun i j => by
    simpa using val_mul_le (valuation k) hg1 hCX i j
  have hc' : ∀ l i, valuation k (H l i) ≤ (valuation k (ϖ : k))⁻¹ ^ c := fun l i => by
    rw [← valuation_inv_pow]; exact hc l i
  have hprod : (valuation k (ϖ : k))⁻¹ ^ c * valuation k (ϖ : k) ^ (c + 1) = valuation k (ϖ : k) := by
    rw [inv_pow, pow_succ, inv_mul_cancel_left₀ (pow_ne_zero _ hϖ0)]
  have hEb : ∀ l j, valuation k ((H * (g.val * (C - X₀))) l j) ≤ valuation k (ϖ : k) := fun l j => by
    rw [← hprod]; exact val_mul_le (valuation k) hc' hgCX l j
  have hsplit : g.val * C = g.val * X₀ + g.val * (C - X₀) := by rw [Matrix.mul_sub]; abel
  have hHY : H * (g.val * X₀) = h * (H₂ * (g.val * X₀)) := Matrix.mul_assoc _ _ _
  have hHC : H * (g.val * C) = H * (g.val * X₀) + H * (g.val * (C - X₀)) := by rw [hsplit, Matrix.mul_add]
  have hHCint : ∀ l j, (H * (g.val * C)) l j ∈ 𝒪[k] := fun l j => by
    rw [hHC, Valuation.mem_integer_iff, Matrix.add_apply]
    refine Valuation.map_add_le _ ?_ ((hEb l j).trans hϖlt.le)
    rw [hHY]; exact hhY l j
  have hQ₀' : ∀ j l, valuation k (Q₀ j l) ≤ 1 := fun j l => (Valuation.mem_integer_iff _ _).1 (hQ₀ j l)
  set E := H * (g.val * (C - X₀)) * Q₀ with hE
  have hEv : ∀ i j, valuation k (E i j) < 1 := fun i j =>
    lt_of_le_of_lt (by simpa using val_mul_le (valuation k) hEb hQ₀' i j) hϖlt
  have hHCQ : H * (g.val * C) * Q₀ = 1 + E := by
    rw [hHC, Matrix.add_mul, hHY, hhYQ]
  obtain ⟨N, hN, hN1⟩ := exists_int_inv_one_add E hEv
  have hN' : ∀ i j, valuation k (N i j) ≤ 1 := fun i j => (Valuation.mem_integer_iff _ _).1 (hN i j)
  have hQint : ∀ j l, (Q₀ * N) j l ∈ 𝒪[k] := fun j l => by
    rw [Valuation.mem_integer_iff]; simpa using val_mul_le (valuation k) hQ₀' hN' j l
  have hHCQ' : H * (g.val * C) * (Q₀ * N) = 1 := by rw [← Matrix.mul_assoc, hHCQ, hN1]
  have hrow : ∀ j, valuation k ((g.val * C) i₀ j) ≤ valuation k ((ϖ ^ (c + 1) : kˣ) : k) := fun j => by
    rw [hsplit, Matrix.add_apply, hi₀ j, zero_add]; simpa using hgCX i₀ j
  have hmem := GlobalTheory.T.box_function_twisted_coinvariant_rank k A D ϖ hϖ ν β hν hνϖ i₀ r c m (g.val * C) H (Q₀ * N) hHi₀ hc (by omega)
    hHCint hQint hHCQ' hrow
  obtain ⟨s, hs⟩ := omA_boxFn hg ν β ϖ C m
  have hΦ := boxFn_mem_SB ϖ C (fun _ => m)
  have h1 : omA ν β g 1 (boxFn ϖ C (fun _ => m)) ∈ lowRank (r + 1) ⊔ twistSpan ν β := by
    rw [hs]; exact Submodule.smul_mem _ _ hmem
  have h2 : omA ν β g 1 (boxFn ϖ C (fun _ => m)) - boxFn ϖ C (fun _ => m) ∈ lowRank (r + 1) ⊔ twistSpan ν β :=
    Submodule.mem_sup_right (sub_mem_twistSpan ν β g hΦ)
  simpa using sub_mem h1 h2
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.GmStep

noncomputable section

namespace GlobalTheory.EtC.GmStep.DegRow

variable {R : Type} [CommRing R] (F : Shv R)

theorem cobd_disc (P : PSh) (s : (free R).obj ((disc.obj P).obj (op ⦋0⦌)) ⟶ F) :
    cobd (E := disc.obj P) s = 0 := by
  simp [cobd, Fin.sum_univ_two, SimplicialObject.δ]

theorem exists_rep (E : Spc) (x : H R E F 0) : ∃ s : (free R).obj (E.obj (op ⦋0⦌)) ⟶ F, IsCls s x := by
  obtain ⟨-, hneg, hmono, ⟨w, hex⟩, -, hpos⟩ := GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_basic_properties R F
  obtain ⟨z, rfl⟩ := x.mk_surjective
  let b := (z.1 : Cochain ((chains R).obj E) (res R F) 0).v 0 0 (add_zero 0)
  have hb : b ≫ (res R F).d 0 1 = 0 := by
    have e := Cochain.congr_v (Cocycle.δ_eq_zero z 1) 0 1 (zero_add 1)
    rw [δ_v 0 1 (zero_add 1) _ 0 1 (zero_add 1) 0 1 (by omega) (zero_add 1),
      (hpos E 1 one_pos).eq_of_tgt (((chains R).obj E).d 0 1) 0, zero_comp, smul_zero, add_zero] at e
    exact e
  haveI : Mono (ShortComplex.mk _ _ w).f := hmono
  let t' : ((chains R).obj E).X 0 ⟶ F := hex.lift b hb
  have ht' : t' ≫ resι R F = b := hex.lift_f b hb
  refine ⟨(chainsXIso R E 0).inv ≫ t', z, rfl, ?_⟩
  refine Cochain.ext _ _ (fun p q hpq => ?_)
  by_cases hp : p = 0
  · subst hp
    obtain rfl : q = 0 := by omega
    change b = (Cochain.single (p := -((0 : ℕ) : ℤ)) (q := 0) ((chainsXIso R E 0).hom ≫ ((chainsXIso R E 0).inv ≫ t') ≫ resι R F) ((0 : ℕ) : ℤ)).v (-((0 : ℕ) : ℤ)) 0 (by simp)
    rw [Cochain.single_v, ← ht']
    simp
  · rcases lt_or_gt_of_ne hp with hp | hp
    · exact (hneg q (by omega)).eq_of_tgt _ _
    · exact (hpos E p hp).eq_of_src _ _

def clsFun (P : PSh) (s : (free R).obj P ⟶ F) : H R (disc.obj P) F 0 :=
  Classical.choose ((isCls_basic R F (disc.obj P) 0).1 s (cobd_disc F P s))

theorem clsFun_spec (P : PSh) (s : (free R).obj P ⟶ F) : IsCls (E := disc.obj P) (n := 0) s (clsFun F P s) :=
  Classical.choose_spec ((isCls_basic R F (disc.obj P) 0).1 s (cobd_disc F P s))

theorem clsFun_eq (P : PSh) (s : (free R).obj P ⟶ F) (x : H R (disc.obj P) F 0)
    (h : IsCls (E := disc.obj P) (n := 0) s x) : clsFun F P s = x :=
  (isCls_basic R F (disc.obj P) 0).2.2.1 s _ _ (clsFun_spec F P s) h

def cls0 (P : PSh) : ((free R).obj P ⟶ F) →+ H R (disc.obj P) F 0 :=
  AddMonoidHom.mk' (clsFun F P) fun s s' =>
    clsFun_eq F P (s + s') _ ((isCls_basic R F (disc.obj P) 0).2.1 s s' _ _ (clsFun_spec F P s) (clsFun_spec F P s'))

theorem degreeZeroClassConstantSpaceAddHom_represents (P : PSh) (s : (free R).obj P ⟶ F) : IsCls (E := disc.obj P) (n := 0) s (cls0 F P s) :=
  clsFun_spec F P s

theorem degreeZeroClassConstantSpaceAddHom_eq_of_represents (P : PSh) (s : (free R).obj P ⟶ F) (x : H R (disc.obj P) F 0)
    (h : IsCls (E := disc.obj P) (n := 0) s x) : cls0 F P s = x :=
  clsFun_eq F P s x h

theorem etaleSpaceCohomologyPullback_degreeZeroClass {P P' : PSh} (f : P ⟶ P') (s : (free R).obj P' ⟶ F) :
    pull R (disc.map f) F 0 (cls0 F P' s) = cls0 F P ((free R).map f ≫ s) :=
  (degreeZeroClassConstantSpaceAddHom_eq_of_represents F P _ _ ((isCls_basic R F (disc.obj P') 0).2.2.2.2 (disc.obj P) (disc.map f) s _ (degreeZeroClassConstantSpaceAddHom_represents F P' s))).symm

theorem degreeZeroClassConstantSpaceAddHom_eq_zero_imp (P : PSh) (s : (free R).obj P ⟶ F) (h : cls0 F P s = 0) : s = 0 :=
  (leray_inj R F (disc.obj P) 0 (fun k m hm hkm _ => by omega)).1 s (h ▸ degreeZeroClassConstantSpaceAddHom_represents F P s)

theorem simplicialSpectralRowDifferential_degreeZeroClass (E : Spc) (p : ℕ) (s : (free R).obj (E.obj (op ⦋p⦌)) ⟶ F) :
    rowD R E F 0 p (cls0 F _ s) = cls0 F _ (cobd s) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [rowD, cobd, map_sum, map_zsmul]
    change (AddMonoidHom.eval (cls0 F _ s)) (∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) • pull R (disc.map (E.δ j)) F 0) = _
    rw [map_sum]
    change (∑ j : Fin (p + 2), (((-1 : ℤ) ^ (j : ℕ)) • pull R (disc.map (E.δ j)) F 0) (cls0 F _ s)) = _
    simp only [AddMonoidHom.smul_apply, etaleSpaceCohomologyPullback_degreeZeroClass]

end GlobalTheory.EtC.GmStep.DegRow


open GlobalTheory.EtC.GmStep.DegRow in
theorem GlobalTheory.EtC.GmStep.rowExact_zero_of_acyclic : ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc),
    (∀ (p : ℕ) (s : ℤ), 0 < s → Subsingleton (H R (disc.obj (E.obj (op ⦋p⦌))) F s)) →
    (∀ m : ℤ, 0 < m → Subsingleton (H R E F m)) → ∀ p : ℕ, RowExact R E F 0 p := by
  intro R _ F E hlev htot p y hy
  obtain ⟨s, hs⟩ : ∃ s : (free R).obj (E.obj (op ⦋p + 1⦌)) ⟶ F, IsCls (E := disc.obj (E.obj (op ⦋p + 1⦌))) (n := 0) s y :=
    exists_rep F (disc.obj (E.obj (op ⦋p + 1⦌))) y
  obtain rfl : cls0 F (E.obj (op ⦋p + 1⦌)) s = y := degreeZeroClassConstantSpaceAddHom_eq_of_represents F _ s y hs
  rw [simplicialSpectralRowDifferential_degreeZeroClass] at hy
  have hc : cobd s = 0 := degreeZeroClassConstantSpaceAddHom_eq_zero_imp F _ _ hy
  obtain ⟨x, hx⟩ := (isCls_basic R F E (p + 1)).1 s hc
  have hx0 : x = 0 := @Subsingleton.elim _ (htot _ (by positivity)) x 0
  rw [hx0] at hx
  obtain ⟨t, ht⟩ := (leray_inj R F E p (fun k m hm _ y => @Subsingleton.elim _ (hlev k m (by exact_mod_cast hm)) y 0)).2 s hx
  exact ⟨cls0 F _ t, by rw [simplicialSpectralRowDifferential_degreeZeroClass, ht]⟩

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.exists_descent_hom_quotient_galois_group_scheme : ∀ (S : Scheme.{0}) (A A' B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] [GrpObj B] (H : Subgroup (𝟙_ (Over S) ⟶ A)) (ψ : A ⟶ A'), IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover H (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left → ∀ f : A ⟶ B, IsMonHom f → (∀ h ∈ H, h ≫ f = 1) → ∃ f' : A' ⟶ B, IsMonHom f' ∧ ψ ≫ f' = f := by
  first | exact @GlobalTheory.HomDescent.exists_desc | exact GlobalTheory.HomDescent.exists_desc | (intros; apply GlobalTheory.HomDescent.exists_desc; all_goals assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieLin

theorem _root_.GlobalTheory.T.exists_ideal_geometric_rank_iff_of_lie_condition : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (B : Type) [CommRing B]
  (βB : R →+* B) (n : ℕ) (M : 𝓞 D.F →+* Matrix (Fin n) (Fin n) B),
    ∃ K₂ : Ideal B, ∀ (T : Type) [CommRing T] (f : B →+* T), lieIdeal b βB M ≤ RingHom.ker f →
      ((∀ (k : Type) [Field k] [IsAlgClosed k] (h : T →+* k) (i : Fin D.a),
          Module.finrank k (eigSub (matAct M (h.comp f)) ((h.comp (f.comp βB)).comp (b.t i))) = D.m) ↔
        K₂ ≤ RingHom.ker f) := by
  first | (exact @GlobalTheory.UPel.HT.LieLin.RankIdeal.exists_ideal_rank_iff) | (exact GlobalTheory.UPel.HT.LieLin.RankIdeal.exists_ideal_rank_iff) | (intros; apply GlobalTheory.UPel.HT.LieLin.RankIdeal.exists_ideal_rank_iff  <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors

theorem _root_.GlobalTheory.T.hasFDerivAt_weightTwoDerivativeEisensteinTerm : ∀ (E : Type) [Field E] [NumberField E] (I : Type) [Fintype I] [DecidableEq I] (φ : I → E →+* ℂ) (m : I → ℕ) (σ : ℂ) (x : E), x ≠ 0 → ∀ z ∈ polydisc I, HasFDerivAt (𝕜 := ℝ) (fun w : I → ℂ => eTerm φ m σ w x) (∑ j, (eTerm φ (m + Pi.single j 1) σ z x • dz j + (eTerm φ m σ z x * (-σ * φ j x / starRingEnd ℂ (defCoord φ z x j))) • dzbar j)) z := by
  first | exact @GlobalTheory.WeightTwoSum.hasFDerivAt_eTerm | exact GlobalTheory.WeightTwoSum.hasFDerivAt_eTerm | (intros; apply GlobalTheory.WeightTwoSum.hasFDerivAt_eTerm <;> assumption)
end
