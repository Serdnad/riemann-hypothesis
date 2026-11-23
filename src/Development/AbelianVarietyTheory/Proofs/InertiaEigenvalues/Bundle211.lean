module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle007
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle001
public import GroundTheory.LocalFields.ExistsUnitFiltrationUnitsLeAndRangePowLe
public import GroundTheory.LocalFields.UnramifiedHensel
public import GroundTheory.LocalFields.HerbrandFunction
public import GroundTheory.LocalFields.Bundle006
public import GroundTheory.LocalFields.IntermediateField
public import Mathlib.RingTheory.Trace.Defs
import Mathlib.Algebra.Module.StablyFree.Basic
public import GroundTheory.LocalFields.Eisenstein
public import GroundTheory.LocalFields.Bundle007
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Order.Interval.Finset.Box
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
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram


open Classical in
theorem jumpSum_mono_of_le :
    ∀ (G : Type) [Group G] (R : ℕ → Subgroup G) (A B C : Subgroup G), Antitone R → (∃ m, R m = ⊥) →
      (∀ t, A ⊓ R t ≤ C → A ⊓ R t ≤ B) → jumpSum R A B ≤ jumpSum R A C := by
  intro G _ R A B C hR ⟨m, hm⟩ hBC
  have hbot : ∀ t, m ≤ t → ∀ D : Subgroup G, A ⊓ R t ≤ D := by
    intro t ht D
    have : R t ≤ ⊥ := hm ▸ hR ht
    exact le_trans inf_le_right (le_trans this bot_le)
  have hfin : ∀ D : Subgroup G,
      (Function.support fun t : ℕ => if A ⊓ R t ≤ D then 0 else Nat.card ↥(A ⊓ R t)) ⊆ ↑(Finset.range m) := by
    intro D
    intro t ht
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    apply ht
    simp [hbot t (not_lt.mp h) D]
  unfold jumpSum
  rw [finsum_eq_sum_of_support_subset _ (hfin B), finsum_eq_sum_of_support_subset _ (hfin C)]
  apply Finset.sum_le_sum
  intro t _
  by_cases hC : A ⊓ R t ≤ C
  · simp [hBC t hC]
  · rw [if_neg hC]
    split_ifs <;> simp

end GlobalTheory.PMon.Ram
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

set_option backward.proofsInPublic true in
theorem jumpSum_support_subset {G : Type} [Group G] (R : ℕ → Subgroup G) (A B : Subgroup G) (hR : Antitone R)
    (m : ℕ) (hm : R m = ⊥) :
    Function.support (fun t : ℕ => by classical exact if A ⊓ R t ≤ B then 0 else Nat.card ↥(A ⊓ R t)) ⊆
      ↑(Finset.range m) := by
  classical
  intro t ht
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra h
  push_neg at h
  apply ht
  have h1 : R t = ⊥ := le_bot_iff.mp (hm ▸ hR h)
  simp [h1]

theorem jumpSum_le_add : ∀ (G : Type) [Group G] (R : ℕ → Subgroup G) (A B C : Subgroup G), Antitone R →
    (∃ m, R m = ⊥) → B ≤ A → jumpSum R A C ≤ jumpSum R A B + jumpSum R B C := by
  intro G _ R A B C hR ⟨m, hm⟩ hBA
  classical
  unfold jumpSum
  rw [finsum_eq_sum_of_support_subset _ (jumpSum_support_subset R A C hR m hm),
    finsum_eq_sum_of_support_subset _ (jumpSum_support_subset R A B hR m hm),
    finsum_eq_sum_of_support_subset _ (jumpSum_support_subset R B C hR m hm),
    ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro t _
  by_cases hC : A ⊓ R t ≤ C
  · simp [hC]
  · by_cases hB : A ⊓ R t ≤ B
    · have heq : B ⊓ R t = A ⊓ R t :=
        le_antisymm (inf_le_inf_right _ hBA) (le_inf hB inf_le_right)
      have hC' : ¬ B ⊓ R t ≤ C := by rw [heq]; exact hC
      simp [hC, hC', heq]
    · simp [hC, hB]

end GlobalTheory.PMon.Ram
end

section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer

theorem map_pw_eq_pw (l : ℕ) [Fact l.Prime] (F : Type) [NormedField F] [CharP F l] [PerfectRing F l]
    (ι : Fl l →+* F) (k : ℤ) (x : Fl l) : ι (GlobalTheory.PSer.pw k x) = GlobalTheory.PMonE.pw l k (ι x) := by
  have hsymm : ∀ y : Fl l, ι ((frobeniusEquiv (Fl l) l).symm y) = (frobeniusEquiv F l).symm (ι y) :=
    fun y => RingHom.map_frobeniusEquiv_symm l ι y
  have hit : ∀ (n : ℕ) (y : Fl l), ι (((frobeniusEquiv (Fl l) l).symm)^[n] y) = ((frobeniusEquiv F l).symm)^[n] (ι y) := by
    intro n
    induction n with
    | zero => intro y; rfl
    | succ n ih => intro y; rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hsymm, ih]
  have hpos : ∀ (n : ℕ) (y : Fl l), ((frobeniusEquiv (Fl l) l : RingAut (Fl l)) ^ n) y = y ^ l ^ n := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ n ih =>
      intro y
      rw [pow_succ']
      change (frobeniusEquiv (Fl l) l) (((frobeniusEquiv (Fl l) l : RingAut (Fl l)) ^ n) y) = _
      rw [ih, frobeniusEquiv_apply, frobenius_def, ← pow_mul, pow_succ]
  have hneg : ∀ (n : ℕ) (y : Fl l), ((frobeniusEquiv (Fl l) l : RingAut (Fl l)) ^ (-(n : ℤ))) y
      = ((frobeniusEquiv (Fl l) l).symm)^[n] y := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ n ih =>
      intro y
      rw [Nat.cast_succ, neg_add, zpow_add, Function.iterate_succ_apply]
      change ((frobeniusEquiv (Fl l) l : RingAut (Fl l)) ^ (-(n : ℤ)))
        (((frobeniusEquiv (Fl l) l : RingAut (Fl l)) ^ (-1 : ℤ)) y) = _
      rw [ih, zpow_neg_one]
      rfl
  cases k with
  | ofNat n =>
    simp only [GlobalTheory.PSer.pw, GlobalTheory.PMonE.pw, Int.ofNat_eq_coe, zpow_natCast, hpos, map_pow]
    simp
  | negSucc n =>
    have hk : Int.negSucc n = -((n + 1 : ℕ) : ℤ) := rfl
    simp only [GlobalTheory.PSer.pw, GlobalTheory.PMonE.pw]
    rw [if_neg (by omega), hk, hneg, hit]
    congr

end GlobalTheory.PSer
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem exists_one_add_pow_eq {R : Type*} [CommRing R] (y : R) (k : ℕ) :
    ∃ w : R, (1 + y) ^ k = 1 + (k : R) * y + y ^ 2 * w := by
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨w, hw⟩ := ih
    refine ⟨(1 + y) * w + k, ?_⟩
    rw [pow_succ, hw]; push_cast; ring

theorem one_add_pow_sub_one_mem {R : Type*} [CommRing R] (I : Ideal R) {n e k : ℕ} {y : R}
    (hy : y ∈ I ^ n) (hk : (k : R) ∈ I ^ e) :
    (1 + y) ^ k - 1 ∈ I ^ min (2 * n) (n + e) := by
  obtain ⟨w, hw⟩ := exists_one_add_pow_eq y k
  have h : (1 + y) ^ k - 1 = (k : R) * y + y ^ 2 * w := by rw [hw]; ring
  rw [h]
  refine Ideal.add_mem _ ?_ ?_
  · refine Ideal.pow_le_pow_right (min_le_right _ _) ?_
    rw [add_comm n e, pow_add]
    exact Ideal.mul_mem_mul hk hy
  · refine Ideal.pow_le_pow_right (min_le_left _ _) ?_
    refine Ideal.mul_mem_right _ _ ?_
    rw [two_mul, pow_add, pow_two]
    exact Ideal.mul_mem_mul hy hy

theorem natCast_mem_maximalIdeal_pow_of_ordIs {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {p e : ℕ} (h : OrdIs F p e) : (p : 𝒪[F]) ∈ 𝓂[F] ^ e := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    ← IsDiscreteValuationRing.addVal_le_iff_dvd, IsDiscreteValuationRing.addVal_pow,
    IsDiscreteValuationRing.addVal_uniformizer hϖ]
  rw [OrdIs] at h
  rw [h]
  simp

theorem pow_mem_unitFiltrationUnits (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (p e n : ℕ) (hp : OrdIs F p e) :
    ∀ x ∈ unitFiltrationUnits F n, x ^ p ∈ unitFiltrationUnits F (min (2 * n) (n + e)) := by
  rintro _ ⟨u, hu, rfl⟩
  refine ⟨u ^ p, ?_, by simp⟩
  rw [SetLike.mem_coe, mem_unitFiltration] at hu ⊢
  have := one_add_pow_sub_one_mem (𝓂[F]) hu (natCast_mem_maximalIdeal_pow_of_ordIs hp)
  simpa using this

end GlobalTheory.PMon.Ram

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem card_mul_herbrandPhi_natCast_of_totallyRamified (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] :
    lowerRamificationGroup F L 0 = ⊤ → ∀ a : ℕ, (Nat.card (L ≃ₐ[F] L) : ℝ) * herbrandPhi F L a =
      ((∑ t ∈ Finset.range a, Nat.card ↥(wild F L t) : ℕ) : ℝ) := by
  intro h0 a
  induction a with
  | zero => simp
  | succ n ih =>
    have hstep := herbrandPhi_of_mem_Icc (K := F) (L := L) n (u := ((n : ℝ) + 1))
      ⟨by linarith, le_refl _⟩
    have hidx : (lowerRamificationGroup F L ((n : ℤ) + 1)).relIndex (lowerRamificationGroup F L 0) *
        Nat.card ↥(wild F L n) = Nat.card (L ≃ₐ[F] L) := by
      rw [h0, Subgroup.relIndex_top_right, wild, Subgroup.index_mul_card]
    have hpos : (0 : ℝ) < ((lowerRamificationGroup F L ((n : ℤ) + 1)).relIndex
        (lowerRamificationGroup F L 0) : ℝ) := relIndex_pos_of_finite _ _
    have hidxR : (((lowerRamificationGroup F L ((n : ℤ) + 1)).relIndex
        (lowerRamificationGroup F L 0) : ℕ) : ℝ) * (Nat.card ↥(wild F L n) : ℝ) =
        (Nat.card (L ≃ₐ[F] L) : ℝ) := by exact_mod_cast hidx
    push_cast [Finset.sum_range_succ] at ih ⊢
    rw [hstep, ← ih, ← hidxR]
    field_simp
    ring

end GlobalTheory.PMon.Ram
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem ringChar_residue_eq_of_ordIs (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (p e : ℕ) (hp : p.Prime) (he : 0 < e) (h : OrdIs F p e) :
    ringChar 𝓀[F] = p := by
  have hnu : ¬ IsUnit (p : 𝒪[F]) := by
    intro hu
    have := (IsDiscreteValuationRing.addVal_eq_zero_of_unit (hu.unit))
    unfold OrdIs at h
    simp at this
    rw [this] at h
    norm_cast at h
    omega
  have hm : (p : 𝒪[F]) ∈ IsLocalRing.maximalIdeal 𝒪[F] := hnu
  have h0 : ((p : ℕ) : 𝓀[F]) = 0 := by
    rw [← map_natCast (IsLocalRing.residue 𝒪[F]), IsLocalRing.residue_eq_zero_iff]
    exact hm
  have hd : ringChar 𝓀[F] ∣ p := (ringChar.spec 𝓀[F] p).mp h0
  rcases (Nat.dvd_prime hp).mp hd with h1 | h1
  · exact absurd h1 CharP.ringChar_ne_one
  · exact h1

theorem upperRamificationGroup_one_eq_top_of_exponent :
    ∀ (F M : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field M]
      [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M] [Algebra F M] [ValuativeExtension F M]
      [FiniteDimensional F M] [IsGalois F M] (p e : ℕ), p.Prime → 0 < e → OrdIs F p e →
      upperRamificationGroup F M 0 = ⊤ → (∀ σ : M ≃ₐ[F] M, σ ^ p = 1) → upperRamificationGroup F M 1 = ⊤ := by
  intro F M _ _ _ _ _ _ _ _ _ _ _ _ p e hp he hord h0 hexp
  rw [upperRamificationGroup_zero] at h0
  have hchar := ringChar_residue_eq_of_ordIs F p e hp he hord
  have hcop := coprime_card_lowerRamificationGroup_zero_quotient F M
  rw [hchar] at hcop
  have h1 : lowerRamificationGroup F M 1 = ⊤ := by
    rw [eq_top_iff]
    intro σ _
    have hσ0 : σ ∈ lowerRamificationGroup F M 0 := by rw [h0]; trivial
    set q : lowerRamificationGroup F M 0 ⧸
        (lowerRamificationGroup F M 1).subgroupOf (lowerRamificationGroup F M 0) :=
      QuotientGroup.mk ⟨σ, hσ0⟩ with hq
    have hqp : q ^ p = 1 := by
      rw [hq, ← QuotientGroup.mk_pow]
      have : (⟨σ, hσ0⟩ : lowerRamificationGroup F M 0) ^ p = 1 := Subtype.ext (by simpa using hexp σ)
      rw [this, QuotientGroup.mk_one]
    have hqc : q ^ Nat.card (lowerRamificationGroup F M 0 ⧸
        (lowerRamificationGroup F M 1).subgroupOf (lowerRamificationGroup F M 0)) = 1 := pow_card_eq_one'
    have hg : q ^ Nat.gcd _ p = 1 := pow_gcd_eq_one.mpr ⟨hqc, hqp⟩
    rw [hcop, pow_one, hq, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hg
    exact hg
  have hphi0 : herbrandPhi F M 0 = 0 := by simp [herbrandPhi]
  have hphi1 : herbrandPhi F M 1 = 1 := by
    have := herbrandPhi_of_mem_Icc (K := F) (L := M) 0 (u := 1) (by norm_num)
    have h1' : lowerRamificationGroup F M (((0 : ℕ) : ℤ) + 1) = ⊤ := by simpa using h1
    rw [h1', Subgroup.relIndex_top_left] at this
    simpa [hphi0] using this
  rw [← hphi1, upperRamificationGroup_herbrandPhi, ← Nat.cast_one, lowerRamificationGroupReal_natCast]
  simpa using h1
end GlobalTheory.PMon.Ram
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

theorem GlobalTheory.PMon.Ram.exists_integer_fixedField_trace_eq : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (p r : ℕ) (x : L) (a : (L ≃ₐ[F] L) → ℤ) (J : Subgroup (L ≃ₐ[F] L)) [J.Normal] (σ₁ : L ≃ₐ[F] L) (c : ℤ), (p : L) ≠ 0 → AxIn F L p → (∀ σ : L ≃ₐ[F] L, ∃ z ∈ 𝒪[L], σ x - x = (a σ : L) + (p : L) ^ r * z) → (∀ σ ∈ J, (p : ℤ) ^ r ∣ a σ) → c * (p : ℤ) ^ r = (J.index : ℤ) * a σ₁ → ∃ z : 𝒪[↥(IntermediateField.fixedField J)], Algebra.trace F ↥(IntermediateField.fixedField J) (z : ↥(IntermediateField.fixedField J)) = (p : F) ^ 2 * (c : F) := by
  intro F L _ _ _ _ _ _ _ _ _ _ _ _ p r x a J _ σ₁ c hp hAx hx hJ hc
  set M := IntermediateField.fixedField J with hMdef
  have hpr : (p : L) ^ r ≠ 0 := pow_ne_zero _ hp
  have hint : ∀ n : ℤ, (n : L) ∈ 𝒪[L] := fun n => intCast_mem _ n
  have hσO : ∀ (σ : L ≃ₐ[F] L) (w : L), w ∈ 𝒪[L] → σ w ∈ 𝒪[L] := by
    intro σ w hw
    rw [Valuation.mem_integer_iff] at hw ⊢
    rwa [valuation_algEquiv_apply F L σ w]
  have hdiff : ∀ σ : L ≃ₐ[F] L, σ (x / (p : L) ^ r) - x / (p : L) ^ r = (σ x - x) / (p : L) ^ r := by
    intro σ
    rw [map_div₀, map_pow, map_natCast, sub_div]

  have hJint : ∀ σ ∈ J, σ (x / (p : L) ^ r) - x / (p : L) ^ r ∈ 𝒪[L] := by
    intro σ hσ
    obtain ⟨z, hz, e⟩ := hx σ
    obtain ⟨k, hk⟩ := hJ σ hσ
    rw [hdiff, e, hk]
    have : (((p : ℤ) ^ r * k : ℤ) : L) + (p : L) ^ r * z = (p : L) ^ r * ((k : L) + z) := by
      push_cast; ring
    rw [this, mul_div_cancel_left₀ _ hpr]
    exact add_mem (hint k) hz
  obtain ⟨y, hyJ, hw⟩ := hAx J (x / (p : L) ^ r) hJint
  obtain ⟨z₁, hz₁, e₁⟩ := hx σ₁
  have hyM : y ∈ M := (IntermediateField.mem_fixedField_iff J y).2 hyJ
  set yM : M := ⟨y, hyM⟩
  set sM : M := σ₁.restrictNormal M yM
  have hsM : (sM : L) = σ₁ y := AlgEquiv.restrictNormal_commutes σ₁ M yM
  have hpF : (p : F) ^ r ≠ 0 := by
    intro h; apply hpr
    have := congrArg (algebraMap F L) h
    simpa using this
  set kF : F := (a σ₁ : F) / (p : F) ^ r
  set zM : M := (p : M) ^ 2 * (algebraMap F M kF - (sM - yM))
  have hzL : (zM : L) = σ₁ ((p : L) ^ 2 * (x / (p : L) ^ r - y)) - (p : L) ^ 2 * (x / (p : L) ^ r - y)
      - (p : L) ^ 2 * z₁ := by
    have h1 : (algebraMap F L kF) = (a σ₁ : L) / (p : L) ^ r := by
      simp [kF]
    have h2 : σ₁ (x / (p : L) ^ r) = x / (p : L) ^ r + (a σ₁ : L) / (p : L) ^ r + z₁ := by
      have := hdiff σ₁
      rw [e₁, add_div, mul_div_cancel_left₀ _ hpr] at this
      linear_combination this
    have h3 : (zM : L) = (p : L) ^ 2 * (algebraMap F L kF - (σ₁ y - y)) := by
      simp only [zM, MulMemClass.coe_mul, SubmonoidClass.coe_pow, AddSubgroupClass.coe_sub,
        IntermediateField.coe_algebraMap_apply, hsM]
      simp [yM]
    rw [h3, map_mul, map_sub, map_pow, map_natCast, h2, h1]
    ring
  have hzO : (zM : L) ∈ 𝒪[L] := by
    rw [hzL]
    exact sub_mem (sub_mem (hσO σ₁ _ hw) hw) (mul_mem (pow_mem (natCast_mem _ p) 2) hz₁)
  have hfin : Module.finrank F M = J.index := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index, hMdef, IntermediateField.fixingSubgroup_fixedField]
  refine ⟨⟨zM, ?_⟩, ?_⟩
  · rw [Valuation.mem_integer_iff] at hzO ⊢
    have hmono := ValuativeExtension.mapValueGroupWithZero_strictMono (A := M) (B := L)
    rw [IntermediateField.valuation_coe, ← map_one (ValuativeExtension.mapValueGroupWithZero M L)] at hzO
    exact hmono.le_iff_le.mp hzO
  · have hz : zM = algebraMap F M ((p : F) ^ 2 * kF) - algebraMap F M ((p : F) ^ 2) * (sM - yM) := by
      simp only [zM, map_mul, map_pow, map_natCast]; ring
    have htr : Algebra.trace F M sM = Algebra.trace F M yM := Algebra.trace_eq_of_algEquiv (σ₁.restrictNormal M) yM
    show Algebra.trace F M zM = _
    rw [hz, map_sub, Algebra.trace_algebraMap, ← Algebra.smul_def, LinearMap.map_smul, map_sub, htr, sub_self,
      smul_zero, sub_zero, hfin, nsmul_eq_mul]
    have hcF : (c : F) * (p : F) ^ r = (J.index : F) * (a σ₁ : F) := by exact_mod_cast congrArg (fun t : ℤ => (t : F)) hc
    have hk : (J.index : F) * kF = c := by
      simp only [kF]
      rw [mul_div_assoc', div_eq_iff hpF]
      linear_combination -hcF
    linear_combination (p : F) ^ 2 * hk
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram


open IsDiscreteValuationRing in
theorem sq_mul_not_mem_maxIdeal_pow :
    ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (p e : ℕ) (c : ℤ),
      p.Prime → 0 < e → OrdIs F p e → ¬ (p : ℤ) ∣ c →
      ∀ w ∈ 𝓂[F] ^ (3 * e), ((w : 𝒪[F]) : F) ≠ (p : F) ^ 2 * (c : F) := by
  intro F _ _ _ _ p e c hp he hord hc w hw heq
  have hw' : w = (p : 𝒪[F]) ^ 2 * (c : 𝒪[F]) := by
    apply Subtype.ext
    simpa using heq

  have hcop : IsCoprime (p : ℤ) c :=
    (Irreducible.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hp).irreducible).mpr hc
  obtain ⟨a, b, hab⟩ := hcop.map (Int.castRingHom 𝒪[F])
  have h1 : IsUnit (a * (Int.castRingHom 𝒪[F]) p + b * (Int.castRingHom 𝒪[F]) c) := by
    rw [hab]; exact isUnit_one
  have hpnu : ¬ IsUnit (p : 𝒪[F]) := by
    rintro ⟨u, hu⟩
    have h0 := addVal_eq_zero_of_unit u
    rw [hu] at h0
    unfold OrdIs at hord
    rw [hord] at h0
    exact (Nat.pos_iff_ne_zero.mp he) (by exact_mod_cast h0)
  have hcu : IsUnit (c : 𝒪[F]) := by
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h1 with h | h
    · exfalso; apply hpnu
      have := isUnit_of_mul_isUnit_right h
      simpa using this
    · have := isUnit_of_mul_isUnit_right h
      simpa using this

  have hval : addVal 𝒪[F] w = ((2 * e : ℕ) : ℕ∞) := by
    obtain ⟨u, hu⟩ := hcu
    rw [hw', addVal_mul, addVal_pow, ← hu, addVal_eq_zero_of_unit, add_zero]
    unfold OrdIs at hord
    rw [hord]
    push_cast
    rfl
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible 𝒪[F]
  rw [(irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hw
  have hle := (addVal_le_iff_dvd).mpr hw
  rw [addVal_pow, addVal_uniformizer hϖ, hval] at hle
  have : ((3 * e : ℕ) : ℕ∞) ≤ ((2 * e : ℕ) : ℕ∞) := by simpa using hle
  have := ENat.coe_le_coe.mp this
  omega

end GlobalTheory.PMon.Ram
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem ordIs_of_ordIs_ext : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (p E : ℕ), OrdIs L p E → ∃ e : ℕ, OrdIs F p e ∧ E = (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation L))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation F))) * e ∧ (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation L))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation F))) = Nat.card ↥(lowerRamificationGroup F L 0) := by
  intro F L _ _ _ _ _ _ _ _ _ _ _ _ p E h
  unfold OrdIs at h ⊢
  have hmap := addVal_algebraMap_integer F L (p : 𝒪[F])
  rw [map_natCast] at hmap
  rw [hmap] at h
  have hne : IsDiscreteValuationRing.addVal 𝒪[F] (p : 𝒪[F]) ≠ ⊤ := by
    intro ht
    rw [ht, ENat.mul_top (by exact_mod_cast (ramificationIndex_pos F L).ne')] at h
    exact ENat.coe_ne_top E h.symm
  obtain ⟨e, he⟩ := ENat.ne_top_iff_exists.mp hne
  refine ⟨e, he.symm, ?_, (card_lowerRamificationGroup_zero (K := F) (L := L)).symm⟩
  rw [← he] at h
  exact_mod_cast h.symm

end GlobalTheory.PMon.Ram
end
