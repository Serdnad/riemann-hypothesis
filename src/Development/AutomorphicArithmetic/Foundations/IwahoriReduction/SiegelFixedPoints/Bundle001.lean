module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle318
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle157
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle131
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle182
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.IsThBIff

@[expose] public section

section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

private theorem hahnSeries_map_mul {Ω : Type} [Field Ω] [Algebra ℚ Ω] (s : Ω ≃ₐ[ℚ] Ω) (x y : HahnSeries ℚ Ω) :
    HahnSeries.map (x * y) (s : Ω →+* Ω) = HahnSeries.map x (s : Ω →+* Ω) * HahnSeries.map y (s : Ω →+* Ω) := by
  have e : ∀ z : HahnSeries ℚ Ω, HahnSeries.map z ((s : Ω →+* Ω) : Ω →ₙ+* Ω) = HahnSeries.map z (s : Ω →+* Ω) := by
    intro z
    ext r
    simp [HahnSeries.map_coeff]
    rfl
  rw [← e, ← e, ← e]
  exact HahnSeries.map_mul _

private theorem theta_hahnSeries_map_comm {Ω : Type} [Field Ω] [Algebra ℚ Ω] (s : Ω ≃ₐ[ℚ] Ω) (q : ℚ) (x : HahnSeries ℚ Ω) :
    theta q (HahnSeries.map x (s : Ω →+* Ω)) = HahnSeries.map (theta q x) (s : Ω →+* Ω) := by
  ext r
  show algebraMap ℚ Ω (q * r) * (HahnSeries.map x (s : Ω →+* Ω)).coeff r = (s : Ω →+* Ω) (algebraMap ℚ Ω (q * r) * x.coeff r)
  rw [HahnSeries.map_coeff, map_mul (s : Ω →+* Ω),
    show (s : Ω →+* Ω) (algebraMap ℚ Ω (q * r)) = algebraMap ℚ Ω (q * r) from s.commutes _]

private theorem hahnSeries_map_sub {Ω : Type} [Field Ω] [Algebra ℚ Ω] (s : Ω ≃ₐ[ℚ] Ω) (x y : HahnSeries ℚ Ω) :
    HahnSeries.map (x - y) (s : Ω →+* Ω) = HahnSeries.map x (s : Ω →+* Ω) - HahnSeries.map y (s : Ω →+* Ω) := by
  ext r
  simp [HahnSeries.map_coeff]

private theorem prim_hahnSeries_map_of_prim_comap {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A A' : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω)
    (hA : ∀ x, x ∈ A' ↔ s x ∈ A) (x : HahnSeries ℚ Ω) (hx : Prim A' x) :
    Prim A (HahnSeries.map x (s : Ω →+* Ω)) := by
  obtain ⟨h1, r, hr0, hr⟩ := hx
  refine ⟨fun t => ?_, r, ?_, ?_⟩
  · rw [HahnSeries.map_coeff]
    exact (hA _).1 (h1 t)
  · rw [HahnSeries.map_coeff]
    exact (map_ne_zero _).2 hr0
  · rw [HahnSeries.map_coeff, ← map_inv₀]
    exact (hA _).1 hr


theorem UpperTheory.Kd.L.dlgal :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (A A' : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω), (∀ x, x ∈ A' ↔ s x ∈ A) → ∀ (n : ℕ) (a : ℚ) (f : X.K) (φ : HahnSeries ℚ Ω), IsDl X A' l n a f φ → IsDl X A l n a (X.gal s f) (HahnSeries.map φ (s : Ω →+* Ω)) := by
  intro Ω _ _ _ _ ε X l _ A A' s hA n q f φ h
  obtain ⟨hφ, a, b, κ, hκ, hfb, ha, hb, hc⟩ := h
  have hM : ∀ g : X.K, X.exp (X.gal s g) = HahnSeries.map (X.exp g) (s : Ω →+* Ω) := by
    intro g
    ext r
    rw [HahnSeries.map_coeff, X.gal_exp]
    rfl
  have hsm : ∀ (c : Ω) (y : HahnSeries ℚ Ω) (r : ℚ),
      (algebraMap Ω (HahnSeries ℚ Ω) c * y).coeff r = c * y.coeff r := by
    intro c y r
    rw [HahnSeries.algebraMap_apply']
    simp [HahnSeries.C_mul_eq_smul]
  have hsκ : s κ ≠ 0 := (map_ne_zero _).2 hκ
  have hc0 : algebraMap Ω X.K (s κ) ≠ 0 := (map_ne_zero _).2 hsκ
  have hexpa : X.exp ((algebraMap Ω X.K (s κ))⁻¹ * X.gal s (algebraMap Ω X.K κ * a)) =
      HahnSeries.map (X.exp a) (s : Ω →+* Ω) := by
    rw [← map_inv₀, map_mul, AlgHom.commutes, hM, map_mul, AlgHom.commutes]
    ext r
    rw [hsm, HahnSeries.map_coeff, HahnSeries.map_coeff, hsm, map_mul, ← mul_assoc,
      show (s κ)⁻¹ * (s : Ω →+* Ω) κ = 1 from inv_mul_cancel₀ hsκ, one_mul]
  refine ⟨fun r => ?_, (algebraMap Ω X.K (s κ))⁻¹ * X.gal s (algebraMap Ω X.K κ * a), X.gal s b, s κ, hsκ,
    ?_, ?_, ?_, fun r => ?_⟩
  · rw [HahnSeries.map_coeff]
    exact (hA _).1 (hφ r)
  · rw [← map_mul, hfb, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
  · rw [hexpa]
    exact prim_hahnSeries_map_of_prim_comap A A' s hA _ ha
  · rw [hM]
    exact prim_hahnSeries_map_of_prim_comap A A' s hA _ hb
  · rw [hexpa, hM, theta_hahnSeries_map_comm, theta_hahnSeries_map_comm, ← hahnSeries_map_mul, ← hahnSeries_map_mul, ← hahnSeries_map_mul, ← hahnSeries_map_mul, ← hahnSeries_map_sub,
      HahnSeries.map_coeff, HahnSeries.map_coeff]
    obtain ⟨z, hz, e⟩ := hc r
    refine ⟨s z, (hA z).1 hz, ?_⟩
    rw [← map_sub, e, map_mul]
    simp
end

section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

private theorem exists_pow_eq {Ω : Type} [Field Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω)
    (hl : ((l : ℕ) : Ω) ∈ A.nonunits) (M : ℕ) (hM : 0 < M) : ∃ k : ℕ, ∃ u ∈ A, (l : Ω) ^ k = (M : Ω) * u := by
  have hp : l.Prime := Fact.out
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hM.ne' l hp.ne_one
  have hc : IsCoprime (l : ℤ) (m : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hm)
  have hc' : IsCoprime (l : A) (m : A) := by simpa using hc.map (Int.castRingHom A)
  have hlu : ¬ IsUnit (l : A) := by
    have h1 : ((l : A) : Ω) ∈ A.nonunits := by simpa using hl
    have := (ValuationSubring.coe_mem_nonunits_iff).1 h1
    exact (IsLocalRing.mem_maximalIdeal _).1 this
  have hmu : IsUnit (m : A) := by
    obtain ⟨a, b, e⟩ := hc'
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add (e ▸ isUnit_one) with h | h
    · exact absurd (isUnit_of_mul_isUnit_right h) hlu
    · exact isUnit_of_mul_isUnit_right h
  obtain ⟨u, hu⟩ := hmu.exists_right_inv
  refine ⟨k, (u : Ω), u.2, ?_⟩
  have e : (m : Ω) * (u : Ω) = 1 := by simpa using congrArg (fun x : A => (x : Ω)) hu
  push_cast
  rw [mul_assoc, e, mul_one]

private theorem isDl_divM {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω] {ε : Ω →+* ℂ}
    (X : Tower Ω ε) (A : ValuationSubring Ω) (l n k M : ℕ) (hM : 0 < M) (u : Ω) (hu : u ∈ A)
    (hk : (l : Ω) ^ k = (M : Ω) * u) (F : X.K) (ψ : HahnSeries ℚ Ω) (hψ : ∀ r, ψ.coeff r ∈ A)
    (h : IsDl X A l (n + k) (M : ℚ) F (HahnSeries.C (M : Ω) * ψ)) : IsDl X A l n 1 F ψ := by
  obtain ⟨-, a, c, κ, hκ, he, ha, hc, hcg⟩ := h
  refine ⟨hψ, a, c, κ, hκ, he, ha, hc, fun r => ?_⟩
  obtain ⟨z, hz, e⟩ := hcg r
  refine ⟨u * z, mul_mem hu hz, ?_⟩
  have hm : algebraMap ℚ Ω (M : ℚ) = (M : Ω) := map_natCast _ _
  rw [NrmT.theta_eq_C_mul _ (X.exp a), NrmT.theta_eq_C_mul _ (X.exp c), hm] at e
  have hM0 : (M : Ω) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  have e2 : HahnSeries.C (M : Ω) * ψ * X.exp a * X.exp c =
      HahnSeries.C (M : Ω) * (ψ * X.exp a * X.exp c) := by ring
  have e3 : HahnSeries.C (M : Ω) * theta 1 (X.exp a) * X.exp c -
      X.exp a * (HahnSeries.C (M : Ω) * theta 1 (X.exp c)) =
      HahnSeries.C (M : Ω) * (theta 1 (X.exp a) * X.exp c - X.exp a * theta 1 (X.exp c)) := by ring
  rw [e2, e3, HahnSeries.C_mul_eq_smul, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, HahnSeries.coeff_smul,
    smul_eq_mul, smul_eq_mul, ← mul_sub, pow_add, hk] at e
  apply mul_left_cancel₀ hM0
  rw [e]; ring

private theorem isDl_weak {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}
    (X : Tower Ω ε) (A : ValuationSubring Ω) (l n k : ℕ) (s : ℚ) (F : X.K) (φ : HahnSeries ℚ Ω)
    (h : IsDl X A l (n + k) s F φ) : IsDl X A l n s F φ := by
  obtain ⟨hφ, a, c, κ, hκ, he, ha, hc, hcg⟩ := h
  refine ⟨hφ, a, c, κ, hκ, he, ha, hc, fun r => ?_⟩
  obtain ⟨z, hz, e⟩ := hcg r
  exact ⟨(l : Ω) ^ k * z, mul_mem (pow_mem (natCast_mem A l) k) hz, by rw [e, pow_add]; ring⟩

theorem UpperTheory.Kd.L.nrm :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ (n M : ℕ), 0 < M → ∀ (w : X.K) (φ φ' : HahnSeries ℚ Ω), w ∈ KT X M → IsDl X A l n (M : ℚ) w φ → (∀ r : ℚ, φ.coeff r ≠ 0 → (r * M).den = 1) → (∀ r : ℚ, φ'.coeff r = if r.den = 1 then φ.coeff r else 0) → IsDl X A l n 1 (nrmT X M w) φ' := by
  intro Ω _ _ _ _ ε X l _ A hl n M hM w φ φ' hw hφ _ hφ'
  have hj := X.j_hol.imp fun _ h => And.symm h
  obtain ⟨k, u, huA, hk⟩ := exists_pow_eq l A hl M hM
  have hw0 : w ≠ 0 := by
    rintro rfl
    obtain ⟨-, a, c, κ, hκ, he, ha, -, -⟩ := hφ
    rw [zero_mul] at he
    have ha0 : a = 0 := by
      rcases mul_eq_zero.1 he.symm with h | h
      · exact absurd ((map_eq_zero_iff _ (algebraMap Ω X.K).injective).1 h) hκ
      · exact h
    obtain ⟨-, r, hr, -⟩ := ha
    exact hr (by rw [ha0, map_zero]; rfl)
  obtain ⟨φ2, h2, hs2⟩ := GlobalTheory.T.exists_logDerivQExpansion_modPrimePow_of_translationInvariant ε X hj l A hl (n + k) M w hM hw0 hw
  have hu := GlobalTheory.T.isLogDerivQExpansionModPrimePow_unique ε X hj l A hl n (M : ℚ) w φ φ2 hφ (isDl_weak X A l n k _ w φ2 h2)
  have hT : ∀ b ∈ Finset.range M,
      IsDl X A l (n + k) (M : ℚ) (X.sl (ofSL (ModularGroup.T ^ b)) w) (NrmT.trT ε b φ2) :=
    fun b _ => NrmT.isLogDerivQExpansionModPrimePow_slash_T_pow X A l (n + k) _ w φ2 b h2
  have hP := GlobalTheory.T.isLogDerivQExpansion_finset_prod_zpow ε X hj l A hl (n + k) (M : ℚ) ℕ (Finset.range M)
    (fun b => X.sl (ofSL (ModularGroup.T ^ b)) w) (fun b => NrmT.trT ε b φ2) (fun _ => 1) hT
  simp only [zpow_one, one_smul] at hP
  rw [NrmT.sum_trT M φ2 hs2 (NrmT.resZ φ2) (NrmT.resZ_coeff φ2)] at hP
  have hN := isDl_divM X A l n k M hM u huA hk _ (NrmT.resZ φ2) (fun r => by
    rw [NrmT.resZ_coeff]; split_ifs
    · exact h2.1 r
    · exact zero_mem A) hP
  refine NrmT.isDl_congr X A l n 1 _ (NrmT.resZ φ2) φ' hN (fun r => ?_) (fun r => ?_)
  · rw [hφ']; split_ifs
    · exact hφ.1 r
    · exact zero_mem A
  · rw [hφ', NrmT.resZ_coeff]; split_ifs
    · exact hu r
    · exact ⟨0, zero_mem A, by ring⟩
end
