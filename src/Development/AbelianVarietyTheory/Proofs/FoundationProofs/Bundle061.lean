module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle020
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle027
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle045
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
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
public import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Mathlib.Geometry.Manifold.StructureGroupoid

@[expose] public section

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNProd

theorem hs_mul : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (C : ℝ) (φ ψ : ℂ → ℂ) (h h' : HahnSeries ℚ Ω),
    HS ε C φ h → HS ε C ψ h' → HS ε C (φ * ψ) (h * h') := by
  intro Ω _ ε C φ ψ h h' H H' z hz
  set e : ℚ → ℂ := fun r => Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z) with he
  set a : ℚ → ℂ := fun r => ε (h.coeff r) * e r with ha
  set b : ℚ → ℂ := fun r => ε (h'.coeff r) * e r with hb
  have hA : HasSum a (φ z) := H z hz
  have hB : HasSum b (ψ z) := H' z hz
  have hAn : Summable fun r => ‖a r‖ := summable_norm_iff.2 hA.summable
  have hBn : Summable fun r => ‖b r‖ := summable_norm_iff.2 hB.summable
  have hP : HasSum (fun p : ℚ × ℚ => a p.1 * b p.2) (φ z * ψ z) :=
    hA.mul hB (summable_mul_of_summable_norm hAn hBn)
  have hF := hP.tsum_fiberwise (fun p : ℚ × ℚ => p.1 + p.2)
  refine hF.congr_fun ?_
  intro s
  have hexp : ∀ p : ℚ × ℚ, p.1 + p.2 = s → a p.1 * b p.2 = ε (h.coeff p.1) * ε (h'.coeff p.2) * e s := by
    intro p hp
    simp only [ha, hb, he, ← hp]
    have : Complex.exp (2 * Real.pi * Complex.I * ((p.1 + p.2 : ℚ) : ℂ) * z) =
        Complex.exp (2 * Real.pi * Complex.I * (p.1 : ℂ) * z) * Complex.exp (2 * Real.pi * Complex.I * (p.2 : ℂ) * z) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [this]; ring
  rw [tsum_subtype (f := fun p : ℚ × ℚ => a p.1 * b p.2)]
  rw [tsum_eq_sum (s := Finset.antidiagonal h.isPWO_support h'.isPWO_support s)]

  · simp only [HahnSeries.coeff_mul, map_sum, map_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_antidiagonal] at hp
    rw [Set.indicator_of_mem (by simpa using hp.2.2)]
    exact (hexp p hp.2.2).symm
  · intro p hp
    by_cases hs : p.1 + p.2 = s
    · rw [Set.indicator_of_mem (by simpa using hs), hexp p hs]
      rw [Finset.mem_antidiagonal] at hp
      simp only [HahnSeries.mem_support, not_and] at hp
      by_cases h1 : h.coeff p.1 = 0
      · simp [h1]
      · have h2 : h'.coeff p.2 = 0 := by
          by_contra h2; exact hp h1 h2 hs
        simp [h2]
    · exact Set.indicator_of_notMem (by simpa using hs) _

end GlobalTheory.FNProd
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem den_scale_left {r : ℚ} {N M : ℕ} (hM : 0 < M) (h : ∃ n : ℤ, r = (n : ℚ) / N) :
    ∃ n : ℤ, r = (n : ℚ) / ((N * M : ℕ) : ℚ) := by
  obtain ⟨n, rfl⟩ := h
  refine ⟨n * M, ?_⟩
  have : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  push_cast
  rw [mul_div_mul_right _ _ this]

theorem den_scale_right {r : ℚ} {N M : ℕ} (hM : 0 < M) (h : ∃ n : ℤ, r = (n : ℚ) / N) :
    ∃ n : ℤ, r = (n : ℚ) / ((M * N : ℕ) : ℚ) := by
  rw [Nat.mul_comm]; exact den_scale_left hM h

theorem den_union {Ω : Type} [Field Ω] {h h' : HahnSeries ℚ Ω} (hh : Den h) (hh' : Den h')
    (x : HahnSeries ℚ Ω) (hx : x.support ⊆ h.support ∪ h'.support) : Den x := by
  obtain ⟨N, hN, H⟩ := hh
  obtain ⟨N', hN', H'⟩ := hh'
  refine ⟨N * N', Nat.mul_pos hN hN', fun r hr => ?_⟩
  rcases hx hr with h1 | h1
  · have := den_scale_left (M := N') hN' (H r h1)
    simpa using this
  · have := den_scale_right (M := N) hN (H' r h1)
    simpa using this

theorem den_mul {Ω : Type} [Field Ω] {h h' : HahnSeries ℚ Ω} (hh : Den h) (hh' : Den h') :
    Den (h * h') := by
  obtain ⟨N, hN, H⟩ := hh
  obtain ⟨N', hN', H'⟩ := hh'
  refine ⟨N * N', Nat.mul_pos hN hN', fun r hr => ?_⟩
  have hs := HahnSeries.support_mul_subset (x := h) (y := h') hr
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.mp hs
  obtain ⟨n, rfl⟩ := H a ha
  obtain ⟨m, rfl⟩ := H' b hb
  refine ⟨n * N' + m * N, ?_⟩
  have h1 : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have h2 : (N' : ℚ) ≠ 0 := by exact_mod_cast hN'.ne'
  push_cast
  field_simp

theorem den_single {Ω : Type} [Field Ω] (r : ℚ) (c : Ω) : Den (HahnSeries.single r c : HahnSeries ℚ Ω) := by
  refine ⟨r.den, r.den_pos, fun s hs => ⟨r.num, ?_⟩⟩
  rw [HahnSeries.coeff_single] at hs
  split_ifs at hs with hsr
  · rw [hsr]; exact (Rat.num_div_den r).symm
  · exact (hs rfl).elim

theorem den_ring : ∀ (Ω : Type) [Field Ω], (∀ h h' : HahnSeries ℚ Ω, Den h → Den h' → Den (h + h') ∧ Den (h - h') ∧ Den (h * h')) ∧ ∀ (r : ℚ) (c : Ω), Den (HahnSeries.single r c : HahnSeries ℚ Ω) := by
  intro Ω _
  refine ⟨fun h h' hh hh' => ⟨den_union hh hh' _ (HahnSeries.support_add_subset h h'),
    den_union hh hh' _ (HahnSeries.support_sub_subset h h'), den_mul hh hh'⟩, fun r c => den_single r c⟩

end GlobalTheory.FN
end

section

open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

namespace GlobalTheory.Sieg

theorem coe_T_smul (τ : ℍ) : ((ModularGroup.T • τ : ℍ) : ℂ) = (τ : ℂ) + 1 := by
  rw [UpperHalfPlane.modular_T_smul, UpperHalfPlane.coe_vadd]
  push_cast; ring

theorem ee_add_one (z : ℂ) : ee (z + 1) = ee z := by
  unfold ee
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (z + 1) = 2 * Real.pi * Complex.I * z + 2 * Real.pi * Complex.I by ring,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

theorem rowVectorMulIntMatrixSL2_modularGroupT_apply (x : Fin 2 → ℚ) : act x ModularGroup.T 0 = x 0 ∧ act x ModularGroup.T 1 = x 0 + x 1 := by
  simp [act, ModularGroup.T, Fin.sum_univ_two]

theorem pt_T_smul (x : Fin 2 → ℚ) (τ : ℍ) : pt x (ModularGroup.T • τ) = pt (act x ModularGroup.T) τ := by
  obtain ⟨h0, h1⟩ := rowVectorMulIntMatrixSL2_modularGroupT_apply x
  simp only [pt, coe_T_smul, h0, h1]
  push_cast; ring

theorem sg_T_smul : ∀ (c : ℕ) (x : Fin 2 → ℚ) (τ : ℍ), sg c x (ModularGroup.T • τ) = sg c (act x ModularGroup.T) τ := by
  intro c x τ
  simp only [sg]
  rw [pt_T_smul, coe_T_smul, ee_add_one]

end GlobalTheory.Sieg
end

section

open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

namespace GlobalTheory.Sieg

theorem act_one_gen (x : Fin 2 → ℚ) : act x 1 = x := by
  funext i
  fin_cases i <;> simp [act, Fin.sum_univ_two]

theorem act_mul_gen (x : Fin 2 → ℚ) (γ δ : SL(2, ℤ)) : act x (γ * δ) = act (act x γ) δ := by
  funext i
  simp only [act, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  push_cast
  ring

theorem modular_law_of_generators (P : (Fin 2 → ℚ) → Prop) (f : (Fin 2 → ℚ) → ℍ → ℂ)
    (hP : ∀ x γ, P x → P (act x γ))
    (hS : ∀ x τ, P x → f x (ModularGroup.S • τ) = f (act x ModularGroup.S) τ)
    (hT : ∀ x τ, P x → f x (ModularGroup.T • τ) = f (act x ModularGroup.T) τ) :
    ∀ (γ : SL(2, ℤ)) x τ, P x → f x (γ • τ) = f (act x γ) τ := by
  let H : Subgroup SL(2, ℤ) :=
    { carrier := {γ | ∀ x τ, P x → f x (γ • τ) = f (act x γ) τ}
      one_mem' := by
        intro x τ _
        simp [act_one_gen]
      mul_mem' := by
        intro γ δ hγ hδ x τ hx
        rw [mul_smul, hγ x _ hx, hδ _ τ (hP x γ hx), act_mul_gen]
      inv_mem' := by
        intro γ hγ x τ hx
        have h := hγ (act x γ⁻¹) (γ⁻¹ • τ) (hP x _ hx)
        rw [smul_inv_smul, ← act_mul_gen, inv_mul_cancel, act_one_gen] at h
        exact h.symm }
  have hle : Subgroup.closure {ModularGroup.S, ModularGroup.T} ≤ H := by
    rw [Subgroup.closure_le]
    intro γ hγ
    rcases hγ with rfl | rfl
    · exact hS
    · exact hT
  intro γ
  have : γ ∈ H := hle (by rw [_root_.SpecialLinearGroup.SL2Z_generators]; exact Subgroup.mem_top γ)
  exact this

end GlobalTheory.Sieg
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem clear_denominators : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε)
    (P : Polynomial T.K), P ≠ 0 → ∃ (p : ℕ → GlobalTheory.FN.ring ε.range) (u : T.K), u ≠ 0 ∧ p P.natDegree ≠ 0 ∧
      ∀ i, T.io (p i) = u * P.coeff i := by
  intro Ω _ _ _ ε T P hP
  classical
  choose a b hb hab using T.io_surj
  set S := Finset.range (P.natDegree + 1) with hS
  have hbne : ∀ f, T.io (b f) ≠ 0 := fun f h => hb f (T.io_inj (by rw [h, map_zero]))
  refine ⟨fun i => if i ∈ S then a (P.coeff i) * ∏ j ∈ S.erase i, b (P.coeff j) else 0,
    T.io (∏ j ∈ S, b (P.coeff j)), ?_, ?_, ?_⟩
  · rw [map_prod]; exact Finset.prod_ne_zero_iff.mpr fun j _ => hbne _
  · have hmem : P.natDegree ∈ S := by simp [hS]
    intro h
    simp only [hmem, if_true] at h
    have h2 := congrArg T.io h
    rw [map_zero, map_mul, ← hab, map_prod, mul_assoc, Finset.mul_prod_erase S (fun j => T.io (b (P.coeff j))) hmem] at h2
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact hP (Polynomial.leadingCoeff_eq_zero.mp h3)
    · exact (Finset.prod_ne_zero_iff.mpr fun j _ => hbne _) h3
  · intro i
    by_cases hi : i ∈ S
    · simp only [hi, if_true]
      rw [map_mul, ← hab, map_prod, map_prod, mul_assoc, Finset.mul_prod_erase S (fun j => T.io (b (P.coeff j))) hi, mul_comm]
    · simp only [hi, if_false, map_zero]
      have : P.natDegree < i := by simp [hS] at hi; omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt this, mul_zero]

end GlobalTheory.FN
end

section

open GlobalTheory.K4 GlobalTheory.KEdge GlobalTheory.NeedB Polynomial

namespace GlobalTheory.K4.TopSpec

variable {F K Ω : Type} [Field F] [Field K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω]

open Polynomial in
variable {F K Ω : Type} [Field F] [Field K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω]
  [IsScalarTower F K Ω] in
theorem _root_.GlobalTheory.K4.TopSpec.res_mem_geo (g : Ω ≃ₐ[K] Ω) :
    AlgEquiv.restrictScalarsHom F g ∈ _root_.GlobalTheory.K4.geo F K Ω := by
  rw [_root_.GlobalTheory.K4.TopW.mem_geo]
  intro z
  exact g.commutes z

open Polynomial in
variable {F K Ω : Type} [Field F] [Field K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω]
  [IsScalarTower F K Ω] in
theorem _root_.GlobalTheory.K4.TopSpec.exists_res {g : Ω ≃ₐ[F] Ω}
    (hg : g ∈ _root_.GlobalTheory.K4.geo F K Ω) :
    ∃ g' : Ω ≃ₐ[K] Ω, AlgEquiv.restrictScalarsHom F g' = g := by
  rw [_root_.GlobalTheory.K4.TopW.mem_geo] at hg
  refine ⟨{ g.toRingEquiv with commutes' := hg }, ?_⟩
  ext y
  rfl

open Polynomial in
variable {F K Ω : Type} [Field F] [Field K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω]
  [IsScalarTower F K Ω] in
theorem _root_.GlobalTheory.K4.TopSpec.continuous_res [Algebra.IsAlgebraic K Ω] :
    Continuous (AlgEquiv.restrictScalarsHom F : (Ω ≃ₐ[K] Ω) →* (Ω ≃ₐ[F] Ω)) := by
  classical
  apply continuous_of_continuousAt_one
  rw [ContinuousAt, map_one]
  intro s hs
  rw [krullTopology_mem_nhds_one_iff] at hs
  obtain ⟨E, hE, hEs⟩ := hs
  rw [Filter.mem_map, krullTopology_mem_nhds_one_iff]
  let b := Module.finBasis F E
  refine ⟨IntermediateField.adjoin K (Set.range fun i => (b i : Ω)), ?_, ?_⟩
  · exact IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  · intro g hg
    apply hEs
    have hfix : ∀ i, g (b i : Ω) = b i := fun i =>
      (IntermediateField.mem_fixingSubgroup_iff _ _).mp hg _
        (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    have key : ∀ z : E, AlgEquiv.restrictScalarsHom F g (z : Ω) = z := by
      intro z
      induction (b.mem_span z) using Submodule.span_induction with
      | mem u hu =>
        obtain ⟨i, rfl⟩ := hu
        exact hfix i
      | zero => simp
      | add u v _ _ hu hv => rw [IntermediateField.coe_add, map_add (f := _), hu, hv]
      | smul a u _ hu => rw [IntermediateField.coe_smul, map_smul, hu]
    exact key ⟨y, hy⟩

end GlobalTheory.K4.TopSpec


open Polynomial in
theorem _root_.GlobalTheory.K4.isTopW_topW : ∀ (k K Ω F : Type) [Field k]
    [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Algebra (RatFunc k) K]
    [IsScalarTower k[X] (RatFunc k) K] [FiniteDimensional (RatFunc k) K] [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] [Field F] [Algebra F K] [Algebra F Ω] [IsScalarTower F K Ω] [Normal F K]
    (N : ℕ) (ζ : Ω), 0 < N → IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[F] Ω, g ζ = ζ) →
    (∀ τ : K ≃ₐ[F] K, ∀ x ∈ FunctionField.ringOfIntegers k K,
      τ x ∈ FunctionField.ringOfIntegers k K) →
    ∀ (a b : F) (α β : Ω), a ≠ 0 → b ≠ 0 → algebraMap F K a ∈ FunctionField.ringOfIntegers k K →
      (algebraMap F K a)⁻¹ ∈ FunctionField.ringOfIntegers k K →
      algebraMap F K b ∈ FunctionField.ringOfIntegers k K →
      (algebraMap F K b)⁻¹ ∈ FunctionField.ringOfIntegers k K →
      α ^ N = algebraMap F Ω a → β ^ N = algebraMap F Ω b →
    ∀ (x y : (Ω ≃ₐ[F] Ω) →* Multiplicative (ZMod N)),
      (∀ g, (x g).toAdd = _root_.GlobalTheory.NeedB.kum (N := N) ζ α g) →
      (∀ g, (y g).toAdd = _root_.GlobalTheory.NeedB.kum (N := N) ζ β g) →
    ∀ η : (Ω ≃ₐ[F] Ω) → ZMod N,
      _root_.GlobalTheory.KEdge.CobOn (_root_.GlobalTheory.K4.geo F K Ω) x y η →
      IsLocallyConstant (fun g : _root_.GlobalTheory.K4.geo F K Ω => η g) →
      (∀ (B : ValuationSubring Ω) (g : Ω ≃ₐ[F] Ω),
        _root_.GlobalTheory.NeedB.Over (FunctionField.ringOfIntegers k K).toSubring B →
        (∀ z, B.valuation z ≤ 1 → B.valuation (g z - z) < 1) →
        g ∈ _root_.GlobalTheory.K4.geo F K Ω → η g = 0) →
    ∀ σ : Ω ≃ₐ[F] Ω, _root_.GlobalTheory.K4.IsTopW (K := K) ζ x y η σ
      (_root_.GlobalTheory.K4.topW (K := K) ζ x y η σ) := by
  intro k K Ω F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ N ζ hN hζ hfix _ a b α β ha hb _ _ _ _ hα hβ
    x y hx hy η hcob hη _ σ
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : CharZero (RatFunc k) :=
    charZero_of_injective_algebraMap (algebraMap k (RatFunc k)).injective
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap (RatFunc k) K).injective
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  haveI : Algebra.IsAlgebraic F Ω := Algebra.IsAlgebraic.trans F K Ω
  set H := _root_.GlobalTheory.K4.geo F K Ω with hH
  haveI : H.Normal := ⟨fun h hh g => _root_.GlobalTheory.K4.TopW.conj_mem_geo g hh⟩
  obtain ⟨hhom, -, -⟩ := _root_.GlobalTheory.KEdge.edge_cup_props _ N H x y η hcob
  have hres := _root_.GlobalTheory.K4.TopSpec.continuous_res (F := F) (K := K) (Ω := Ω)
  have hmem : ∀ g : Ω ≃ₐ[K] Ω, AlgEquiv.restrictScalarsHom F g ∈ H :=
    _root_.GlobalTheory.K4.TopSpec.res_mem_geo
  have hne : ∀ {γ : Ω} {c : F}, c ≠ 0 → γ ^ N = algebraMap F Ω c → γ ≠ 0 := by
    intro γ c hc hγ h0
    rw [h0, zero_pow hN.ne'] at hγ
    exact hc ((algebraMap F Ω).injective (hγ.symm.trans (map_zero _).symm))
  have hkum : ∀ {γ : Ω} {c : F}, c ≠ 0 → γ ^ N = algebraMap F Ω c →
      IsLocallyConstant (_root_.GlobalTheory.NeedB.kum (K := F) (N := N) ζ γ) :=
    fun hc hγ => (_root_.GlobalTheory.NeedB.KumLemma.kummer_character_main F Ω N ζ _ hN hζ hfix
      (hne hc hγ) ⟨_, hγ.symm⟩).1
  have hx_lc : IsLocallyConstant fun g : Ω ≃ₐ[K] Ω =>
      Multiplicative.toAdd (x (AlgEquiv.restrictScalarsHom F g)) := by
    have hfun : (fun g : Ω ≃ₐ[K] Ω => Multiplicative.toAdd (x (AlgEquiv.restrictScalarsHom F g))) =
        _root_.GlobalTheory.NeedB.kum ζ α ∘ AlgEquiv.restrictScalarsHom F := funext fun g => hx _
    rw [hfun]
    exact (hkum ha hα).comp_continuous hres
  have hy_lc : IsLocallyConstant fun g : Ω ≃ₐ[K] Ω =>
      Multiplicative.toAdd (y (AlgEquiv.restrictScalarsHom F g)) := by
    have hfun : (fun g : Ω ≃ₐ[K] Ω => Multiplicative.toAdd (y (AlgEquiv.restrictScalarsHom F g))) =
        _root_.GlobalTheory.NeedB.kum ζ β ∘ AlgEquiv.restrictScalarsHom F := funext fun g => hy _
    rw [hfun]
    exact (hkum hb hβ).comp_continuous hres
  have hη₁ : IsLocallyConstant fun g : Ω ≃ₐ[K] Ω => η (AlgEquiv.restrictScalarsHom F g) :=
    hη.comp_continuous (f := fun g : Ω ≃ₐ[K] Ω => (⟨AlgEquiv.restrictScalarsHom F g, hmem g⟩ : H))
      (hres.subtype_mk _)
  have hη₂ : IsLocallyConstant fun g : Ω ≃ₐ[K] Ω => η (σ * AlgEquiv.restrictScalarsHom F g * σ⁻¹) :=
    hη.comp_continuous (f := fun g : Ω ≃ₐ[K] Ω =>
      (⟨σ * AlgEquiv.restrictScalarsHom F g * σ⁻¹,
        _root_.GlobalTheory.K4.TopW.conj_mem_geo σ (hmem g)⟩ : H))
      (((continuous_const.mul hres).mul continuous_const).subtype_mk _)
  let χ : (Ω ≃ₐ[K] Ω) → ZMod N := fun g =>
    _root_.GlobalTheory.KEdge.edge x y η σ (AlgEquiv.restrictScalarsHom F g)
  have hlc : IsLocallyConstant χ := by
    have hfun : χ = fun g => η (σ * AlgEquiv.restrictScalarsHom F g * σ⁻¹) -
        η (AlgEquiv.restrictScalarsHom F g) -
        Multiplicative.toAdd (x (AlgEquiv.restrictScalarsHom F g)) * Multiplicative.toAdd (y σ) +
        Multiplicative.toAdd (x σ) * Multiplicative.toAdd (y (AlgEquiv.restrictScalarsHom F g)) :=
      rfl
    rw [hfun]
    exact ((hη₂.comp₂ hη₁ (· - ·)).comp₂ (hx_lc.comp (· * Multiplicative.toAdd (y σ))) (· - ·)).comp₂
      (hy_lc.comp (Multiplicative.toAdd (x σ) * ·)) (· + ·)
  have hadd : ∀ g ∈ (⊥ : IntermediateField K Ω).fixingSubgroup,
      ∀ h ∈ (⊥ : IntermediateField K Ω).fixingSubgroup, χ (g * h) = χ g + χ h := by
    intro g _ h _
    simp only [χ, map_mul]
    exact hhom σ _ (hmem g) _ (hmem h)
  obtain ⟨θ, hθ0, hθN, hθ⟩ :=
    _root_.GlobalTheory.kummer_generator_of_char K Ω N ζ hN hζ (fun g => hfix (AlgEquiv.restrictScalarsHom F g)) ⊥ χ hlc hadd
  obtain ⟨w, hw⟩ := IntermediateField.mem_bot.mp hθN
  apply _root_.GlobalTheory.K4.TopW.isTopW_topW_of_exists
  refine ⟨w, ?_, θ, hw.symm, ?_⟩
  · rintro rfl
    rw [map_zero] at hw
    exact hθ0 ((pow_eq_zero_iff hN.ne').mp hw.symm)
  · intro g hg
    obtain ⟨g', rfl⟩ := _root_.GlobalTheory.K4.TopSpec.exists_res hg
    apply _root_.GlobalTheory.NeedB.kum_eq_of hζ hθ0
    exact hθ g' (by rw [IntermediateField.fixingSubgroup_bot]; exact Subgroup.mem_top _)
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ

theorem mono_sub_mem_of_sub_mem {R : Type} [CommRing R] (I : Ideal R) (u v : Fin 2 → R)
    (h : ∀ i, u i - v i ∈ I) (a b : ℕ) : u 0 ^ a * u 1 ^ b - v 0 ^ a * v 1 ^ b ∈ I := by
  have h0 := Ideal.Quotient.eq.2 (h 0)
  have h1 := Ideal.Quotient.eq.2 (h 1)
  rw [← Ideal.Quotient.eq]
  simp only [map_mul, map_pow, h0, h1]

theorem Tower.B_sub_mem {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (N l w : ℕ)
    [Fact l.Prime] (b : X.Fn l) (hb : b ∈ X.B N l w) (n : ℕ) (u v : Fin 2 → ℤ_[l])
    (huv : ∀ i, u i - v i ∈ (idl l) ^ n) :
    b u - b v ∈ (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l)) := by
  induction hb using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, -, hc⟩ := hx.1
    rw [hc u, hc v, ← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← sub_smul]
    exact Submodule.smul_mem_smul (mono_sub_mem_of_sub_mem _ u v huv _ _) Submodule.mem_top
  | zero => simp
  | add x y _ _ hx hy =>
    have := Submodule.add_mem _ hx hy
    simp only [Pi.add_apply]
    convert this using 1
    abel
  | smul r x _ hx =>
    simp only [Pi.smul_apply, ← smul_sub]
    exact Submodule.smul_mem _ r hx

end GlobalTheory.KZ
end
