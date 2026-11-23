module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Mathlib.NumberTheory.ModularForms.Basic
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.Artinian.Instances
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices.SsD

theorem toGL_mat (σ : SL(2, ℤ)) : toGL (mat σ) = (σ : GL (Fin 2) ℝ) := by
  have h : (mat σ).det ≠ 0 := by simp [mat]
  unfold toGL
  rw [dite_eq_right h]
  ext i j
  simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, mat]

theorem DdF_eq (k : ℤ) (σ : SL(2, ℤ)) (F : ℍ → ℂ) : DdF k σ F = F ∣[k] σ := by
  simp [DdF, hkF, toGL_mat, ModularForm.SL_slash]

theorem exists_pow_mem {G : Type*} [Group G] (H : Subgroup G) [H.FiniteIndex] (a : G) :
    ∃ m, 0 < m ∧ a ^ m ∈ H := by
  obtain ⟨i, j, hij, h⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun n : ℕ => (QuotientGroup.mk (a ^ n) : G ⧸ H))
  have h' : (a ^ i)⁻¹ * a ^ j ∈ H := QuotientGroup.eq.mp h
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · refine ⟨j - i, Nat.sub_pos_of_lt hlt, ?_⟩
    have e : a ^ (j - i) = (a ^ i)⁻¹ * a ^ j := by
      rw [eq_inv_mul_iff_mul_eq, ← pow_add, Nat.add_sub_cancel' hlt.le]
    rwa [e]
  · refine ⟨i - j, Nat.sub_pos_of_lt hlt, ?_⟩
    have e : a ^ (i - j) = (a ^ j)⁻¹ * a ^ i := by
      rw [eq_inv_mul_iff_mul_eq, ← pow_add, Nat.add_sub_cancel' hlt.le]
    rw [e]
    simpa [mul_inv_rev] using H.inv_mem h'

theorem eigen_of_pow_fix {V : Type*} [AddCommGroup V] [Module ℂ V] (D : Module.End ℂ V) {m : ℕ}
    (hm : 0 < m) (v : V) (c : ℂ) (n : ℕ) (h1 : (D ^ m) v = v)
    (h2 : ((D - c • LinearMap.id : Module.End ℂ V) ^ n) v = 0) : D v = c • v := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp at h2
    simp [h2]
  set p : ℂ[X] := X ^ m - C 1
  set q : ℂ[X] := (X - C c) ^ n
  have hp : aeval D p v = 0 := by simp [p, h1]
  have hq : aeval D q v = 0 := by
    simpa [q, Module.algebraMap_end_eq_smul_id] using h2
  have hsq : Squarefree p :=
    (separable_X_pow_sub_C (1 : ℂ) (by exact_mod_cast hm.ne') one_ne_zero).squarefree
  have hg : aeval D (EuclideanDomain.gcd p q) v = 0 := by
    rw [EuclideanDomain.gcd_eq_gcd_ab p q, mul_comm p, mul_comm q, map_add (f := _), map_mul, map_mul,
      LinearMap.add_apply, Module.End.mul_apply, Module.End.mul_apply, hp, hq, map_zero, map_zero,
      add_zero]
  have hgd : EuclideanDomain.gcd p q ∣ X - C c := by
    exact (hsq.squarefree_of_dvd (EuclideanDomain.gcd_dvd_left p q)).dvd_pow_iff_dvd hn.ne' |>.mp
      (EuclideanDomain.gcd_dvd_right p q)
  obtain ⟨r, hr⟩ := hgd
  have : aeval D (X - C c) v = 0 := by
    rw [hr, mul_comm, map_mul, Module.End.mul_apply, hg, map_zero]
  simpa [sub_eq_zero, Module.algebraMap_end_eq_smul_id] using this

noncomputable def slashEnd (k : ℤ) (σ : SL(2, ℤ)) : Module.End ℂ (ℍ → ℂ) where
  toFun F := F ∣[k] σ
  map_add' F G := SlashAction.add_slash _ _ _ _
  map_smul' c F := by simp [ModularForm.SL_smul_slash]

theorem slashEnd_pow (k : ℤ) (σ : SL(2, ℤ)) (j : ℕ) (F : ℍ → ℂ) :
    (slashEnd k σ ^ j) F = F ∣[k] (σ ^ j) := by
  induction j generalizing F with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, Module.End.mul_apply, ih, pow_succ', SlashAction.slash_mul]
    rfl

end GlobalTheory.HeckeFamilyMatrices.SsD

namespace GlobalTheory.HeckeFamilyMatrices


open GlobalTheory.HeckeFamilyMatrices.SsD in
theorem diamond_genEigen_eigen : ∀ (N l k : ℕ), 5 ≤ N → l.Prime → ¬ l ∣ N → 3 ≤ k → ∀ (d : ZMod N) (σ : SL(2, ℤ)), IsDiam N l d σ →
  ∀ (f : ModularForm (Lev N l) (k : ℤ)) (c : ℂ) (n : ℕ), (fun F => DdF (k : ℤ) σ F - c • F)^[n] ⇑f = 0 → DdF (k : ℤ) σ ⇑f = c • ⇑f := by
  intro N l k hN hl _ _ d σ _ f c n hn
  haveI : NeZero N := ⟨by omega⟩
  haveI : NeZero l := ⟨hl.ne_zero⟩
  haveI : (Lev N l).FiniteIndex := by unfold Lev; infer_instance
  obtain ⟨m, hm, hmem⟩ := exists_pow_mem (Lev N l) σ
  have hfix : (slashEnd (k : ℤ) σ ^ m) ⇑f = ⇑f := by
    rw [slashEnd_pow]
    exact SlashInvariantForm.slash_action_eqn f _ ⟨_, hmem, rfl⟩
  have hE : ⇑(slashEnd (k : ℤ) σ - c • LinearMap.id : Module.End ℂ (ℍ → ℂ)) = fun F => DdF (k : ℤ) σ F - c • F := by
    funext F
    simp [slashEnd, DdF_eq]
  have h2 : ((slashEnd (k : ℤ) σ - c • LinearMap.id : Module.End ℂ (ℍ → ℂ)) ^ n) ⇑f = 0 := by
    rw [Module.End.pow_apply, hE]
    exact hn
  have := eigen_of_pow_fix _ hm _ c n hfix h2
  simpa [slashEnd, DdF_eq] using this

end GlobalTheory.HeckeFamilyMatrices
end

section

noncomputable section

open Polynomial IntermediateField

namespace GlobalTheory.NeedB.KumLemma

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]

theorem pow_val_add {N : ℕ} [NeZero N] {ζ : Ω} (hζ : IsPrimitiveRoot ζ N) (a b : ZMod N) :
    ζ ^ (a + b).val = ζ ^ a.val * ζ ^ b.val := by
  rw [ZMod.val_add, ← pow_add]
  conv_rhs => rw [← Nat.mod_add_div (a.val + b.val) N]
  rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]

theorem exists_pow {N : ℕ} [NeZero N] {ζ θ : Ω} (hζ : IsPrimitiveRoot ζ N) (hθ : θ ≠ 0)
    (hN : θ ^ N ∈ Set.range (algebraMap K Ω)) (g : Ω ≃ₐ[K] Ω) :
    ∃ i : ZMod N, g θ = ζ ^ i.val * θ := by
  obtain ⟨c, hc⟩ := hN
  have hg : (g θ) ^ N = θ ^ N := by rw [← map_pow, ← hc, AlgEquiv.commutes]
  have h1 : (g θ / θ) ^ N = 1 := by
    rw [div_pow, hg, div_self (pow_ne_zero _ hθ)]
  obtain ⟨i, hi, hi'⟩ := hζ.eq_pow_of_pow_eq_one h1
  refine ⟨(i : ZMod N), ?_⟩
  rw [ZMod.val_cast_of_lt hi, hi', div_mul_cancel₀ _ hθ]

theorem unique_pow {N : ℕ} [NeZero N] {ζ θ : Ω} (hζ : IsPrimitiveRoot ζ N) (hθ : θ ≠ 0)
    {a b : ZMod N} (h : ζ ^ a.val * θ = ζ ^ b.val * θ) : a = b := by
  have h' : ζ ^ a.val = ζ ^ b.val := mul_right_cancel₀ hθ h
  exact ZMod.val_injective N (hζ.pow_inj (ZMod.val_lt a) (ZMod.val_lt b) h')

theorem kum_spec {N : ℕ} [NeZero N] {ζ θ : Ω} (hζ : IsPrimitiveRoot ζ N) (hθ : θ ≠ 0)
    (hN : θ ^ N ∈ Set.range (algebraMap K Ω)) (g : Ω ≃ₐ[K] Ω) :
    g θ = ζ ^ (kum (N := N) ζ θ g).val * θ := by
  have h := exists_pow hζ hθ hN g
  unfold kum
  rw [dite_eq_left h]
  exact h.choose_spec

theorem kum_eq {N : ℕ} [NeZero N] {ζ θ : Ω} (hζ : IsPrimitiveRoot ζ N) (hθ : θ ≠ 0)
    (hN : θ ^ N ∈ Set.range (algebraMap K Ω)) (g : Ω ≃ₐ[K] Ω) {i : ZMod N}
    (hi : g θ = ζ ^ i.val * θ) : kum (N := N) ζ θ g = i :=
  unique_pow hζ hθ ((kum_spec hζ hθ hN g).symm.trans hi)

theorem kum_mul {N : ℕ} [NeZero N] {ζ θ : Ω} (hζ : IsPrimitiveRoot ζ N) (hfix : ∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ)
    (hθ : θ ≠ 0) (hN : θ ^ N ∈ Set.range (algebraMap K Ω)) (g h : Ω ≃ₐ[K] Ω) :
    kum (N := N) ζ θ (g * h) = kum ζ θ g + kum ζ θ h := by
  apply kum_eq hζ hθ hN
  rw [AlgEquiv.mul_apply, kum_spec hζ hθ hN h, map_mul, map_pow, hfix, kum_spec hζ hθ hN g,
    add_comm, pow_val_add hζ]
  ring

theorem kum_eq_zero_iff {N : ℕ} [NeZero N] {ζ θ : Ω} (hζ : IsPrimitiveRoot ζ N) (hθ : θ ≠ 0)
    (hN : θ ^ N ∈ Set.range (algebraMap K Ω)) (g : Ω ≃ₐ[K] Ω) :
    kum (N := N) ζ θ g = 0 ↔ g θ = θ := by
  constructor
  · intro h
    have := kum_spec hζ hθ hN g
    rwa [h, ZMod.val_zero, pow_zero, one_mul] at this
  · intro h
    apply kum_eq hζ hθ hN
    rw [h, ZMod.val_zero, pow_zero, one_mul]

theorem kummer_character [Algebra.IsAlgebraic K Ω] (N : ℕ) (ζ θ : Ω) (hN0 : 0 < N)
    (hζ : IsPrimitiveRoot ζ N) (hfix : ∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ) (hθ : θ ≠ 0)
    (hN : θ ^ N ∈ Set.range (algebraMap K Ω)) :
    IsLocallyConstant (kum (N := N) (K := K) ζ θ) ∧ (∀ g : Ω ≃ₐ[K] Ω, g θ = ζ ^ (kum (N := N) ζ θ g).val * θ) ∧
    (∀ g h : Ω ≃ₐ[K] Ω, kum (N := N) ζ θ (g * h) = kum ζ θ g + kum ζ θ h) ∧
    (∀ g : Ω ≃ₐ[K] Ω, kum (N := N) ζ θ g = 0 ↔ g θ = θ) := by
  haveI : NeZero N := ⟨by omega⟩
  refine ⟨?_, kum_spec hζ hθ hN, kum_mul hζ hfix hθ hN, kum_eq_zero_iff hζ hθ hN⟩
  rw [IsLocallyConstant.iff_exists_open]
  intro g
  haveI : FiniteDimensional K K⟮θ⟯ :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral θ)
  have hopen : IsOpen ((K⟮θ⟯).fixingSubgroup : Set (Ω ≃ₐ[K] Ω)) :=
    IntermediateField.fixingSubgroup_isOpen _
  refine ⟨(fun g' => g⁻¹ * g') ⁻¹' ((K⟮θ⟯).fixingSubgroup : Set (Ω ≃ₐ[K] Ω)),
    hopen.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simp only [Set.mem_preimage, inv_mul_cancel, SetLike.mem_coe]
    exact Subgroup.one_mem _
  · intro g' hg'
    have hfθ : (g⁻¹ * g') θ = θ := by
      have := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg' θ
        (IntermediateField.mem_adjoin_simple_self K θ)
      exact this
    have h0 := (kum_eq_zero_iff hζ hθ hN _).2 hfθ
    have : g' = g * (g⁻¹ * g') := by group
    rw [this, kum_mul hζ hfix hθ hN, h0, add_zero]

end GlobalTheory.NeedB.KumLemma


open GlobalTheory.NeedB in
theorem GlobalTheory.NeedB.KumLemma.kummer_character_main : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] (N : ℕ) (ζ θ : Ω), 0 < N →
  IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ) → θ ≠ 0 → θ ^ N ∈ Set.range (algebraMap K Ω) →
  IsLocallyConstant (kum (N := N) (K := K) ζ θ) ∧ (∀ g : Ω ≃ₐ[K] Ω, g θ = ζ ^ (kum (N := N) ζ θ g).val * θ) ∧
  (∀ g h : Ω ≃ₐ[K] Ω, kum (N := N) ζ θ (g * h) = kum ζ θ g + kum ζ θ h) ∧ (∀ g : Ω ≃ₐ[K] Ω, kum (N := N) ζ θ g = 0 ↔ g θ = θ) :=
  fun K Ω _ _ _ _ N ζ θ h0 hζ hf hθ hN => GlobalTheory.NeedB.KumLemma.kummer_character N ζ θ h0 hζ hf hθ hN
end
end

section

open GlobalTheory.NeedB Polynomial

namespace GlobalTheory

theorem inert_fixes_root_of_unit_ratio (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (B : ValuationSubring Ω)
    (g : Ω ≃ₐ[K] Ω) (N : ℕ) (c θ : Ω) :
    0 < N → B.valuation (N : Ω) = 1 → Inert B g → g c = c → c ≠ 0 → g (θ ^ N) = θ ^ N →
      B.valuation (θ ^ N / c ^ N) = 1 → g θ = θ := by
  intro hN hvN hin hgc hc hgθ hvθ
  set v := B.valuation
  by_cases hθ : θ = 0
  · simp [hθ]
  set u := θ / c with hu
  have hu0 : u ≠ 0 := div_ne_zero hθ hc
  have hvu : v u = 1 := by
    have h1 : v u ^ N = 1 := by rw [← map_pow, hu, div_pow]; exact hvθ
    exact (pow_eq_one_iff_left (Nat.pos_iff_ne_zero.mp hN)).mp h1
  have hgu : g u = g θ / c := by rw [hu, map_div₀, hgc]
  have hguN : (g u) ^ N = u ^ N := by
    rw [← map_pow, hu, div_pow, map_div₀, map_pow g c, hgc, hgθ]
  set ξ := g u / u with hξ
  have hξN : ξ ^ N = 1 := by rw [hξ, div_pow, hguN, div_self (pow_ne_zero _ hu0)]
  have hvξ1 : v (ξ - 1) < 1 := by
    have h2 : ξ - 1 = (g u - u) / u := by rw [hξ, sub_div, div_self hu0]
    rw [h2, map_div₀, hvu, div_one]
    exact hin u hvu.le
  have hvξ : v ξ ≤ 1 := by
    have : ξ = (ξ - 1) + 1 := by ring
    rw [this]
    exact (Valuation.map_add v _ _).trans (max_le hvξ1.le (by simp))
  have hpow : ∀ j : ℕ, v (ξ ^ j - 1) < 1 := by
    intro j
    have h3 : ξ ^ j - 1 = (∑ i ∈ Finset.range j, ξ ^ i) * (ξ - 1) := (geom_sum_mul ξ j).symm
    rw [h3, map_mul]
    have h4 : v (∑ i ∈ Finset.range j, ξ ^ i) ≤ 1 :=
      Valuation.map_sum_le v (fun i _ => by rw [map_pow]; exact pow_le_one' hvξ i)
    calc v (∑ i ∈ Finset.range j, ξ ^ i) * v (ξ - 1) ≤ 1 * v (ξ - 1) := mul_le_mul_left h4 _
      _ = v (ξ - 1) := one_mul _
      _ < 1 := hvξ1
  set S := ∑ i ∈ Finset.range N, ξ ^ i with hS
  have hSN : S - (N : Ω) = ∑ i ∈ Finset.range N, (ξ ^ i - 1) := by
    rw [hS, Finset.sum_sub_distrib]; simp
  have hvSN : v (S - (N : Ω)) < 1 := by
    rw [hSN]; exact Valuation.map_sum_lt v one_ne_zero (fun i _ => hpow i)
  have hS0 : S ≠ 0 := by
    intro h0
    rw [h0, zero_sub, Valuation.map_neg, hvN] at hvSN
    exact lt_irrefl _ hvSN
  have hmul : S * (ξ - 1) = 0 := by rw [hS, geom_sum_mul, hξN, sub_self]
  have hξ1 : ξ = 1 := by
    rcases mul_eq_zero.mp hmul with h | h
    · exact absurd h hS0
    · exact sub_eq_zero.mp h
  have : g u = u := by
    rw [hξ, div_eq_one_iff_eq hu0] at hξ1; exact hξ1
  rw [hgu, hu] at this
  exact (div_left_inj' hc).mp this

end GlobalTheory
end

section

open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem exists_normal_finiteIndex_fixing (L : Type) [Field L] (G : Type) [Group G]
    [MulSemiringAction G L] (S : Finset L) (hS : ∀ s ∈ S, (MulAction.orbit G s).Finite) :
    ∃ U : Subgroup G, U.Normal ∧ U.FiniteIndex ∧ (∀ s ∈ S, s ∈ Fix L U) ∧
      ∀ h : G, h ∉ U → ∃ x ∈ Fix L U, h • x ≠ x := by
  classical
  set T : Set L := ⋃ s ∈ S, MulAction.orbit G s with hT
  have hTfin : T.Finite := Set.Finite.biUnion S.finite_toSet (fun s hs => hS s hs)
  have hTstab : ∀ g : G, ∀ x ∈ T, g • x ∈ T := by
    intro g x hx
    simp only [hT, Set.mem_iUnion] at hx ⊢
    obtain ⟨s, hs, hx⟩ := hx
    exact ⟨s, hs, MulAction.mem_orbit_of_mem_orbit g hx⟩
  set F : Finset L := hTfin.toFinset
  have hF : ∀ x, x ∈ F ↔ x ∈ T := fun x => hTfin.mem_toFinset
  let U : Subgroup G := ⨅ x ∈ F, MulAction.stabilizer G x
  have hU : ∀ g : G, g ∈ U ↔ ∀ x ∈ T, g • x = x := by
    intro g
    simp only [U, Subgroup.mem_iInf, MulAction.mem_stabilizer_iff, hF]
  have hST : ∀ s ∈ S, s ∈ T := by
    intro s hs
    simp only [hT, Set.mem_iUnion]
    exact ⟨s, hs, MulAction.mem_orbit_self s⟩
  have hFix : ∀ x ∈ T, x ∈ Fix L U := by
    intro x hx
    change ∀ m : U, m • x = x
    rintro ⟨g, hg⟩
    exact (hU g).1 hg x hx
  refine ⟨U, ?_, ?_, fun s hs => hFix s (hST s hs), ?_⟩
  · refine ⟨fun n hn g => ?_⟩
    rw [hU] at hn ⊢
    intro x hx
    have := hn (g⁻¹ • x) (hTstab g⁻¹ x hx)
    rw [mul_smul, mul_smul, this, smul_inv_smul]
  · refine Subgroup.finiteIndex_iInf' _ (fun x hx => ?_)
    refine ⟨?_⟩
    rw [MulAction.index_stabilizer]
    have hx' := (hF x).1 hx
    simp only [hT, Set.mem_iUnion] at hx'
    obtain ⟨s, hs, hxs⟩ := hx'
    rw [MulAction.orbit_eq_iff.mpr hxs]
    exact (Set.ncard_pos (hS s hs)).mpr ⟨s, MulAction.mem_orbit_self s⟩ |>.ne'
  · intro h hh
    rw [hU] at hh
    push_neg at hh
    obtain ⟨x, hx, hne⟩ := hh
    exact ⟨x, hFix x hx, hne⟩

end GlobalTheory.AlmostEt
end

section

open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem exists_reps_of_cosetTrace : ∀ (L : Type) [Field L] (G : Type) [Group G] [MulSemiringAction G L]
    (U : Subgroup G) [Fintype (G ⧸ U)] (S : Finset L), (∀ s ∈ S, s ∈ Fix L U) → ∀ y₀ ∈ Fix L U,
    ∃ (y : L) (D E : Finset G), y = ∑ d ∈ D, d • y₀ ∧
      (∀ h : G, ∃! g, g ∈ E ∧ h • y = g • y ∧ ∀ s ∈ S, h • s = g • s) ∧
      ∑ g ∈ E, g • y = cosetTrace U y₀ := by
  intro L _ G _ _ U _ S hS y₀ hy₀
  classical
  set V : Subgroup G := fixingSubgroup G (S : Set L) with hV
  have hUV : U ≤ V := by
    intro u hu
    rw [hV, mem_fixingSubgroup_iff]
    intro s hs
    exact hS s hs ⟨u, hu⟩
  have hy0 : ∀ a b : G, (a : G ⧸ U) = b → a • y₀ = b • y₀ := by
    intro a b hab
    rw [QuotientGroup.eq] at hab
    have h1 : (a⁻¹ * b) • y₀ = y₀ := hy₀ ⟨_, hab⟩
    calc a • y₀ = a • ((a⁻¹ * b) • y₀) := by rw [h1]
      _ = b • y₀ := by rw [smul_smul, mul_inv_cancel_left]
  set f : G ⧸ U → L := fun q => q.out • y₀ with hf
  have hfmk : ∀ g : G, f (g : G ⧸ U) = g • y₀ := fun g => hy0 _ _ (QuotientGroup.out_eq' _)
  have hfeq : ∀ (g : G) (q : G ⧸ U), f (g • q) = g • f q := by
    intro g q
    induction q using QuotientGroup.induction_on with
    | H a =>
      show f ((g * a : G) : G ⧸ U) = g • f (a : G ⧸ U)
      rw [hfmk, hfmk, mul_smul]
  let π : G ⧸ U → G ⧸ V := Subgroup.quotientMapOfLE hUV
  have hπmk : ∀ g : G, π (g : G ⧸ U) = (g : G ⧸ V) := fun g => rfl
  have hπeq : ∀ (g : G) (q : G ⧸ U), π (g • q) = g • π q := by
    intro g q
    induction q using QuotientGroup.induction_on with
    | H a => rw [MulAction.Quotient.smul_mk, hπmk, hπmk, MulAction.Quotient.smul_mk]
  have hV1 : ∀ g : G, (g : G ⧸ V) = ((1 : G) : G ⧸ V) ↔ g ∈ V := by
    intro g
    rw [QuotientGroup.eq, mul_one, inv_mem_iff]
  haveI : Finite (G ⧸ V) := Finite.of_surjective π (by
    intro c
    induction c using QuotientGroup.induction_on with
    | H a => exact ⟨(a : G ⧸ U), rfl⟩)
  letI : Fintype (G ⧸ V) := Fintype.ofFinite _
  set F : Finset (G ⧸ U) := Finset.univ.filter (fun q => π q = ((1 : G) : G ⧸ V)) with hF
  have hout : ∀ {H : Subgroup G} (a b : G ⧸ H), a.out = b.out → a = b := by
    intro H a b hab
    rw [← QuotientGroup.out_eq' a, ← QuotientGroup.out_eq' b, hab]

  have hyV : ∀ v ∈ V, v • (∑ q ∈ F, f q) = ∑ q ∈ F, f q := by
    intro v hv
    rw [Finset.smul_sum]
    symm
    refine Finset.sum_nbij' (fun q => v⁻¹ • q) (fun q => v • q) ?_ ?_ ?_ ?_ ?_
    · intro q hq
      simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      rw [hπeq, hq, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, hV1]
      exact V.inv_mem hv
    · intro q hq
      simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      rw [hπeq, hq, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, hV1]
      exact hv
    · intro q _
      simp only [smul_inv_smul]
    · intro q _
      simp only [inv_smul_smul]
    · intro q _
      rw [hfeq, smul_inv_smul]
  refine ⟨∑ q ∈ F, f q, F.image Quotient.out, (Finset.univ : Finset (G ⧸ V)).image Quotient.out, ?_, ?_, ?_⟩
  · rw [Finset.sum_image (fun a _ b _ hab => hout a b hab)]
  · intro h
    have hgh : (h : G ⧸ V).out⁻¹ * h ∈ V := QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
    refine ⟨(h : G ⧸ V).out, ⟨Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, ?_, ?_⟩, ?_⟩
    · conv_lhs => rw [← mul_inv_cancel_left (h : G ⧸ V).out h]
      rw [← smul_smul, hyV _ hgh]
    · intro s hs
      have h2 : ((h : G ⧸ V).out⁻¹ * h) • s = s := (mem_fixingSubgroup_iff G).1 hgh s hs
      conv_lhs => rw [← mul_inv_cancel_left (h : G ⧸ V).out h]
      rw [← smul_smul, h2]
    · rintro g' ⟨hg'E, _, hg'S⟩
      obtain ⟨c, _, rfl⟩ := Finset.mem_image.1 hg'E
      have h3 : c.out⁻¹ * h ∈ V := (mem_fixingSubgroup_iff G).2 (fun s hs => by
        rw [← smul_smul, hg'S s hs, inv_smul_smul])
      have h4 : (c.out : G ⧸ V) = (h : G ⧸ V) := QuotientGroup.eq.2 h3
      rw [QuotientGroup.out_eq'] at h4
      rw [h4]
  · rw [Finset.sum_image (fun a _ b _ hab => hout a b hab)]
    unfold cosetTrace
    change _ = ∑ q : G ⧸ U, f q
    rw [← Finset.sum_fiberwise Finset.univ π f]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Finset.smul_sum]
    have key : ∀ g : G, g⁻¹ • (g : G ⧸ V) = ((1 : G) : G ⧸ V) := fun g => by
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, inv_mul_cancel]
    refine Finset.sum_nbij' (fun q => c.out • q) (fun q => c.out⁻¹ • q) ?_ ?_ ?_ ?_ ?_
    · intro q hq
      simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      rw [hπeq, hq, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.out_eq']
    · intro q hq
      simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      rw [hπeq, hq]
      have h5 := key c.out
      rwa [QuotientGroup.out_eq'] at h5
    · intro q _
      simp only [inv_smul_smul]
    · intro q _
      simp only [smul_inv_smul]
    · intro q _
      rw [hfeq]

end GlobalTheory.AlmostEt
end
