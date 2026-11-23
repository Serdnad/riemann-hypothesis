module

public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle206
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemOfForallAnnihilatorAnnihilatorFieldModInteger
public import GroundTheory.LocalFields.Different
public import GroundTheory.LocalFields.IntermediateField
public import GroundTheory.LocalFields.Bundle004
public import Mathlib.FieldTheory.Galois.Basic
public import GroundTheory.LocalFields.Bundle007
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Tactic.ToDual
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Padics.LocalField
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Valuation.Integral
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Nonarchimedean.Completion
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle007
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import GroundTheory.LocalFields.Interface
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Data.Nat.Find
import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.exists_integral_dual_functional : ∀ (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL]
    (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O →
    ∃ (lam : LL →ₗ[ℚ_[l]] ℚ_[l]) (n : ℕ) (e f : Fin n → O),
      (∀ z : ℤ_[l], ∃ o : O, algebraMap O LL o = algebraMap ℚ_[l] LL (z : ℚ_[l])) ∧
      (∀ o : O, ∃ z : ℤ_[l], lam (algebraMap O LL o) = (z : ℚ_[l])) ∧
      (∀ x : LL, x = ∑ i, lam (algebraMap O LL (f i) * x) • algebraMap O LL (e i)) := by
  first | exact @GlobalTheory.IntDual.intDual_coef | exact GlobalTheory.IntDual.intDual_coef | (intros; apply GlobalTheory.IntDual.intDual_coef <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.goodCoefficients_explicit_sums : ∀ (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → (∀ x : ℕ → O, ∃ a : O, ∀ n : ℕ, ∃ b : O, a - ∑ j ∈ Finset.range n, ((l : ℕ) : O) ^ j * x j = ((l : ℕ) : O) ^ n * b) ∧ (∀ a : O, (∀ n : ℕ, ∃ b : O, a = ((l : ℕ) : O) ^ n * b) → a = 0) := by
  first | exact @GlobalTheory.goodO_coeff_explicit_sums | exact GlobalTheory.goodO_coeff_explicit_sums | (intros; apply GlobalTheory.goodO_coeff_explicit_sums <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.mem_of_forall_annihilator_annihilator_fieldModIntegers : ∀ (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (M N : Type) [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N] [Module.Finite O M] (β : M →ₗ[O] N →ₗ[O] (LL ⧸ LinearMap.range (Algebra.linearMap O LL))) (S : Submodule O N), (∀ c, (∀ d, β d c = 0) → c ∈ S) → ∀ c, (∀ d, (∀ s ∈ S, β d s = 0) → β d c = 0) → c ∈ S := by
  first | exact @GlobalTheory.mem_of_forall_annihilator_annihilator | exact GlobalTheory.mem_of_forall_annihilator_annihilator | (intros; apply GlobalTheory.mem_of_forall_annihilator_annihilator <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem exists_mem_maximalIdeal_pow_eq_trace_of_le_differentExponent :
    ∀ (F M : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M] [Algebra F M] [ValuativeExtension F M] [FiniteDimensional F M] [IsGalois F M] (n : ℕ), (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation M))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation F))) * n ≤ differentExponent F M → ∀ z : 𝒪[M], ∃ w ∈ 𝓂[F] ^ n, ((w : 𝒪[F]) : F) = Algebra.trace F M (z : M) := by
  intro F M _ _ _ _ _ _ _ _ _ _ _ _ n hn z
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  have hϖ0 : (ϖ : F) ≠ 0 := by
    have : ϖ ≠ 0 := hϖ.ne_zero
    exact_mod_cast this
  set I : Ideal 𝒪[M] := Ideal.span {algebraMap 𝒪[F] 𝒪[M] (ϖ ^ n)} with hI
  have hImap : I = (𝓂[F] ^ n).map (algebraMap 𝒪[F] 𝒪[M]) := by
    rw [hI, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton]
  have hIeq : I = 𝓂[M] ^ ((_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation M))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation F))) * n) := by
    rw [hImap, Ideal.map_pow, map_maximalIdeal, pow_mul]
  have hle : differentIdeal 𝒪[F] 𝒪[M] ≤ I := by
    rw [differentIdeal_eq_maximalIdeal_pow, hIeq]
    exact Ideal.pow_le_pow_right hn
  have hIne : I ≠ ⊥ := by
    rw [hI, ne_eq, Ideal.span_singleton_eq_bot]
    intro h
    have : ((algebraMap 𝒪[F] 𝒪[M] (ϖ ^ n) : 𝒪[M]) : M) = 0 := by rw [h]; rfl
    rw [coe_algebraMap_integer] at this
    rw [SubmonoidClass.coe_pow, map_pow] at this
    exact pow_ne_zero n ((_root_.map_ne_zero _).mpr hϖ0) this
  have key := (differentialIdeal_le_iff (K := F) (L := M) hIne).mp hle
  set x : M := algebraMap F M ((ϖ : F) ^ n) with hx
  have hx0 : x ≠ 0 := by
    rw [hx]; exact (_root_.map_ne_zero _).mpr (pow_ne_zero _ hϖ0)
  have hIfrac : ((I : FractionalIdeal (nonZeroDivisors 𝒪[M]) M)) = FractionalIdeal.spanSingleton (nonZeroDivisors 𝒪[M]) x := by
    rw [hI, FractionalIdeal.coeIdeal_span_singleton]
    congr 1
  have hmem : x⁻¹ * (z : M) ∈ (((I⁻¹ : FractionalIdeal (nonZeroDivisors 𝒪[M]) M) : Submodule 𝒪[M] M)) := by
    rw [hIfrac, FractionalIdeal.spanSingleton_inv, FractionalIdeal.mem_coe,
      FractionalIdeal.mem_spanSingleton]
    exact ⟨z, by rw [Algebra.smul_def, mul_comm]; rfl⟩
  have htr : Algebra.trace F M (x⁻¹ * (z : M)) ∈ (1 : Submodule 𝒪[F] F) :=
    key ⟨_, hmem, rfl⟩
  obtain ⟨a, ha⟩ := Submodule.mem_one.mp htr
  refine ⟨ϖ ^ n * a, Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (hϖ.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self ϖ) n), ?_⟩
  have hz : (z : M) = x * (x⁻¹ * (z : M)) := by rw [← mul_assoc, mul_inv_cancel₀ hx0, one_mul]
  rw [hz, hx, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]
  simp only [Subring.coe_mul, SubmonoidClass.coe_pow]
  rw [← ha]
  rfl

end GlobalTheory.PMon.Ram
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem baseChange_fixedField :
    ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L] (A : Subgroup (L ≃ₐ[K] L)), ∃ j : (L ≃ₐ[↥(IntermediateField.fixedField A)] L) →* (L ≃ₐ[K] L), Function.Injective j ∧ j.range = A ∧ (∀ σ x, j σ x = σ x) ∧ ∀ i : ℤ, lowerRamificationGroup ↥(IntermediateField.fixedField A) L i = (lowerRamificationGroup K L i).comap j := by
  intro K L _ _ _ _ _ _ _ _ _ _ _ _ A
  refine ⟨AlgEquiv.restrictScalarsHom K, AlgEquiv.restrictScalarsHom_injective K, ?_, ?_, ?_⟩
  · rw [GroundTheory.LocalField.range_restrictScalarsHom, IntermediateField.fixingSubgroup_fixedField]
  · intro σ x
    rfl
  · intro i
    exact (lowerRamificationGroup_comap_restrictScalars (IntermediateField.fixedField A) i).symm

end GlobalTheory.PMon.Ram
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem doublingArith_step (V : ℕ → ℕ → ℕ) (E k : ℕ) (hE : 0 < E)
    (h1 : ∀ j, 1 ≤ j → j + 1 ≤ 8 → min (2 * V k (k + j)) (V k (k + j) + E) ≤ V k (k + j + 1))
    (h2 : V k (k + 8) ≤ 6 * E)
    (h3 : V k (k + 3) ≤ V k (k + 2) + V (k + 2) (k + 3)) :
    V k (k + 1) < E ∧ 2 * V k (k + 1) ≤ V (k + 2) (k + 3) := by
  have e1 := h1 1 le_rfl (by norm_num)
  have e2 := h1 2 (by norm_num) (by norm_num)
  have e3 := h1 3 (by norm_num) (by norm_num)
  have e4 := h1 4 (by norm_num) (by norm_num)
  have e5 := h1 5 (by norm_num) (by norm_num)
  have e6 := h1 6 (by norm_num) (by norm_num)
  have e7 := h1 7 (by norm_num) (by norm_num)
  rw [show k + 1 + 1 = k + 2 by ring] at e1
  rw [show k + 2 + 1 = k + 3 by ring] at e2
  rw [show k + 3 + 1 = k + 4 by ring] at e3
  rw [show k + 4 + 1 = k + 5 by ring] at e4
  rw [show k + 5 + 1 = k + 6 by ring] at e5
  rw [show k + 6 + 1 = k + 7 by ring] at e6
  rw [show k + 7 + 1 = k + 8 by ring] at e7
  rw [min_le_iff] at e1 e2 e3 e4 e5 e6 e7
  omega

theorem doublingArith : ∀ (V : ℕ → ℕ → ℕ) (E T g : ℕ), 0 < E →
    (∀ k ≤ 2 * T, ∀ j, 1 ≤ j → j + 1 ≤ 8 → min (2 * V k (k + j)) (V k (k + j) + E) ≤ V k (k + j + 1)) →
    (∀ k ≤ 2 * T, V k (k + 8) ≤ 6 * E) →
    (∀ k, V k (k + 3) ≤ V k (k + 2) + V (k + 2) (k + 3)) → g ≤ V 0 1 → 2 ^ T * g < E := by
  intro V E T g hE h1 h2 h3 hg
  have step : ∀ k, k ≤ 2 * T → V k (k + 1) < E ∧ 2 * V k (k + 1) ≤ V (k + 2) (k + 3) :=
    fun k hk => doublingArith_step V E k hE (h1 k hk) (h2 k hk) (h3 k)
  have ind : ∀ i, i ≤ T → 2 ^ i * g ≤ V (2 * i) (2 * i + 1) := by
    intro i
    induction i with
    | zero => intro _; simpa using hg
    | succ n ih =>
      intro hn
      have hs := (step (2 * n) (by omega)).2
      have ih' := ih (by omega)
      rw [show 2 * (n + 1) = 2 * n + 2 by ring, show 2 * n + 2 + 1 = 2 * n + 3 by ring, pow_succ]
      calc 2 ^ n * 2 * g = 2 * (2 ^ n * g) := by ring
        _ ≤ 2 * V (2 * n) (2 * n + 1) := Nat.mul_le_mul_left 2 ih'
        _ ≤ V (2 * n + 2) (2 * n + 3) := hs
  exact lt_of_le_of_lt (ind T le_rfl) (step (2 * T) le_rfl).1

end GlobalTheory.PMon.Ram
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem exists_initialSegment_not_inf_le :
    ∀ (G : Type) [Group G] (R : ℕ → Subgroup G) (A B : Subgroup G), Antitone R →
      (∃ m, R m = ⊥) → ∃ n : ℕ, ∀ t, t < n ↔ ¬ A ⊓ R t ≤ B := by
  intro G _ R A B hR hm
  classical
  obtain ⟨m, hm⟩ := hm
  have h : ∃ t, A ⊓ R t ≤ B := ⟨m, by rw [hm]; simp⟩
  refine ⟨Nat.find h, fun t => ⟨fun ht => Nat.find_min h ht, fun hn => ?_⟩⟩
  by_contra hc
  push_neg at hc
  exact hn (le_trans (inf_le_inf_left A (hR hc)) (Nat.find_spec h))

end GlobalTheory.PMon.Ram
end

section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PMonE.OrthBasis

private lemma exists_orthogonal_translate (l : ℕ) [Fact l.Prime] (W : Submodule ℚ_[l] ℂ_[l])
    [FiniteDimensional ℚ_[l] W] (x : ℂ_[l]) (hx : x ∉ W) :
    ∃ y : ℂ_[l], y - x ∈ W ∧ y ≠ 0 ∧ ∀ w ∈ W, ‖y‖ ≤ ‖y + w‖ ∧ ‖w‖ ≤ ‖y + w‖ := by
  haveI : ProperSpace W := FiniteDimensional.proper ℚ_[l] W
  obtain ⟨w₀, hw₀K, hmin⟩ := (isCompact_closedBall (0 : W) ‖x‖).exists_isMinOn
    ⟨0, Metric.mem_closedBall_self (norm_nonneg x)⟩
    (Continuous.continuousOn (f := fun w : W => ‖x - (w : ℂ_[l])‖) (by fun_prop))
  have h0 : ‖x - (w₀ : ℂ_[l])‖ ≤ ‖x‖ := by
    simpa using hmin (Metric.mem_closedBall_self (norm_nonneg x) : (0 : W) ∈ _)
  have hglob : ∀ w : W, ‖x - (w₀ : ℂ_[l])‖ ≤ ‖x - (w : ℂ_[l])‖ := by
    intro w
    by_cases hw : w ∈ Metric.closedBall (0 : W) ‖x‖
    · exact hmin hw
    · have hlt : ‖x‖ < ‖(w : ℂ_[l])‖ := by simpa using hw
      have h1 : ‖x - (w : ℂ_[l])‖ = ‖(w : ℂ_[l])‖ := by
        rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_neg]; exact hlt.ne),
          norm_neg, max_eq_right hlt.le]
      rw [h1]; exact h0.trans hlt.le
  refine ⟨x - w₀, by simpa using W.neg_mem w₀.2, ?_, fun w hw => ⟨?_, ?_⟩⟩
  · intro h
    exact hx (by rw [sub_eq_zero.1 h]; exact w₀.2)
  · have := hglob ⟨w₀ - w, W.sub_mem w₀.2 hw⟩
    simpa [sub_sub_eq_add_sub, sub_add_eq_add_sub, add_sub_assoc] using this
  · have h1 := hglob ⟨w₀ - w, W.sub_mem w₀.2 hw⟩
    have h2 : w = (x - w₀ + w) + -(x - w₀) := by abel
    calc ‖w‖ = ‖(x - w₀ + w) + -(x - w₀)‖ := by rw [← h2]
      _ ≤ max ‖x - w₀ + w‖ ‖-(x - w₀)‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ ‖x - w₀ + w‖ := by
        rw [norm_neg]
        refine max_le le_rfl ?_
        have : x - (↑(⟨w₀ - w, W.sub_mem w₀.2 hw⟩ : W) : ℂ_[l]) = x - w₀ + w := by simp; abel
        rw [← this]; exact h1

private lemma exists_orthogonal_family_in_span (l : ℕ) [Fact l.Prime] :
    ∀ (n : ℕ) (μ : Fin n → ℂ_[l]), LinearIndependent ℚ_[l] μ →
      ∃ u : Fin n → ℂ_[l], (∀ i, u i ∈ Submodule.span ℚ_[l] (Set.range μ)) ∧ (∀ i, u i ≠ 0) ∧
        ∀ (c : Fin n → ℚ_[l]) (j : Fin n),
          ‖c j‖ * ‖u j‖ ≤ ‖∑ i, algebraMap ℚ_[l] ℂ_[l] (c i) * u i‖ := by
  intro n
  induction n with
  | zero => intro μ _; exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun _ j => j.elim0⟩
  | succ n ih =>
    intro μ hμ
    rw [← Fin.snoc_init_self μ, linearIndependent_finSnoc] at hμ
    obtain ⟨hμ₀, hx⟩ := hμ
    obtain ⟨u₀, hu₀S, hu₀, horth⟩ := ih _ hμ₀
    set W := Submodule.span ℚ_[l] (Set.range (Fin.init μ))
    haveI : FiniteDimensional ℚ_[l] W :=
      FiniteDimensional.span_of_finite ℚ_[l] (Set.finite_range _)
    obtain ⟨y, hyx, hy0, hy⟩ := exists_orthogonal_translate l W _ hx
    have hWS : W ≤ Submodule.span ℚ_[l] (Set.range μ) := by
      apply Submodule.span_mono
      rintro _ ⟨i, rfl⟩
      exact ⟨i.castSucc, rfl⟩
    have hxS : μ (Fin.last n) ∈ Submodule.span ℚ_[l] (Set.range μ) :=
      Submodule.subset_span ⟨_, rfl⟩
    refine ⟨Fin.snoc (α := fun _ => ℂ_[l]) u₀ y, fun i => ?_, fun i => ?_, fun c j => ?_⟩
    · refine Fin.lastCases ?_ (fun k => ?_) i
      · simp only [Fin.snoc_last]
        have : y = μ (Fin.last n) + (y - μ (Fin.last n)) := by abel
        rw [this]; exact Submodule.add_mem _ hxS (hWS hyx)
      · simp only [Fin.snoc_castSucc]; exact hWS (hu₀S k)
    · refine Fin.lastCases ?_ (fun k => ?_) i
      · simpa using hy0
      · simpa using hu₀ k
    · rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      set w := ∑ i : Fin n, algebraMap ℚ_[l] ℂ_[l] (c i.castSucc) * u₀ i
      have hw : w ∈ W := Submodule.sum_mem _ fun i _ => by
        rw [← Algebra.smul_def]; exact Submodule.smul_mem _ _ (hu₀S i)
      have key : ‖c (Fin.last n)‖ * ‖y‖ ≤ ‖w + algebraMap ℚ_[l] ℂ_[l] (c (Fin.last n)) * y‖ ∧
          ‖w‖ ≤ ‖w + algebraMap ℚ_[l] ℂ_[l] (c (Fin.last n)) * y‖ := by
        by_cases hc : c (Fin.last n) = 0
        · simp [hc]
        · set a := algebraMap ℚ_[l] ℂ_[l] (c (Fin.last n))
          have hna : ‖a‖ = ‖c (Fin.last n)‖ := norm_algebraMap' ℂ_[l] _
          have ha : a ≠ 0 := by
            intro h; apply hc; rw [← norm_eq_zero, ← hna, h, norm_zero]
          have hw' : a⁻¹ * w ∈ W := by
            rw [show a⁻¹ = algebraMap ℚ_[l] ℂ_[l] (c (Fin.last n))⁻¹ by simp [a],
              ← Algebra.smul_def]
            exact Submodule.smul_mem _ _ hw
          obtain ⟨h1, h2⟩ := hy _ hw'
          have e : w + a * y = a * (y + a⁻¹ * w) := by field_simp; ring
          rw [e, norm_mul, hna]
          refine ⟨mul_le_mul_of_nonneg_left h1 (norm_nonneg _), ?_⟩
          have : ‖w‖ = ‖c (Fin.last n)‖ * ‖a⁻¹ * w‖ := by
            rw [norm_mul, norm_inv, hna, ← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.2 hc),
              one_mul]
          rw [this]; exact mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      refine Fin.lastCases ?_ (fun k => ?_) j
      · simpa using key.1
      · simp only [Fin.snoc_castSucc]
        exact (horth (fun i => c i.castSucc) k).trans key.2

private lemma exists_rescale_norm_mem_Ioc (l : ℕ) [Fact l.Prime] (x : ℂ_[l]) (hx : x ≠ 0) :
    ∃ t : ℚ_[l], t ≠ 0 ∧ (l : ℝ)⁻¹ < ‖algebraMap ℚ_[l] ℂ_[l] t * x‖ ∧
      ‖algebraMap ℚ_[l] ℂ_[l] t * x‖ ≤ 1 := by
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hlpos : (0 : ℝ) < l := zero_lt_one.trans hl
  obtain ⟨n, h1, h2⟩ := exists_mem_Ioc_zpow (norm_pos_iff.2 hx) hl
  have hN : ‖algebraMap ℚ_[l] ℂ_[l] ((l : ℚ_[l]) ^ (n + 1)) * x‖ = ‖x‖ / (l : ℝ) ^ (n + 1) := by
    rw [norm_mul, norm_algebraMap', norm_zpow, Padic.norm_p, inv_zpow, div_eq_inv_mul]
  refine ⟨(l : ℚ_[l]) ^ (n + 1), zpow_ne_zero _ (by exact_mod_cast (Fact.out : l.Prime).ne_zero),
    ?_, ?_⟩
  · rw [hN, lt_div_iff₀ (zpow_pos hlpos _), zpow_add_one₀ hlpos.ne', mul_comm _ (l : ℝ), ← mul_assoc,
      inv_mul_cancel₀ hlpos.ne', one_mul]
    exact h1
  · rw [hN, div_le_one (zpow_pos hlpos _)]
    exact h2

private lemma exists_sorted_orthogonal_family_in_span (l : ℕ) [Fact l.Prime] (h : ℕ) (μ : Fin h → ℂ_[l])
    (hμ : LinearIndependent ℚ_[l] μ) :
    ∃ v : Fin h → ℂ_[l], (∀ i, v i ∈ Submodule.span ℚ_[l] (Set.range μ)) ∧
      (∀ i, v i ≠ 0 ∧ ‖v i‖ ≤ 1) ∧ (∀ i, (l : ℝ)⁻¹ < ‖v i‖) ∧ Antitone (fun i => ‖v i‖) ∧
      ∀ (c : Fin h → ℚ_[l]) (j : Fin h),
        ‖c j‖ * ‖v j‖ ≤ ‖∑ i, algebraMap ℚ_[l] ℂ_[l] (c i) * v i‖ := by
  obtain ⟨u, huS, hu0, horth⟩ := exists_orthogonal_family_in_span l h μ hμ
  choose t ht0 htlo hthi using fun i => exists_rescale_norm_mem_Ioc l (u i) (hu0 i)
  set w : Fin h → ℂ_[l] := fun i => algebraMap ℚ_[l] ℂ_[l] (t i) * u i with hw_def
  have hworth : ∀ (c : Fin h → ℚ_[l]) (j : Fin h),
      ‖c j‖ * ‖w j‖ ≤ ‖∑ i, algebraMap ℚ_[l] ℂ_[l] (c i) * w i‖ := by
    intro c j
    have := horth (fun i => c i * t i) j
    simp only [hw_def, map_mul, mul_assoc, norm_mul, norm_algebraMap'] at this ⊢
    exact this
  set σ := Tuple.sort (fun i => -‖w i‖)
  refine ⟨fun i => w (σ i), fun i => ?_, fun i => ⟨?_, hthi _⟩, fun i => htlo _, ?_, fun c j => ?_⟩
  · simp only [hw_def]
    rw [← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (huS _)
  · simp only [hw_def]
    intro h0
    have := congrArg norm h0
    rw [norm_zero] at this
    exact (lt_irrefl (0 : ℝ)) ((inv_pos.2 (by exact_mod_cast (Fact.out : l.Prime).pos)).trans
      (this ▸ htlo (σ i)))
  · intro a b hab
    exact neg_le_neg_iff.1 (Tuple.monotone_sort (fun i => -‖w i‖) hab)
  · have := hworth (fun k => c (σ.symm k)) (σ j)
    rw [← Equiv.sum_comp σ] at this
    simpa using this

theorem _root_.GlobalTheory.PMonE.OrthBasis.exists_orthBasis : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (μ : Fin h → ℂ_[l]), (∀ c : Fin h → ℚ_[l], ∑ j, algebraMap ℚ_[l] ℂ_[l] (c j) * μ j = 0 → c = 0) → ∃ (P : Matrix (Fin h) (Fin h) ℚ_[l]) (μ' : Fin h → ℂ_[l]), P.det ≠ 0 ∧ (∀ i, μ' i = ∑ j, algebraMap ℚ_[l] ℂ_[l] (P i j) * μ j) ∧ (∀ i, μ' i ≠ 0 ∧ ‖μ' i‖ ≤ 1) ∧ Antitone (fun i => ‖μ' i‖) ∧ (∀ i j, ‖μ' i‖ < l * ‖μ' j‖) ∧ ∀ (c : Fin h → ℚ_[l]) (j : Fin h), ‖c j‖ * ‖μ' j‖ ≤ ‖∑ i, algebraMap ℚ_[l] ℂ_[l] (c i) * μ' i‖ := by
  intro l _ h μ hind
  classical
  have hμ : LinearIndependent ℚ_[l] μ := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have := hind g (by simpa [Algebra.smul_def] using hg)
    simp [this]
  obtain ⟨v, hvS, hv1, hvlo, hanti, horth⟩ := exists_sorted_orthogonal_family_in_span l h μ hμ
  choose P hP using fun i => (Submodule.mem_span_range_iff_exists_fun ℚ_[l]).1 (hvS i)
  have hlpos : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  refine ⟨Matrix.of P, v, ?_, fun i => ?_, hv1, hanti, fun i j => ?_, horth⟩
  · intro hdet
    obtain ⟨w, hw0, hwP⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
    have hcol : ∀ j, ∑ i, w i * P i j = 0 := fun j => by
      simpa [Matrix.vecMul, dotProduct] using congrFun hwP j
    have hsum : ∑ i, algebraMap ℚ_[l] ℂ_[l] (w i) * v i = 0 := by
      simp_rw [← Algebra.smul_def, ← hP, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_smul, hcol, zero_smul, Finset.sum_const_zero]
    apply hw0
    funext j
    have h1 := horth w j
    rw [hsum, norm_zero] at h1
    have h2 : 0 < ‖v j‖ := norm_pos_iff.2 (hv1 j).1
    have h3 : ‖w j‖ = 0 := le_antisymm (by nlinarith [norm_nonneg (w j)]) (norm_nonneg _)
    simpa using h3
  · rw [← hP i]
    simp [Algebra.smul_def]
  · calc ‖v i‖ ≤ 1 := (hv1 i).2
      _ = (l : ℝ) * (l : ℝ)⁻¹ := (mul_inv_cancel₀ hlpos.ne').symm
      _ < (l : ℝ) * ‖v j‖ := mul_lt_mul_of_pos_left (hvlo j) hlpos

end GlobalTheory.PMonE.OrthBasis
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem card_le_index_mul_card_map_inf (G H : Type) [Group G] [Group H] [Finite H]
    (f : G →* H) (N : Subgroup G) (I : Subgroup H) (hf : Function.Surjective f)
    (hN : N.index ≠ 0) : Nat.card ↥I ≤ N.index * Nat.card ↥(N.map f ⊓ I) := by
  have h1 : (N.map f).relIndex I * Nat.card ↥(N.map f ⊓ I) = Nat.card I := by
    rw [Subgroup.relIndex, mul_comm, ← Subgroup.card_mul_index ((N.map f).subgroupOf I)]
    congr 1
    rw [← Subgroup.inf_subgroupOf_right]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv).symm
  have h2 : (N.map f).relIndex I ≤ (N.map f).index := by
    rw [← Subgroup.relIndex_top_right]
    apply Subgroup.relIndex_le_of_le_right le_top
    rw [Subgroup.relIndex_top_right]
    exact Subgroup.index_ne_zero_of_finite
  have h3 : (N.map f).index ≤ N.index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hN) (Subgroup.index_map_dvd N hf)
  rw [← h1]
  exact Nat.mul_le_mul_right _ (h2.trans h3)

end GlobalTheory.PMon.Ram
end
