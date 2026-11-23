module

public import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle122
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerTowerQqPowLevelEqQ
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle032
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingCyclotomicTowerLevel
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle124
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle123
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle125
public import Mathlib.Basic.Complex.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.GroupTheory.PGroup
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle127
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHomToKernelSqCentralExtensionSlTwoZMod
public import ReciprocityTheory.Hypotheses.GalCohDefs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle126
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle009
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle023
import Formalism.GaloisCohomology.StatementLoc

@[expose] public section

section

open Polynomial Classical GlobalTheory.BadShare

theorem _root_.GlobalTheory.T.levelDatum_submonoid_chi_mul_unipotent : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ L : Lev g N, L.Mem 1 ∧ (∀ u v, L.Mem u → L.Mem v → L.Mem (u * v)) ∧ L.chi 1 = 1 ∧ (∀ u v, L.Mem u → L.Mem v → L.chi (u * v) = L.chi u * L.chi v) ∧ ∀ u, L.Mem u → IsNilpotent (u.val - 1) := by
  first | exact @GlobalTheory.BadShare.LevGroup.lev_group | exact GlobalTheory.BadShare.LevGroup.lev_group | (intros; apply GlobalTheory.BadShare.LevGroup.lev_group <;> assumption)
end

section

open GlobalTheory.K5 GlobalTheory.KumDlog

noncomputable section

namespace GlobalTheory.K5.LevEmb

theorem emb_inj_range : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ (T : Tower p Ω) (m : ℕ), 1 ≤ m → ∀ ι : On p m →ₐ[O0 p] Ω, IsEmb T m ι →
    Function.Injective ι ∧ ι.range = Lev T m := by
  intro p _ Ω _ _ hΩ T m hm ι hι
  obtain ⟨b, hb⟩ := GlobalTheory.K5.OnFree.on_free p m
  have hadj : Algebra.adjoin (O0 p) {xn p m, yn p m} = ⊤ :=
    GlobalTheory.K5.OnDVR.adjoin_eq_top_of_basis b (xn p m) (yn p m) (fun i => (i : ℕ)) (fun j => (j : ℕ))
      (fun i j => hb i j)
  refine ⟨?_, ?_⟩
  · obtain ⟨hdom, -, -⟩ := GlobalTheory.K5.OnDVR.isDVR_On p m hm
    haveI : Module.Finite (O0 p) (On p m) := Module.Finite.of_basis b
    haveI : Algebra.IsIntegral (O0 p) (On p m) := Algebra.IsIntegral.of_finite _ _
    have hk : RingHom.ker (ι : On p m →+* Ω) = ⊥ := by
      apply Ideal.eq_bot_of_comap_eq_bot (R := O0 p)
      rw [eq_bot_iff]
      intro a ha
      rw [Ideal.mem_comap, RingHom.mem_ker] at ha
      have h1 : algebraMap (O0 p) Ω a = 0 := by
        rw [← ι.commutes]; exact ha
      rw [Ideal.mem_bot]
      exact hΩ.inj (by rw [h1, map_zero])
    exact (RingHom.injective_iff_ker_eq_bot _).2 hk
  · rw [← Algebra.map_top, ← hadj, AlgHom.map_adjoin, Set.image_pair, hι.1, hι.2]
    rfl

end GlobalTheory.K5.LevEmb
end
end

section

open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.StableSubset

open Finset Equiv

theorem mem_iff_of_map_eq {N : ℕ} (σ : Perm (Fin N)) (A : Finset (Fin N))
    (h : A.map σ.toEmbedding = A) (x : Fin N) : σ x ∈ A ↔ x ∈ A := by
  conv_lhs => rw [← h]
  exact Finset.mem_map' σ.toEmbedding

theorem map_eq_of_mem_iff {N : ℕ} (σ : Perm (Fin N)) (A : Finset (Fin N))
    (h : ∀ x, x ∈ A → σ x ∈ A) : A.map σ.toEmbedding = A := by
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 hy
    exact h x hx
  · simp

theorem card_stab_le {N : ℕ} (A : Finset (Fin N)) :
    (univ.filter fun σ : Perm (Fin N) => A.map σ.toEmbedding = A).card ≤
      A.card.factorial * (N - A.card).factorial := by
  have hsub : (univ.filter fun σ : Perm (Fin N) => A.map σ.toEmbedding = A) ⊆
      (univ : Finset (Perm {x // x ∈ A} × Perm {x // x ∉ A})).image
        (fun p => Perm.subtypeCongr p.1 p.2) := by
    intro σ hσ
    have h := mem_iff_of_map_eq σ A (Finset.mem_filter.1 hσ).2
    refine Finset.mem_image.2 ⟨(σ.subtypePerm h, σ.subtypePerm (fun x => not_congr (h x))),
      Finset.mem_univ _, ?_⟩
    ext x
    by_cases hx : x ∈ A
    · simp [Perm.subtypeCongr.left_apply _ _ hx]
    · simp [Perm.subtypeCongr.right_apply _ _ hx]
  refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
  simp [Fintype.card_perm, Fintype.card_subtype_compl]

theorem card_fix_ge {N : ℕ} (A : Finset (Fin N)) (h0 : 0 < A.card) (hN : A.card < N) :
    A.card.factorial * (N - A.card).factorial ≤
      4 * (univ.filter fun σ : Perm (Fin N) => A.map σ.toEmbedding = A ∧
        (∃ i ∈ A, σ i = i) ∧ ∃ j ∉ A, σ j = j).card := by
  have c1 : Fintype.card {x // x ∈ A} = A.card := by simp
  have c2 : Fintype.card {x // x ∉ A} = N - A.card := by simp [Fintype.card_subtype_compl]
  have h1 := GlobalTheory.T.factorial_le_two_mul_card_perm_with_fixedPoint {x // x ∈ A} (Fintype.card_pos_iff.1 (by omega))
  have h2 := GlobalTheory.T.factorial_le_two_mul_card_perm_with_fixedPoint {x // x ∉ A} (Fintype.card_pos_iff.1 (by omega))
  rw [c1] at h1
  rw [c2] at h2
  refine (Nat.mul_le_mul h1 h2).trans ?_
  rw [mul_mul_mul_comm, ← Finset.card_product]
  refine Nat.mul_le_mul le_rfl ?_
  refine Finset.card_le_card_of_injOn (fun p => Perm.subtypeCongr p.1 p.2) ?_ ?_
  · rintro ⟨e, f⟩ hp
    simp only [Finset.coe_product, Set.mem_prod, Finset.coe_filter, Finset.mem_univ, true_and,
      Set.mem_setOf_eq] at hp ⊢
    obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := hp
    refine ⟨map_eq_of_mem_iff _ _ ?_, ⟨i, i.2, ?_⟩, ⟨j, j.2, ?_⟩⟩
    · intro x hx
      rw [Perm.subtypeCongr.left_apply _ _ hx]
      exact (e ⟨x, hx⟩).2
    · rw [Perm.subtypeCongr.left_apply_subtype, hi]
    · rw [Perm.subtypeCongr.right_apply_subtype, hj]
  · rintro ⟨e, f⟩ - ⟨e', f'⟩ - h
    have h' : Perm.subtypeCongr e f = Perm.subtypeCongr e' f' := h
    refine Prod.ext ?_ ?_
    · ext x : 2
      have := congrArg (fun s : Perm (Fin N) => s x) h'
      simpa only [Perm.subtypeCongr.left_apply_subtype] using this
    · ext x : 2
      have := congrArg (fun s : Perm (Fin N) => s x) h'
      simpa only [Perm.subtypeCongr.right_apply_subtype] using this

noncomputable def wt {N : ℕ} (A : Finset (Fin N)) (σ : Perm (Fin N)) : ℕ :=
  if A.map σ.toEmbedding = A then
    (if (∃ i ∈ A, σ i = i) ∧ ∃ j ∉ A, σ j = j then 4 else 8) else 0

theorem sum_wt_le {N : ℕ} (A : Finset (Fin N)) (h0 : 0 < A.card) (hN : A.card < N) :
    ∑ σ, wt A σ ≤ 7 * (A.card.factorial * (N - A.card).factorial) := by
  have h1 := card_stab_le A
  have h2 := card_fix_ge A h0 hN
  have h3 : ∑ σ, wt A σ + 4 * (univ.filter fun σ : Perm (Fin N) => A.map σ.toEmbedding = A ∧
        (∃ i ∈ A, σ i = i) ∧ ∃ j ∉ A, σ j = j).card =
      8 * (univ.filter fun σ : Perm (Fin N) => A.map σ.toEmbedding = A).card := by
    rw [Finset.card_filter, Finset.card_filter, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    unfold wt
    by_cases ha : A.map σ.toEmbedding = A <;>
      by_cases hb : (∃ i ∈ A, σ i = i) ∧ ∃ j ∉ A, σ j = j <;> simp only [ha, hb] <;> simp
  omega

theorem four_le_wt {N : ℕ} (A : Finset (Fin N)) (σ : Perm (Fin N))
    (h : A.map σ.toEmbedding = A) : 4 ≤ wt A σ := by
  unfold wt
  rw [if_pos h]
  split_ifs <;> omega

theorem eight_le_sum_wt {N a : ℕ} (σ : Perm (Fin N)) (A : Finset (Fin N)) (hA : A.card = a)
    (h : A.map σ.toEmbedding = A) : 8 ≤ ∑ B ∈ powersetCard a (univ : Finset (Fin N)), wt B σ := by
  have hAm : A ∈ powersetCard a (univ : Finset (Fin N)) := by simp [hA]
  by_cases hb : (∃ i ∈ A, σ i = i) ∧ ∃ j ∉ A, σ j = j
  · obtain ⟨⟨i, hi, hσi⟩, ⟨j, hj, hσj⟩⟩ := hb
    set B := insert j (A.erase i) with hB
    have hjB : j ∈ B := Finset.mem_insert_self _ _
    have hne : A ≠ B := fun e => hj (e ▸ hjB)
    have hBc : B.card = a := by
      rw [hB, Finset.card_insert_of_notMem (fun hh => hj (Finset.mem_of_mem_erase hh)),
        Finset.card_erase_add_one hi, hA]
    have hBm : B ∈ powersetCard a (univ : Finset (Fin N)) := by simp [hBc]
    have hBs : B.map σ.toEmbedding = B := by
      apply map_eq_of_mem_iff
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · rw [hσj]; exact hjB
      · refine Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨?_, ?_⟩)
        · intro e
          exact (Finset.mem_erase.1 hx).1 (σ.injective (e.trans hσi.symm))
        · exact (mem_iff_of_map_eq σ A h x).2 (Finset.mem_erase.1 hx).2
    have hs : ({A, B} : Finset _) ⊆ powersetCard a (univ : Finset (Fin N)) := by
      intro C hC
      rcases Finset.mem_insert.1 hC with rfl | hC
      · exact hAm
      · rw [Finset.mem_singleton.1 hC]; exact hBm
    have := Finset.sum_le_sum_of_subset (f := fun B => wt B σ) hs
    rw [Finset.sum_pair hne] at this
    have h1 := four_le_wt A σ h
    have h2 := four_le_wt B σ hBs
    omega
  · have : wt A σ = 8 := by unfold wt; rw [if_pos h, if_neg hb]
    rw [← this]
    exact Finset.single_le_sum (f := fun B => wt B σ) (fun _ _ => Nat.zero_le _) hAm

theorem card_exists_stable_subset_le : ∀ N a : ℕ, 0 < a → a < N →
    8 * (Finset.univ.filter fun σ : Equiv.Perm (Fin N) =>
      ∃ A : Finset (Fin N), A.card = a ∧ A.map σ.toEmbedding = A).card ≤ 7 * N.factorial := by
  intro N a h0 hN
  calc _ ≤ ∑ σ : Perm (Fin N), ∑ B ∈ powersetCard a (univ : Finset (Fin N)), wt B σ := by
        rw [Finset.card_filter, Finset.mul_sum]
        refine Finset.sum_le_sum fun σ _ => ?_
        split_ifs with h
        · obtain ⟨A, hA, h⟩ := h
          exact eight_le_sum_wt σ A hA h
        · simp
    _ = ∑ B ∈ powersetCard a (univ : Finset (Fin N)), ∑ σ : Perm (Fin N), wt B σ :=
        Finset.sum_comm
    _ ≤ ∑ B ∈ powersetCard a (univ : Finset (Fin N)),
          7 * (a.factorial * (N - a).factorial) := by
        refine Finset.sum_le_sum fun B hB => ?_
        have hB' : B.card = a := (Finset.mem_powersetCard.1 hB).2
        have := sum_wt_le B (by omega) (by omega)
        rwa [hB'] at this
    _ = 7 * N.factorial := by
        rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
          smul_eq_mul, ← Nat.choose_mul_factorial_mul_factorial hN.le]
        ring

end GlobalTheory.StableSubset
end

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

theorem _root_.GlobalTheory.T.cocycle_isCoboundary_of_neg_central_element : ∀ (G : Type) [Group G] (R : Type) [CommRing R] (V : Type) [AddCommGroup V] [Module R V] (ρ : G → V →ₗ[R] V), (∀ g h v, ρ (g * h) v = ρ h (ρ g v)) → (∀ v, ρ 1 v = v) → IsUnit (2 : R) → ∀ (S : Submodule R V), (∀ g, ∀ v ∈ S, ρ g v ∈ S) → ∀ (Δ : Subgroup G), Δ.Normal → (∀ δ ∈ Δ, ∀ v, ρ δ v = v) → ∀ c : G, (∀ v ∈ S, ρ c v = -v) → (∀ g, c * g * c⁻¹ * g⁻¹ ∈ Δ) → ∀ z : G → V, (∀ g, z g ∈ S) → (∀ g h, z (g * h) = ρ h (z g) + z h) → (∀ δ ∈ Δ, z δ = 0) → ∃ p ∈ S, ∀ g, z g = ρ g p - p := by
  first | exact @GlobalTheory.KZ.H3.cocycle_isCoboundary_of_neg_central | exact GlobalTheory.KZ.H3.cocycle_isCoboundary_of_neg_central | (intros; apply GlobalTheory.KZ.H3.cocycle_isCoboundary_of_neg_central <;> assumption)
end

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

theorem _root_.GlobalTheory.T.exists_cocycle_extension_of_neg_central_element : ∀ (G : Type) [Group G] (R : Type) [CommRing R] (V : Type) [AddCommGroup V] [Module R V] (ρ : G → V →ₗ[R] V), (∀ g h v, ρ (g * h) v = ρ h (ρ g v)) → (∀ v, ρ 1 v = v) → IsUnit (2 : R) → ∀ (S : Submodule R V), (∀ g, ∀ v ∈ S, ρ g v ∈ S) → ∀ (Δ : Subgroup G), Δ.Normal → (∀ δ ∈ Δ, ∀ v, ρ δ v = v) → ∀ c : G, (∀ v ∈ S, ρ c v = -v) → (∀ g, c * g * c⁻¹ * g⁻¹ ∈ Δ) → ∀ φ : G → V, (∀ δ ∈ Δ, φ δ ∈ S) → (∀ δ ∈ Δ, ∀ δ' ∈ Δ, φ (δ * δ') = φ δ + φ δ') → (∀ g, ∀ δ ∈ Δ, ρ g (φ (g * δ * g⁻¹)) = φ δ) → ∃ z : G → V, (∀ g, z g ∈ S) ∧ (∀ g h, z (g * h) = ρ h (z g) + z h) ∧ ∀ δ ∈ Δ, z δ = φ δ := by
  first | exact @GlobalTheory.KZ.H3.exists_cocycle_extension_of_neg_action | exact GlobalTheory.KZ.H3.exists_cocycle_extension_of_neg_action | (intros; apply GlobalTheory.KZ.H3.exists_cocycle_extension_of_neg_action <;> assumption)
end

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

theorem _root_.GlobalTheory.T.exists_root_ball_of_analyticOrder_dvd : ∀ (h : ℂ → ℂ) (m : ℕ) (c : ℂ) (R : ℝ), 0 < m → 0 < R → AnalyticOnNhd ℂ h (Metric.closedBall c R) → (∀ τ ∈ Metric.closedBall c R, ∃ k : ℕ, analyticOrderAt h τ = ((m * k : ℕ) : ℕ∞)) → ∃ r : ℂ → ℂ, DifferentiableOn ℂ r (Metric.ball c R) ∧ ∀ z ∈ Metric.ball c R, r z ^ m = h z := by
  first | exact @GlobalTheory.KZ.RootDisc.exists_root_disc | exact GlobalTheory.KZ.RootDisc.exists_root_disc | (intros; apply GlobalTheory.KZ.RootDisc.exists_root_disc <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.coeff_mem_range_of_isRoot_of_coeff_mem_range : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (b : PowerSeries ℂ) (Q : Polynomial (PowerSeries ℂ)), Q ≠ 0 → (∀ i k, PowerSeries.coeff k (Q.coeff i) ∈ ε.range) → Q.eval b = 0 → ∀ k, PowerSeries.coeff k b ∈ ε.range := by
  first | exact @GlobalTheory.PsRoot.coeff_mem_range_of_isRoot | exact GlobalTheory.PsRoot.coeff_mem_range_of_isRoot | (intros; apply GlobalTheory.PsRoot.coeff_mem_range_of_isRoot <;> assumption)
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

theorem _root_.GlobalTheory.T.mem_valuationSubring_galois_iff_of_kummer_stable : ∀ (l : ℕ), l.Prime → ∀ (F L : Type) [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L], IsPGroup l (L ≃ₐ[F] L) → (∃ ζ : F, IsPrimitiveRoot ζ l) → ∀ W : ValuationSubring L, (∀ θ : L, θ ≠ 0 → θ ^ l ∈ (algebraMap F L).range → ∀ τ : L ≃ₐ[F] L, ∀ x ∈ IntermediateField.adjoin F {θ}, τ x ∈ W ↔ x ∈ W) → ∀ (τ : L ≃ₐ[F] L) (x : L), τ x ∈ W ↔ x ∈ W := by
  first | exact @GlobalTheory.valuationSubring_galois_stable_of_kummer | exact GlobalTheory.valuationSubring_galois_stable_of_kummer | (intros; apply GlobalTheory.valuationSubring_galois_stable_of_kummer <;> assumption)
end

section

open Polynomial

theorem _root_.GlobalTheory.T.specialise_generic_solution_almost_all_points : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] (R : Type) [CommRing R] [IsDomain R] [Algebra k R] (N : ℕ) (I : Type) [Fintype I] (V : Submodule k A) (D : Ideal A), 2 ≤ N → (∃ (ξ : A →ₐ[k] R) (Δ : I → ℕ → A →ₗ[k] R) (m : ℕ) (v : Fin m → A) (y : Fin m → R),
  Function.Injective ξ ∧ (∀ i, Δ i 0 1 = 1) ∧ (∀ i, (∀ l, ∀ u w : A, Δ i l (u * w) = ∑ p ∈ Finset.range (l + 1), l.choose p • (Δ i p u * Δ i (l - p) w))) ∧ (∀ i, ∃ π : A, Δ i 1 π = 1) ∧
  (∀ j, v j ∈ V) ∧ LinearIndependent k v ∧ (∃ j, IsUnit (y j)) ∧ ∑ j, y j * ξ (v j) = 0 ∧ (∀ i, ∀ l < N, ∑ j, y j * Δ i l (v j) = 0) ∧
  (∀ i i', i ≠ i' → ∃ u : A, IsUnit (Δ i 0 u - Δ i' 0 u)) ∧ (∀ i, ∃ u : A, IsUnit (Δ i 0 u - ξ u)) ∧ (∀ i, ∃ u ∈ D, IsUnit (Δ i 0 u)) ∧ (∃ u ∈ D, IsUnit (ξ u))) → ∃ a : A, a ≠ 0 ∧ ∀ P : Ideal A, P.IsMaximal → a ∉ P → ∃ (Q' : I → Ideal A) (f : A), (∀ i, (Q' i).IsMaximal) ∧ Function.Injective Q' ∧ (∀ i, Q' i ≠ P) ∧ (∀ i, ¬ D ≤ Q' i) ∧ ¬ D ≤ P ∧ f ∈ V ∧ f ≠ 0 ∧ f ∈ P ∧ ∀ i, f ∈ Q' i ^ N := by
  first | exact @GlobalTheory.specialise_generic_solution | exact GlobalTheory.specialise_generic_solution | (intros; apply GlobalTheory.specialise_generic_solution <;> assumption)
end

section

open Polynomial

theorem _root_.GlobalTheory.T.exists_linear_system_maximalDegree_factorization : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra k[X] A] [IsScalarTower k k[X] A] [Module.Finite k[X] A] [Module.Free k[X] A] (N : ℕ) (P₀ : Ideal A), 1 ≤ N → P₀.IsMaximal → ∃ (r : ℕ) (V : Submodule k A) (D : Ideal A) (Q : Fin r → Ideal A) (f₀ : A), (FiniteDimensional k V ∧ (∀ v ∈ V, v ∈ D) ∧ (∀ i, (Q i).IsMaximal) ∧ Function.Injective Q ∧ (∀ i, Q i ≠ P₀) ∧ (∀ i, ¬ D ≤ Q i) ∧ ¬ D ≤ P₀ ∧ f₀ ∈ V ∧ f₀ ≠ 0 ∧ Ideal.span {f₀} = P₀ * D * ∏ i, Q i ^ N ∧ (∀ u : A, ∃ v ∈ V, u - v ∈ P₀ * ∏ i, Q i ^ (N - 1))) ∧ (∀ f ∈ V, f ≠ 0 → Module.finrank k (A ⧸ Ideal.span {f}) ≤ Module.finrank k (A ⧸ Ideal.span {f₀})) := by
  first | exact @GlobalTheory.linear_system_setup | exact GlobalTheory.linear_system_setup | (intros; apply GlobalTheory.linear_system_setup <;> assumption)
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

theorem _root_.GlobalTheory.T.exists_hom_to_kernel_sq_centralExtension_slTwoZMod : ∀ (l n m : ℕ), l.Prime → 0 < m → Nat.Coprime m (6 * l) → ∀ (E : Type) [Group E] (π : E →* Matrix.SpecialLinearGroup (Fin 2) (ZMod m)), Function.Surjective π → π.ker ≤ Subgroup.center E → (∀ x ∈ π.ker, x ^ (l ^ n) = 1) → ∃ ψ : E →* E, (∀ e, ψ e ∈ π.ker) ∧ ∀ x ∈ π.ker, ψ x = x ^ 2 := by
  first | exact @GlobalTheory.CentralExt.exists_hom_to_kernel_eq_sq_on_kernel_of_central_ext_sl2 | exact GlobalTheory.CentralExt.exists_hom_to_kernel_eq_sq_on_kernel_of_central_ext_sl2 | (intros; apply GlobalTheory.CentralExt.exists_hom_to_kernel_eq_sq_on_kernel_of_central_ext_sl2 <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

theorem _root_.GlobalTheory.T.exists_coboundary_of_subsingleton_contCohomology_three : ∀ (R : Type) [CommRing R] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (M : Type) [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R Γ M), Subsingleton (Hn ρ 3) → ∀ c : Γ × Γ × Γ → M, Continuous c → (∀ g h k m, ρ g (c (h, k, m)) - c (g * h, k, m) + c (g, h * k, m) - c (g, h, k * m) + c (g, h, k) = 0) → ∃ u : Γ × Γ → M, Continuous u ∧ ∀ g h k, ρ g (u (h, k)) - u (g * h, k) + u (g, h * k) - u (g, h) = c (g, h, k) := by
  first | exact @GlobalTheory.exists_coboundary_of_subsingleton_Hn_three | exact GlobalTheory.exists_coboundary_of_subsingleton_Hn_three | (intros; apply GlobalTheory.exists_coboundary_of_subsingleton_Hn_three <;> assumption)
end
