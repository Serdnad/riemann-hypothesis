module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle016
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle331
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle539
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle540
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle543
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle541
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle334
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle542
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitaryOfLocallyBijectiveFromFilteredFunctor
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxD
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003
public import Mathlib.Analysis.Calculus.BumpFunction.Basic

@[expose] public section

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
namespace GlobalTheory.Shin

theorem tensorInd_virt_prime : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (Nat.card Γ).Prime → s ≠ 1 → ∀ χ ∈ Virt ℂ ℂ G, ∃ X ∈ Virt ℂ ℂ (G ⋊[φ] Γ), (∀ g, X (inl g) = ∏ t : Γ, χ (φ t g)) ∧ ∀ δ, X (inl δ * inr s) = χ (nrmG φ s (Nat.card Γ) δ) := by
  intro G Γ _ _ _ _ φ s hp hs χ hχ
  have hgen : ∀ t : Γ, t ∈ Subgroup.zpowers s := by
    haveI : Fact (Nat.card Γ).Prime := ⟨hp⟩
    intro t
    exact mem_zpowers_of_prime_card rfl hs
  obtain ⟨a, b, ha, hb, rfl⟩ := (mem_virt_iff_sub ℂ ℂ G χ).1 hχ
  obtain ⟨A, hA, hA1, hA2⟩ := GlobalTheory.T.exists_tensorInduction_char' G Γ φ s hgen a ha
  obtain ⟨B, hB, hB1, hB2⟩ := GlobalTheory.T.exists_tensorInduction_char' G Γ φ s hgen b hb
  obtain ⟨Z, hZ, hZ1, hZ2⟩ := GlobalTheory.T.exists_virtualCharacter_semidirect_orbit_cross_terms G Γ φ s hp hs (a - b) b
    ((mem_virt_iff_sub ℂ ℂ G _).2 ⟨a, b, ha, hb, rfl⟩)
    ((mem_virt_iff_sub ℂ ℂ G b).2 ⟨b, 0, hb, (GlobalTheory.T.isCharacterOverSubfield_zero_and_add ℂ ℂ G).1, by simp⟩)
  have hAv : A ∈ Virt ℂ ℂ (G ⋊[φ] Γ) := AddSubgroup.subset_closure hA
  have hBv : B ∈ Virt ℂ ℂ (G ⋊[φ] Γ) := AddSubgroup.subset_closure hB
  refine ⟨A - B - Z, (Virt ℂ ℂ _).sub_mem ((Virt ℂ ℂ _).sub_mem hAv hBv) hZ, ?_, ?_⟩
  · intro g
    simp only [Pi.sub_apply, hA1, hB1, hZ1, sub_add_cancel]
    ring
  · intro δ
    simp only [Pi.sub_apply, hA2, hB2, hZ2, sub_zero]

end GlobalTheory.Shin
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam.SepGL

theorem vmul_ne_zero {N : ℕ} (x : Fin 2 → ZMod N) (hx : x ≠ 0) (α : GL (Fin 2) (ZMod N)) :
    vmul x α ≠ 0 := by
  intro h
  apply hx
  have h2 : (x ᵥ* (α : Matrix (Fin 2) (Fin 2) (ZMod N))) ᵥ*
      ((α⁻¹ : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) = x := by
    rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]
  unfold vmul at h
  rw [← h2, h, Matrix.zero_vecMul]

theorem main : ∀ (N : ℕ) [NeZero N] (τ : ℍ) (α β : GL (Fin 2) (ZMod N)), (∀ i : Fin 2, wp N (vmul (Pi.single i 1) α) τ = wp N (vmul (Pi.single i 1) β) τ ∧ wpd N (vmul (Pi.single i 1) α) τ = wpd N (vmul (Pi.single i 1) β) τ) → α = β := by
  intro N _ τ α β h
  rcases subsingleton_or_nontrivial (ZMod N) with hs | hs
  · exact Matrix.GeneralLinearGroup.ext fun i j => Subsingleton.elim _ _
  · have key : ∀ i : Fin 2, vmul (Pi.single i 1) α = vmul (Pi.single i 1) β := by
      intro i
      have h0 : (Pi.single i (1 : ZMod N) : Fin 2 → ZMod N) ≠ 0 := by
        intro h1
        have := congrFun h1 i
        simp at this
      exact GlobalTheory.T.eq_of_weierstrassP_derivWeierstrassP_torsion_eq N τ _ _ (vmul_ne_zero _ h0 α) (vmul_ne_zero _ h0 β) (h i).1 (h i).2
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    have := congrFun (key i) j
    simpa [vmul, Matrix.single_vecMul] using this

end GlobalTheory.WpFam.SepGL
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

theorem _root_.GlobalTheory.T.weierstrass_division_value_q_expansion : ∀ (N : ℕ) [NeZero N] (x : Fin 2 → ZMod N), x ≠ 0 → HasQ N (wB N x) (cB N x) := by
  first | exact @GlobalTheory.WpFam.ExpansionB.main | exact GlobalTheory.WpFam.ExpansionB.main | (intros; apply GlobalTheory.WpFam.ExpansionB.main <;> assumption)
end

section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef

theorem functionFieldPlaceOrder_inv {k F : Type} [Field k] [Field F] [Algebra k F] (v : Place k F) (x : F) (hx : x ≠ 0) :
    ord v x⁻¹ = - ord v x := by
  have h0 : v.1 x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  unfold ord
  rw [map_inv₀, WithZero.log_inv, neg_neg]

theorem adjoin_simple_inv_eq (k F : Type) [Field k] [Field F] [Algebra k F] (x : F) :
    k⟮x⁻¹⟯ = k⟮x⟯ := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact inv_mem (IntermediateField.mem_adjoin_simple_self k x)
  · rw [IntermediateField.adjoin_simple_le_iff]
    have := inv_mem (IntermediateField.mem_adjoin_simple_self k x⁻¹)
    rwa [inv_inv] at this

theorem finite_support_and_sum_ord_eq_zero : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
    ∀ x : F, x ≠ 0 → {v : Place k F | v.1 x ≠ 1}.Finite ∧ ∑ᶠ v : Place k F, ord v x = 0 := by
  intro k F _ _ _ _ _ hF x hx
  by_cases htr : Transcendental k x
  · have htr' : Transcendental k x⁻¹ := by
      intro h
      apply htr
      have := h.inv
      rwa [inv_inv] at this
    obtain ⟨hA, hsA⟩ := GlobalTheory.T.functionField_zeros_finite_sum_order_eq_finrank k F hF x htr
    obtain ⟨hB, hsB⟩ := GlobalTheory.T.functionField_zeros_finite_sum_order_eq_finrank k F hF x⁻¹ htr'
    rw [adjoin_simple_inv_eq] at hsB
    set A := {v : Place k F | v.1 x < 1}
    set B := {v : Place k F | v.1 x⁻¹ < 1}
    have hsub : {v : Place k F | v.1 x ≠ 1} ⊆ A ∪ B := by
      intro v hv
      have h0 : v.1 x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
      rcases lt_or_gt_of_ne hv with h | h
      · exact Or.inl h
      · right
        show v.1 x⁻¹ < 1
        rw [map_inv₀]
        exact inv_lt_one_of_one_lt₀ h
    refine ⟨(hA.union hB).subset hsub, ?_⟩
    have hpt : ∀ v : Place k F, ord v x = A.indicator (fun w => ord w x) v - B.indicator (fun w => ord w x⁻¹) v := by
      intro v
      have h0 : v.1 x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
      rcases lt_trichotomy (v.1 x) 1 with h | h | h
      · have hB' : v ∉ B := by
          show ¬ v.1 x⁻¹ < 1
          rw [map_inv₀, not_lt]
          exact (one_le_inv₀ (zero_lt_iff.2 h0)).2 h.le
        rw [Set.indicator_of_mem (show v ∈ A from h), Set.indicator_of_notMem hB', sub_zero]
      · have e : ord v x = 0 := by unfold ord; rw [h, WithZero.log_one, neg_zero]
        rw [e, Set.indicator_of_notMem (show v ∉ A from fun h' => by change v.1 x < 1 at h'; rw [h] at h'; exact lt_irrefl _ h'),
          Set.indicator_of_notMem (show v ∉ B from by
            show ¬ v.1 x⁻¹ < 1
            rw [map_inv₀, h, inv_one]; exact lt_irrefl _)]
        simp
      · have hA' : v ∉ A := fun h' => lt_asymm h h'
        have hB' : v ∈ B := by
          show v.1 x⁻¹ < 1
          rw [map_inv₀]
          exact inv_lt_one_of_one_lt₀ h
        rw [Set.indicator_of_notMem hA', Set.indicator_of_mem hB', functionFieldPlaceOrder_inv v x hx, zero_sub, neg_neg]
    have hfA : (Function.support (A.indicator fun w => ord w x)).Finite :=
      hA.subset (Set.support_indicator_subset)
    have hfB : (Function.support (B.indicator fun w => ord w x⁻¹)).Finite :=
      hB.subset (Set.support_indicator_subset)
    rw [finsum_congr hpt, finsum_sub_distrib hfA hfB, ← finsum_mem_def, ← finsum_mem_def, hsA, hsB, sub_self]
  · have halg : IsAlgebraic k x := by
      by_contra h
      exact htr h
    have hint : IsIntegral k x := halg.isIntegral
    have hdeg : (minpoly k x).degree = 1 :=
      IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hint)
    obtain ⟨c, rfl⟩ := minpoly.mem_range_of_degree_eq_one k x hdeg
    have hc : c ≠ 0 := by
      rintro rfl
      exact hx (map_zero _)
    have hv : ∀ v : Place k F, v.1 (algebraMap k F c) = 1 := fun v => v.2.2 c hc
    refine ⟨by simp [hv], ?_⟩
    have : ∀ v : Place k F, ord v (algebraMap k F c) = 0 := by
      intro v; unfold ord; rw [hv v, WithZero.log_one, neg_zero]
    simp [this]

end GlobalTheory.Nef
end

section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef

theorem local_index_scaled : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ (v : Place k F) (n : ℕ) (M : Matrix (Fin n) (Fin n) F) (d : ℕ), M.det ≠ 0 →
    (∀ i j, v.1 (M⁻¹ i j) ≤ WithZero.exp (d : ℤ)) →
    ∃ (N : ℕ) (φ : (Fin n → F) →ₗ[k] (Fin N → k)), (N : ℤ) = n * d - ord v M.det ∧
      ∀ p : Fin n → F, (∀ i, v.1 (p i) ≤ WithZero.exp (d : ℤ)) → φ p = 0 →
        ∀ i, v.1 (M.mulVec p i) ≤ 1 := by
  intro k F _ _ _ _ _ hFF v n M d hM hMinv
  obtain ⟨hmul, hzpow, -, -, -, ⟨π, hπ0, hπ⟩, -⟩ := GlobalTheory.T.functionFieldPlaceOrder_calculus k F v

  have hvπ : v.1 π = WithZero.exp (-1) := by
    have hne : v.1 π ≠ 0 := by simpa using hπ0
    have : WithZero.log (v.1 π) = -1 := by
      unfold ord at hπ; omega
    rw [← this, WithZero.exp_log hne]
  set c : F := π ^ d with hcdef
  have hc0 : c ≠ 0 := pow_ne_zero _ hπ0
  have hvc : v.1 c = WithZero.exp (-(d : ℤ)) := by
    rw [hcdef, map_pow, hvπ]
    show WithZero.exp (-1) ^ d = _
    rw [← WithZero.exp_nsmul]; congr 1; simp
  set h : Matrix (Fin n) (Fin n) F := c⁻¹ • M with hhdef
  have hdet : h.det = (c⁻¹) ^ n * M.det := by rw [hhdef, Matrix.det_smul, Fintype.card_fin]
  have hdet0 : h.det ≠ 0 := by rw [hdet]; exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hc0)) hM
  have hinv : h⁻¹ = c • M⁻¹ := by
    rw [hhdef]
    apply Matrix.inv_eq_left_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hc0, one_smul,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hM)]
  have hinvb : ∀ i j, v.1 (h⁻¹ i j) ≤ 1 := by
    intro i j
    rw [hinv, Matrix.smul_apply, smul_eq_mul, map_mul, hvc]
    calc WithZero.exp (-(d : ℤ)) * v.1 (M⁻¹ i j) ≤ WithZero.exp (-(d : ℤ)) * WithZero.exp (d : ℤ) :=
          by gcongr; exact hMinv i j
      _ = 1 := by rw [← WithZero.exp_add]; simp
  obtain ⟨N, φ₀, hN, hφ₀⟩ := GlobalTheory.T.functionFieldPlace_local_index_colength k F hFF v n h hdet0 hinvb

  have hord : ord v h.det = -(n * d : ℤ) + ord v M.det := by
    have e : (c⁻¹) ^ n = π ^ (-(n * d : ℤ)) := by
      rw [hcdef, inv_pow, ← pow_mul, ← zpow_natCast, ← zpow_neg]; congr 1; push_cast; ring
    rw [hdet, hmul _ _ (pow_ne_zero _ (inv_ne_zero hc0)) hM, e, hzpow π hπ0, hπ, mul_one]
  let sc : (Fin n → F) →ₗ[k] (Fin n → F) :=
    { toFun := fun p => c • p
      map_add' := fun p q => smul_add c p q
      map_smul' := fun a p => by
        ext i
        show c * (a • p i) = a • (c * p i)
        rw [Algebra.smul_def, Algebra.smul_def]; ring }
  refine ⟨N, φ₀ ∘ₗ sc, by rw [hN, hord]; ring, ?_⟩
  intro p hp hφ i
  have hx : ∀ i, v.1 ((c • p) i) ≤ 1 := by
    intro i
    rw [Pi.smul_apply, smul_eq_mul, map_mul, hvc]
    calc WithZero.exp (-(d : ℤ)) * v.1 (p i) ≤ WithZero.exp (-(d : ℤ)) * WithZero.exp (d : ℤ) :=
          by gcongr; exact hp i
      _ = 1 := by rw [← WithZero.exp_add]; simp
  have := hφ₀ (c • p) hx hφ i
  have e2 : h.mulVec (c • p) = M.mulVec p := by
    rw [hhdef, Matrix.mulVec_smul, Matrix.smul_mulVec, smul_smul, mul_inv_cancel₀ hc0, one_smul]
  rwa [e2] at this

end GlobalTheory.Nef
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem nonempty_cover : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]
    (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), Nonempty (Cover A) := by
  intro n Y _ _ _ _ _ _ ι La _ A
  classical
  have hε : ∀ x : Y, ∃ ε > 0, ball (A.chart (A.pick x) x) ε ⊆ (A.chart (A.pick x)).target :=
    fun x => Metric.isOpen_iff.1 (A.chart (A.pick x)).open_target _
      ((A.chart (A.pick x)).map_source (A.mem_pick x))
  choose ε hε0 hεb using hε
  let b : ∀ x : Y, ContDiffBump (A.chart (A.pick x) x) := fun x =>
    ⟨ε x / 4, ε x / 2, by linarith [hε0 x], by linarith [hε0 x]⟩
  let β : Y → Y → ℝ := fun x => A.chiC (A.pick x) (b x)
  let K0 : Y → Set (V n) := fun x => closedBall (A.chart (A.pick x) x) (ε x / 2)
  have hK0t : ∀ x, K0 x ⊆ (A.chart (A.pick x)).target := fun x =>
    (closedBall_subset_ball (by linarith [hε0 x])).trans (hεb x)
  have hbs : ∀ x u, (b x) u ≠ 0 → u ∈ K0 x := by
    intro x u hu
    have : u ∈ Function.support (b x) := hu
    rw [(b x).support_eq] at this
    exact ball_subset_closedBall this
  have hβs : ∀ x, A.SmoothFn (β x) := fun x =>
    A.chiC_smooth (b x).contDiff (hbs x) (isCompact_closedBall _ _) (hK0t x)
  have hβ0 : ∀ x y, 0 ≤ β x y := by
    intro x y
    show 0 ≤ A.chiC _ _ y
    unfold WeightedAtlas.chiC
    split_ifs
    · exact (b x).nonneg
    · exact le_rfl
  let U : Y → Set Y := fun x =>
    (A.chart (A.pick x)).source ∩ (A.chart (A.pick x)) ⁻¹' ball (A.chart (A.pick x) x) (ε x / 2)
  have hUo : ∀ x, IsOpen (U x) := fun x =>
    (A.chart (A.pick x)).continuousOn.isOpen_inter_preimage (A.chart (A.pick x)).open_source
      isOpen_ball
  have hUx : ∀ x, x ∈ U x := fun x => ⟨A.mem_pick x, by exact Set.mem_preimage.mpr (mem_ball_self (by linarith [hε0 x]))⟩
  have hUpos : ∀ x y, y ∈ U x → 0 < β x y := by
    rintro x y ⟨hy, hyb⟩
    show 0 < A.chiC _ _ y
    rw [A.chiC_of_mem hy]
    exact (b x).pos_of_mem_ball hyb
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hUo
    (fun y _ => Set.mem_iUnion.2 ⟨y, hUx y⟩)
  let pt : Fin t.card → Y := fun a => (t.equivFin.symm a).1
  let S : Y → ℝ := fun y => ∑ a, β (pt a) y
  have hS : ∀ y, 0 < S y := by
    intro y
    obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
    have hpt : pt (t.equivFin ⟨x, hxt⟩) = x := by simp [pt]
    have h1 : β (pt (t.equivFin ⟨x, hxt⟩)) y ≤ S y :=
      Finset.single_le_sum (f := fun a => β (pt a) y) (fun a _ => hβ0 (pt a) y)
        (Finset.mem_univ _)
    rw [hpt] at h1
    linarith [hUpos x y hyx]
  have hSs : A.SmoothFn S := by
    intro j
    have : (S ∘ (A.chart j).symm) = fun v => ∑ a, β (pt a) ((A.chart j).symm v) := rfl
    rw [this]
    exact ContDiffOn.sum fun a _ => hβs (pt a) j
  refine ⟨{
    m := t.card
    idx := fun a => A.pick (pt a)
    c := fun a => A.chart (A.pick (pt a)) (pt a)
    r := fun a => 3 * ε (pt a) / 4
    chi := fun a y => β (pt a) y / S y
    r_pos := fun a => by have := hε0 (pt a); positivity
    sub := fun a => (closedBall_subset_ball (by linarith [hε0 (pt a)])).trans (hεb (pt a))
    smooth := ?_
    supp := ?_
    nonneg := fun a y => div_nonneg (hβ0 _ y) (hS y).le
    sum_one := fun y => by rw [← Finset.sum_div]; exact div_self (hS y).ne' }⟩
  · intro a j v hv
    exact ((hβs (pt a) j v hv).div (hSs j v hv) (hS _).ne')
  · intro a
    set x := pt a
    have hKc : IsClosed ((A.chart (A.pick x)).symm '' K0 x) :=
      (A.isCompact_chartImage (isCompact_closedBall _ _) (hK0t x)).isClosed
    refine (closure_minimal ?_ hKc).trans ?_
    · intro y hy
      have hy' : β x y ≠ 0 := fun h0 => hy (by simp only [h0, zero_div])
      by_contra hK
      exact hy' (A.chiC_eq_zero (hbs x) hK)
    · rintro _ ⟨u, hu, rfl⟩
      refine ⟨(A.chart (A.pick x)).map_target (hK0t x hu), ?_⟩
      simp only [Set.mem_preimage]
      rw [(A.chart (A.pick x)).right_inv (hK0t x hu)]
      exact mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hu) (by linarith [hε0 x]))

end GlobalTheory.OTY
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.etaleSpace_descent_local_equivalence : ∀ (R : Type) [CommRing R] (F : Shv R) (T : Type 1) [Category.{0} T] (Cov : MorphismProperty T) [Cov.IsStableUnderComposition] (Φ Φ' : T ⥤ Spcᵒᵖ) (α : Φ' ⟶ Φ), Refines Cov (fun U X a => Hyp R Φ a ∧ Hyp R Φ' a) → (∀ (U : T) (n : ℤ) (x : H R (Φ.obj U).unop F n), ∃ (V : T) (g : U ⟶ V), Cov g ∧ ∃ y : H R (Φ'.obj V).unop F n, pull R (α.app V).unop F n y = pull R (Φ.map g).unop F n x) → (∀ (U : T) (n : ℤ) (y : H R (Φ'.obj U).unop F n), pull R (α.app U).unop F n y = 0 → ∃ (V : T) (g : U ⟶ V), Cov g ∧ pull R (Φ'.map g).unop F n y = 0) → ∀ U, Eqv R (α.app U).unop F := by
  first | (exact @GlobalTheory.EtC.Descent.main) | (exact GlobalTheory.EtC.Descent.main) | (intros; apply GlobalTheory.EtC.Descent.main <;> assumption)
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.etale_isLocalHomeomorph' : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (U : Set Y) (z : Y → V n), Etale A U z → IsLocalHomeomorph (fun y : U => z y) := by
  first | exact @GlobalTheory.OTY.etale_isLocalHomeomorph | exact GlobalTheory.OTY.etale_isLocalHomeomorph | (intros; apply GlobalTheory.OTY.etale_isLocalHomeomorph <;> assumption)
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.measure_compl_nonvanishingSet_eq_zero_of_dense : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (Λ : La) (τ : ι → Y → ℂ), A.IsSec Λ τ → Dense (nz A τ) → A.mu (nz A τ)ᶜ = 0 := by
  first | exact @GlobalTheory.zeroSet_null_of_dense_nz | exact GlobalTheory.zeroSet_null_of_dense_nz | (intros; apply GlobalTheory.zeroSet_null_of_dense_nz <;> assumption)
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.contDiffAt_chart_inverse_of_etale : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (U : Set Y) (z : Y → V n), Etale A U z → ∀ e : OpenPartialHomeomorph U (V n), IsChart n (fun y : U => z y) e → ∀ v ∈ e.target, ∀ i, ((e.symm v : U) : Y) ∈ (A.chart i).source → ContDiffAt ℂ ∞ (fun v' => A.chart i (e.symm v' : U)) v ∧ (∀ᶠ v' in 𝓝 v, ((e.symm v' : U) : Y) ∈ (A.chart i).source) ∧ ∀ ξ : V n, fderiv ℂ (fun v' => A.chart i (e.symm v' : U)) v (jz A z i (e.symm v : U) ξ) = ξ := by
  first | exact @GlobalTheory.OTY.etale_local_inverse | exact GlobalTheory.OTY.etale_local_inverse | (intros; apply GlobalTheory.OTY.etale_local_inverse <;> assumption)
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.smooth_and_smoothR_of_contDiffAt_in_charts : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (U : Set Y) (z : Y → V n), Etale A U z → (∀ u : Y → ℂ, (∀ x ∈ U, ∃ i, x ∈ (A.chart i).source ∧ ContDiffAt ℝ ∞ (u ∘ (A.chart i).symm) (A.chart i x)) → Smooth n (fun y : U => z y) (fun y : U => u y)) ∧ (∀ φ : Y → ℝ, (∀ x ∈ U, ∃ i, x ∈ (A.chart i).source ∧ ContDiffAt ℝ ∞ (φ ∘ (A.chart i).symm) (A.chart i x)) → SmoothR n (fun y : U => z y) (fun y : U => φ y)) := by
  first | exact @GlobalTheory.OTY.smooth_etale_of_smooth_in_charts | exact GlobalTheory.OTY.smooth_etale_of_smooth_in_charts | (intros; apply GlobalTheory.OTY.smooth_etale_of_smooth_in_charts <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.finitary_of_locally_bijective_from_filtered_functor : ∀ (R : Type) [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) (F : Shv R) (η : M ⟶ onRings F), PreservesFilteredColimitsOfSize.{0, 0} M → (∀ (A : CommRingCat.{0}) (x : (onRings F).obj A), ∃ (ι : Type) (_ : Finite ι) (B : ι → CommRingCat.{0}) (g : ∀ i, A ⟶ B i) (m : ∀ i, M.obj (B i)), (∀ i, (g i).hom.Etale) ∧ (∀ p : Spec A, ∃ i v, Spec.map (g i) v = p) ∧ ∀ i, (η.app (B i)).hom (m i) = ((onRings F).map (g i)).hom x) → (∀ (A : CommRingCat.{0}) (m : M.obj A), (η.app A).hom m = 0 → ∃ (ι : Type) (_ : Finite ι) (B : ι → CommRingCat.{0}) (g : ∀ i, A ⟶ B i), (∀ i, (g i).hom.Etale) ∧ (∀ p : Spec A, ∃ i v, Spec.map (g i) v = p) ∧ ∀ i, (M.map (g i)).hom m = 0) → Finitary F := by
  first
  | exact @GlobalTheory.EtC.FinitaryOfLocBij.finitary_of_locally_bijective
  | exact GlobalTheory.EtC.FinitaryOfLocBij.finitary_of_locally_bijective
  | (intros; apply GlobalTheory.EtC.FinitaryOfLocBij.finitary_of_locally_bijective <;> assumption)
end
