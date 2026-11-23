module

public import Formalism.RealPlaceAnalysis.Bundle001
public import Mathlib.Analysis.Matrix.Spectrum
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle005
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle013
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle007
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
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Basic.PEquiv
public import Mathlib.Data.Matrix.PEquiv

@[expose] public section

section

open Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants

namespace GlobalTheory.EigenPartialSum

theorem rank_add_le' {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    (A + B).rank ≤ A.rank + B.rank := by
  simp only [← Matrix.finrank_range_mulVecLin]
  rw [Matrix.mulVecLin_add]
  refine le_trans (Submodule.finrank_mono ?_)
    (Submodule.finrank_add_le_finrank_add_finrank (LinearMap.range A.mulVecLin)
      (LinearMap.range B.mulVecLin))
  rintro _ ⟨x, rfl⟩
  exact Submodule.add_mem_sup ⟨x, rfl⟩ ⟨x, rfl⟩

theorem rank_le_two_mul {n : ℕ} (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ)
    (h0 : ∀ a b, ε a = ε b → Y a b = 0) (c : Bool) :
    Y.rank ≤ 2 * (univ.filter fun a => ε a = c).card := by
  classical
  set P : Matrix (Fin n) (Fin n) ℂ := diagonal fun a => if ε a = c then 1 else 0 with hP
  have hY : Y = P * Y + Y * P := by
    ext a b
    simp only [hP, Matrix.add_apply, diagonal_mul, mul_diagonal]
    by_cases hab : ε a = ε b
    · simp [h0 a b hab]
    · by_cases ha : ε a = c
      · have hb : ¬ ε b = c := fun hb => hab (ha.trans hb.symm)
        simp [ha, hb]
      · have hb : ε b = c := by
          revert hab ha
          cases ε a <;> cases ε b <;> cases c <;> simp
        simp [ha, hb]
  have hr : P.rank = (univ.filter fun a => ε a = c).card := by
    rw [hP, rank_diagonal, Fintype.card_subtype]
    congr 1
    ext a
    simp
  calc Y.rank = (P * Y + Y * P).rank := by rw [← hY]
    _ ≤ (P * Y).rank + (Y * P).rank := rank_add_le' _ _
    _ ≤ P.rank + P.rank := add_le_add (rank_mul_le_left _ _) (rank_mul_le_right _ _)
    _ = _ := by rw [hr]; ring

theorem apply_eq_zero_of_inP {n : ℕ} {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ}
    (h : inP ε Y) (a b : Fin n) (hab : ε a = ε b) : Y a b = 0 := by
  have h1 := congrFun (congrFun h.2 a) b
  simp only [Jm, mul_diagonal, diagonal_mul, Matrix.neg_apply, hab] at h1
  cases hb : ε b <;> simp [hb] at h1
  · linear_combination (-1 / 2 : ℂ) * h1
  · linear_combination (1 / 2 : ℂ) * h1

theorem sum_sq_eigenvalues {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) (hY : Y.IsHermitian) :
    ∑ j, hY.eigenvalues j ^ 2 = hs Y := by
  have h1 : (Y * Y).trace = ((∑ j, hY.eigenvalues j ^ 2 : ℝ) : ℂ) := by
    conv_lhs => rw [hY.spectral_theorem, ← map_mul]
    rw [Unitary.conjStarAlgAut_apply, trace_mul_cycle, Unitary.coe_star_mul_self, one_mul,
      diagonal_mul_diagonal, trace_diagonal]
    simp [sq]
  have h2 : (Y * Y).trace = ((hs Y : ℝ) : ℂ) := by
    simp only [trace, diag_apply, Matrix.mul_apply, hs]
    push_cast
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    rw [← hY.apply j i, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  exact_mod_cast h1.symm.trans h2

theorem abs_sum_eigenvalues_le : ∀ (n : ℕ) (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ)
    (hY : Y.IsHermitian), inP ε Y → ∀ J : Finset (Fin n), |∑ j ∈ J, hY.eigenvalues j| ≤
      Real.sqrt (2 * ((min (univ.filter fun a => ε a = true).card
        (univ.filter fun a => ε a = false).card : ℕ) : ℝ)) * Real.sqrt (hs Y) := by
  intro n ε Y hY hP J
  classical
  set q : ℕ := min (univ.filter fun a => ε a = true).card
    (univ.filter fun a => ε a = false).card with hq
  have hr : Y.rank ≤ 2 * q := by
    have h1 := rank_le_two_mul ε Y (apply_eq_zero_of_inP hP) true
    have h2 := rank_le_two_mul ε Y (apply_eq_zero_of_inP hP) false
    omega
  set S := J.filter fun j => hY.eigenvalues j ≠ 0 with hS
  have hc : S.card ≤ 2 * q := by
    refine le_trans ?_ hr
    rw [hY.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
    exact card_le_card (filter_subset_filter _ (subset_univ _))
  have hc' : (S.card : ℝ) ≤ 2 * (q : ℝ) := by exact_mod_cast hc
  have hsum : ∑ j ∈ J, hY.eigenvalues j = ∑ j ∈ S, hY.eigenvalues j :=
    (sum_filter_ne_zero J).symm
  have hsq : ∑ j ∈ S, hY.eigenvalues j ^ 2 ≤ hs Y := by
    rw [← sum_sq_eigenvalues Y hY]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => sq_nonneg _
  rw [hsum, ← Real.sqrt_mul (by positivity)]
  refine Real.abs_le_sqrt (le_trans sq_sum_le_card_mul_sum_sq ?_)
  exact mul_le_mul hc' hsq (sum_nonneg fun _ _ => sq_nonneg _) (by positivity)

end GlobalTheory.EigenPartialSum
end

section

open Matrix

namespace GlobalTheory

theorem hform_sub_left_flag {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A)
    (J : Matrix n n A) (x x' y : n → A) :
    Formalism.UG.hform σ J (x - x') y = Formalism.UG.hform σ J x y - Formalism.UG.hform σ J x' y := by
  unfold Formalism.UG.hform
  simp only [Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

theorem hform_sub_right_flag {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A)
    (J : Matrix n n A) (x y y' : n → A) :
    Formalism.UG.hform σ J x (y - y') = Formalism.UG.hform σ J x y - Formalism.UG.hform σ J x y' := by
  unfold Formalism.UG.hform
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

private theorem hform_eq_dotProduct_mulVec {K : Type} [CommRing K] {n : ℕ} (σ : K →+* K)
    (J : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
    Formalism.UG.hform σ J x y = (fun i => σ (x i)) ⬝ᵥ (J *ᵥ y) := by
  unfold Formalism.UG.hform
  simp only [dotProduct, mulVec, Finset.mul_sum, mul_assoc]

private theorem hform_mulVec_eq_of_unitary {K : Type} [CommRing K] {n : ℕ} (σ : K →+* K)
    (J γ : Matrix (Fin n) (Fin n) K) (hγ : Formalism.UG.cT σ γ * J * γ = J) (x y : Fin n → K) :
    Formalism.UG.hform σ J (γ *ᵥ x) (γ *ᵥ y) = Formalism.UG.hform σ J x y := by
  rw [hform_eq_dotProduct_mulVec, hform_eq_dotProduct_mulVec]
  have h1 : (fun i => σ ((γ *ᵥ x) i)) = γ.map σ *ᵥ (fun i => σ (x i)) := by
    funext i
    exact RingHom.map_mulVec σ γ x i
  unfold Formalism.UG.cT at hγ
  rw [Matrix.mul_assoc] at hγ
  rw [h1, ← vecMul_transpose (γ.map σ), ← dotProduct_mulVec]
  simp only [mulVec_mulVec, hγ]

theorem lowering_difference_of_isometries :
    ∀ (K R : Type) [Field K] [StarRing K] [CommRing R] [Algebra R K] (n : ℕ) (J : Matrix (Fin n) (Fin n) K), Formalism.UG.IsHerm (starRingEnd K) J → ∀ (a : ℕ) (G : ℕ → Submodule R (Fin n → K)), G 0 = ⊥ → Monotone G → (∀ p ≤ 2 * a + 1, ∀ y, y ∈ G (2 * a + 1 - p) ↔ y ∈ G (2 * a + 1) ∧ ∀ s ∈ G p, Formalism.UG.hform (starRingEnd K) J s y = 0) → ∀ γ γ' : Matrix (Fin n) (Fin n) K, Formalism.UG.cT (starRingEnd K) γ * J * γ = J → Formalism.UG.cT (starRingEnd K) γ' * J * γ' = J → (∀ p ≤ 2 * a, ∀ y ∈ G (p + 1), (γ - 1) *ᵥ y ∈ G p) → (∀ p ≤ 2 * a, ∀ y ∈ G (p + 1), (γ' - 1) *ᵥ y ∈ G p) → ∀ c : ℕ, 1 ≤ c → (∀ q p : ℕ, q < p → q + p ≤ 2 * a → p - q < c → ∀ y ∈ G (p + 1), (γ - γ') *ᵥ y ∈ G q) → (∀ p ≤ 2 * a + 1, ∀ y ∈ G p, (γ - γ') *ᵥ y ∈ G (p - c)) ∧ ∀ p p' : ℕ, p ≤ 2 * a → p' ≤ 2 * a → p + p' ≤ 2 * a + c → ∀ x ∈ G (p + 1), ∀ y ∈ G (p' + 1), Formalism.UG.hform (starRingEnd K) J ((γ - γ') *ᵥ x) y + Formalism.UG.hform (starRingEnd K) J x ((γ - γ') *ᵥ y) = 0 := by
  intro K R _ _ _ _ n J _ a G hG0 hGm hdual γ γ' hγ hγ' hl hl' c hc hlow
  set hf := Formalism.UG.hform (starRingEnd K) J with hhf
  have hL : ∀ x x' y, hf (x - x') y = hf x y - hf x' y := fun x x' y => hform_sub_left_flag _ J x x' y
  have hR : ∀ x y y', hf x (y - y') = hf x y - hf x y' := fun x y y' => hform_sub_right_flag _ J x y y'
  have iso : ∀ x y, hf (γ *ᵥ x) (γ *ᵥ y) = hf x y := hform_mulVec_eq_of_unitary _ J γ hγ
  have iso' : ∀ x y, hf (γ' *ᵥ x) (γ' *ᵥ y) = hf x y := hform_mulVec_eq_of_unitary _ J γ' hγ'
  have h0 : ∀ v, hf 0 v = 0 := fun v => by simp [hhf, Formalism.UG.hform]
  have mem0 : ∀ y ∈ G 0, y = 0 := fun y hy => by
    rw [hG0] at hy
    exact (Submodule.mem_bot R).1 hy
  have orth : ∀ m m', m + m' ≤ 2 * a + 1 → ∀ u ∈ G m, ∀ v ∈ G m', hf u v = 0 := by
    intro m m' hmm u hu v hv
    exact ((hdual m (by omega) v).1 (hGm (by omega) hv)).2 u hu
  have key : ∀ x y, hf ((γ - γ') *ᵥ x) (γ *ᵥ y) + hf (γ' *ᵥ x) ((γ - γ') *ᵥ y) = 0 := by
    intro x y
    rw [sub_mulVec, sub_mulVec, hL, hR, iso, iso']
    ring
  have base : ∀ p ≤ 2 * a + 1, ∀ y ∈ G p, (γ - γ') *ᵥ y ∈ G (p - 1) := by
    intro p hp y hy
    rcases Nat.eq_zero_or_pos p with rfl | hp0
    · rw [mem0 y hy, mulVec_zero]
      exact zero_mem _
    · obtain ⟨p0, rfl⟩ : ∃ p0, p = p0 + 1 := ⟨p - 1, by omega⟩
      have e : (γ - γ') *ᵥ y = (γ - 1) *ᵥ y - (γ' - 1) *ᵥ y := by
        simp only [sub_mulVec, one_mulVec]
        abel
      rw [e, Nat.add_sub_cancel]
      exact sub_mem (hl p0 (by omega) y hy) (hl' p0 (by omega) y hy)
  have main1 : ∀ p, p ≤ 2 * a + 1 → ∀ y ∈ G p, (γ - γ') *ᵥ y ∈ G (p - c) := by
    intro p
    induction p using Nat.strong_induction_on with
    | _ p ih =>
      intro hp y hy
      by_cases hA : c = 1 ∨ p ≤ 1
      · exact hGm (by omega) (base p hp y hy)
      by_cases hB : 2 * p ≤ 2 * a + 1 + c ∨ p < c
      · obtain ⟨p0, rfl⟩ : ∃ p0, p = p0 + 1 := ⟨p - 1, by omega⟩
        exact hlow (p0 + 1 - c) p0 (by omega) (by omega) (by omega) y hy
      have hγy : γ *ᵥ y ∈ G p := by
        have e1 : γ *ᵥ y = (γ - 1) *ᵥ y + y := by
          simp only [sub_mulVec, one_mulVec]
          abel
        rw [e1]
        refine add_mem (hGm (Nat.sub_le p 1) (hl (p - 1) (by omega) y ?_)) hy
        rwa [Nat.sub_add_cancel (by omega : 1 ≤ p)]
      have inner : ∀ j, j ≤ 2 * a + 1 - (p - c) → ∀ s ∈ G j, hf s ((γ - γ') *ᵥ y) = 0 := by
        intro j
        induction j with
        | zero =>
          intro _ s hs
          rw [mem0 s hs, h0]
        | succ j ihj =>
          intro hj s hs
          have k := key s y
          have ha : hf ((γ' - 1) *ᵥ s) ((γ - γ') *ᵥ y) =
              hf (γ' *ᵥ s) ((γ - γ') *ᵥ y) - hf s ((γ - γ') *ᵥ y) := by
            rw [sub_mulVec γ' 1, one_mulVec, hL]
          have hz1 := ihj (by omega) _ (hl' j (by omega) s hs)
          have hz2 := orth (j + 1 - c) p (by omega) _ (ih (j + 1) (by omega) (by omega) s hs) _ hγy
          linear_combination k + ha - hz1 - hz2
      have hd := (hdual (2 * a + 1 - (p - c)) (by omega) ((γ - γ') *ᵥ y)).2
        ⟨hGm (by omega) (base p hp y hy), fun s hs => inner _ le_rfl s hs⟩
      have e2 : 2 * a + 1 - (2 * a + 1 - (p - c)) = p - c := by omega
      rwa [e2] at hd
  refine ⟨main1, ?_⟩
  intro p p' hp hp' hpp x hx y hy
  have e3 : hf ((γ - γ') *ᵥ x) ((γ - 1) *ᵥ y) = 0 :=
    orth (p + 1 - c) p' (by omega) _ (main1 (p + 1) (by omega) x hx) _ (hl p' hp' y hy)
  have e4 : hf ((γ' - 1) *ᵥ x) ((γ - γ') *ᵥ y) = 0 :=
    orth p (p' + 1 - c) (by omega) _ (hl' p hp x hx) _ (main1 (p' + 1) (by omega) y hy)
  rw [sub_mulVec γ 1, one_mulVec, hR] at e3
  rw [sub_mulVec γ' 1, one_mulVec, hL] at e4
  linear_combination key x y - e3 - e4

end GlobalTheory
end

section

open ValuativeRel

namespace GlobalTheory.SmulIntegralDenominator

theorem exists_smul_integral {K : Type} [Field K] [ValuativeRel K]
    {R : Type} [CommRing R] [Algebra K R] [Module.Finite K R] (x : R) :
    ∃ e : 𝒪[K], e ≠ 0 ∧ IsIntegral 𝒪[K] (e • x) := by
  have h1 : IsAlgebraic K x := (Algebra.IsIntegral.isIntegral (R := K) x).isAlgebraic
  have h2 : IsAlgebraic 𝒪[K] x := (IsFractionRing.isAlgebraic_iff 𝒪[K] K R).mpr h1
  exact h2.exists_integral_multiple

theorem common_denominator {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
    {R : Type} [CommRing R] [Algebra K R] [TopologicalSpace R] (L : Formalism.MainNotions.S.Loc.LocE K R)
    {ι : Type} [Fintype ι] (f : ι → R) :
    ∃ e ∈ Valuation.integer (ValuativeRel.valuation K), e ≠ (0 : K) ∧
      ∀ i : ι, ∃ o ∈ L.O, f i = algebraMap K R e⁻¹ * o := by
  classical
  haveI : Module.Finite K R := Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)
  choose e he0 he using fun i => exists_smul_integral (K := K) (f i)
  have hP : (∏ i, e i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => he0 i
  have hP' : ((∏ i, e i : 𝒪[K]) : K) ≠ 0 := fun h => hP (Subtype.ext h)
  refine ⟨((∏ i, e i : 𝒪[K]) : K), (∏ i, e i).2, hP', fun i => ?_⟩
  refine ⟨(∏ i, e i) • f i, ?_, ?_⟩
  · rw [L.O_def, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), mul_smul]
    exact (he i).smul _
  · rw [Subring.smul_def, Algebra.smul_def, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hP', map_one,
      one_mul]

theorem main : (let d1 : {K : Type} → [inst : Field K] → [inst_1 : ValuativeRel K] → [inst_2 : TopologicalSpace K] → {R : Type} → [inst_3 : CommRing R] → [inst_4 : Algebra K R] → [inst_5 : TopologicalSpace R] → Formalism.MainNotions.S.Loc.LocE K R → K → R → Prop := @(fun {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] {R : Type} [CommRing R] [Algebra K R] [TopologicalSpace R] (L : Formalism.MainNotions.S.Loc.LocE K R) (γ : K) (x : R) ↦ ∃ o ∈ Formalism.MainNotions.S.Loc.LocE.O L, x = (Algebra.algebraMap K R : K → R) γ * o); ∀ {K : Type} [inst : Field K] [inst_1 : ValuativeRel K] [inst_2 : TopologicalSpace K] {R : Type} [inst_3 : CommRing R] [inst_4 : Algebra K R] [inst_5 : TopologicalSpace R] (L : Formalism.MainNotions.S.Loc.LocE K R) {ι : Type} [Fintype ι] (f : ι → R), ∃ e ∈ Valuation.integer (ValuativeRel.valuation K), e ≠ (0 : K) ∧ ∀ (i : ι), d1 L e⁻¹ (f i)) := by
  intro d1 K _ _ _ R _ _ _ L ι _ f
  obtain ⟨e, he, he0, h⟩ := common_denominator L f
  exact ⟨e, he, he0, fun i => by obtain ⟨o, ho, hf⟩ := h i; exact ⟨o, ho, hf⟩⟩

end GlobalTheory.SmulIntegralDenominator
end

section

open ValuativeRel MeasureTheory ComplexConjugate Formalism.MainNotions.S.Loc
open scoped ComplexOrder

namespace GlobalTheory.SgLoc.PtAlg

variable {E : Type} [CommRing E]

theorem ptEntryL_append (bs : List (Eˣ × ℕ+)) (t : Eˣ) (s : ℕ+) :
    ∀ (m : ℕ), (bs.map (fun b => (b.2 : ℕ))).sum = m → ∀ a b : ℕ,
      ptEntryL (bs ++ [(t, s)]) a b =
        if a < m ∧ b < m then ptEntryL bs a b
        else if m ≤ a ∧ m ≤ b ∧ a + b + 1 = 2 * m + s then (t : E) else 0 := by
  induction bs with
  | nil =>
    intro m hm a b
    simp only [List.map_nil, List.sum_nil] at hm
    subst hm
    simp only [List.nil_append, ptEntryL]
    split_ifs <;> first | rfl | omega
  | cons hd bs ih =>
    obtain ⟨t', s'⟩ := hd
    intro m hm a b
    simp only [List.map_cons, List.sum_cons] at hm
    simp only [List.cons_append, ptEntryL]
    rw [ih _ rfl]
    split_ifs <;> first | rfl | omega

theorem mat_snoc {m : ℕ} (h : Pt E m) (t : Eˣ) (s : ℕ+) (a b : Fin (m + s)) :
    (h.snoc t s).mat a b =
      if hab : (a : ℕ) < m ∧ (b : ℕ) < m then h.mat ⟨a, hab.1⟩ ⟨b, hab.2⟩
      else if m ≤ (a : ℕ) ∧ m ≤ (b : ℕ) ∧ (a : ℕ) + b + 1 = 2 * m + s then (t : E) else 0 := by
  show ptEntryL (h.blocks ++ [(t, s)]) a b = _
  rw [ptEntryL_append h.blocks t s m h.size]
  split_ifs <;> rfl

theorem det_snoc_eq {m : ℕ} (h : Pt E m) (t : Eˣ) (s : ℕ+) :
    (h.snoc t s).mat.det =
      h.mat.det * (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin s)) : ℤˣ) : ℤ) *
        (t : E) ^ (s : ℕ)) := by
  have key : Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm (h.snoc t s).mat =
      Matrix.fromBlocks h.mat 0 0
        ((t : E) • (Fin.revPerm : Equiv.Perm (Fin s)).permMatrix E) := by
    ext (i | i) (j | j) <;>
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, mat_snoc,
        finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.val_castAdd, Fin.val_natAdd,
        Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
        Matrix.fromBlocks_apply₂₂, Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul] <;>
      have hi := i.isLt <;> have hj := j.isLt
    · rw [dite_eq_left ⟨hi, hj⟩]
    · rw [dite_eq_right (by omega), ite_eq_right (by omega)]
    · rw [dite_eq_right (by omega), ite_eq_right (by omega)]
    · rw [dite_eq_right (by omega)]
      simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
        Option.mem_def, Option.some.injEq, Fin.revPerm_apply]
      by_cases hij : Fin.rev i = j
      · rw [ite_eq_left (by rw [← hij, Fin.val_rev]; omega), ite_eq_left hij, mul_one]
      · rw [ite_eq_right (fun hc => hij (Fin.ext (by rw [Fin.val_rev]; omega))),
          ite_eq_right hij, mul_zero]
  have hdet := congrArg Matrix.det key
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_smul,
    Matrix.det_permutation, Fintype.card_fin] at hdet
  rw [hdet]
  ring

theorem det_snoc {m : ℕ} (h : Pt E m) (t : Eˣ) (s : ℕ+) :
    (h.snoc t s).mat.det = h.mat.det * (t : E) ^ (s : ℕ) ∨
      (h.snoc t s).mat.det = -(h.mat.det * (t : E) ^ (s : ℕ)) := by
  rw [det_snoc_eq]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin s))) with h1 | h1
  · left
    rw [h1]
    simp
  · right
    rw [h1]
    simp

private theorem isUnit_det_of_mem_UH_Hpk (bs : List (Eˣ × ℕ+)) :
    ∀ (n : ℕ) (hn : (bs.map (fun b => (b.2 : ℕ))).sum = n),
      IsUnit (Pt.mat (⟨bs, hn⟩ : Pt E n)).det := by
  induction bs using List.reverseRecOn with
  | nil =>
    intro n hn
    have hn' : n = 0 := by rw [← hn]; simp
    subst hn'
    simp
  | append_singleton bs x ih =>
    obtain ⟨t, s⟩ := x
    intro n hn
    have hn' : n = (bs.map (fun b => (b.2 : ℕ))).sum + s := by rw [← hn]; simp
    subst hn'
    have hu := ih _ rfl
    change IsUnit (Pt.snoc (⟨bs, rfl⟩ : Pt E _) t s).mat.det
    rcases det_snoc (⟨bs, rfl⟩ : Pt E _) t s with h1 | h1
    · rw [h1]
      exact hu.mul ((Units.isUnit t).pow _)
    · rw [h1]
      exact (hu.mul ((Units.isUnit t).pow _)).neg

theorem isUnit_det {m : ℕ} (h : Pt E m) : IsUnit h.mat.det := by
  exact isUnit_det_of_mem_UH_Hpk h.blocks m h.size

end GlobalTheory.SgLoc.PtAlg

namespace GlobalTheory.SgLoc

end GlobalTheory.SgLoc
end

section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.PlueckerBound

theorem norm_det_inner_le {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {b : ℕ}
    (u w : Fin b → E) :
    ‖(Matrix.of fun a a' => ⟪u a, w a'⟫_ℂ).det‖ ≤ (∏ a, ‖u a‖) * ∏ a, ‖w a‖ := by
  have h := GlobalTheory.Hadamard.norm_det_apply_le (𝕜 := ℂ) (fun a => innerSL ℂ (u a)) w
  simp only [innerSL_apply_apply, innerSL_apply_norm] at h
  rw [mul_comm]
  exact h

theorem det_inner_sum_smul {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {b : ℕ}
    (u v : Fin b → E) (t : Matrix (Fin b) (Fin b) ℂ) :
    (Matrix.of fun a a' => ⟪u a, ∑ i, t i a' • v i⟫_ℂ).det
      = (Matrix.of fun a a' => ⟪u a, v a'⟫_ℂ).det * t.det := by
  rw [← Matrix.det_mul]
  congr 1
  ext a a'
  simp [Matrix.mul_apply, inner_sum, inner_smul_right, mul_comm]

theorem norm_det_inner_le_of_det_eq_one (n b : ℕ) (v u : Fin b → EuclideanSpace ℂ (Fin n))
    (t : Matrix (Fin b) (Fin b) ℂ) (ht : t.det = 1)
    (_h : ∀ a a', a ≠ a' → ⟪∑ i, t i a • v i, ∑ i, t i a' • v i⟫_ℂ = 0) :
    ‖(Matrix.of fun a a' => ⟪u a, v a'⟫_ℂ).det‖ ≤ (∏ a, ‖u a‖) * ∏ a, ‖∑ i, t i a • v i‖ := by
  have h := norm_det_inner_le u (fun a => ∑ i, t i a • v i)
  rwa [det_inner_sum_smul, ht, mul_one] at h

end GlobalTheory.PlueckerBound
end

section

open MeasureTheory

theorem _root_.GlobalTheory.T.extend_ae_linear_of_local_sq_bound_dense : ∀ {X : Type} [MeasurableSpace X] (μ : Measure X) (K : ℕ → Set X),
    (∀ n, MeasurableSet (K n)) → ⋃ n, K n = Set.univ →
    ∀ {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H]
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (D : Submodule ℂ H), Dense (D : Set H) → ∀ F : H → X → E,
    (∀ u ∈ D, ∀ u' ∈ D, F (u + u') =ᵐ[μ] fun x => F u x + F u' x) →
    (∀ (b : ℂ), ∀ u ∈ D, F (b • u) =ᵐ[μ] fun x => b • F u x) →
    (∀ n, ∃ C : ℝ, ∀ u ∈ D, AEStronglyMeasurable (F u) (μ.restrict (K n)) ∧
      ∫⁻ x in K n, (‖F u x‖₊ : ENNReal) ^ 2 ∂μ ≤ ENNReal.ofReal (C * ‖u‖ ^ 2)) →
    ∃ T : H → X → E, (∀ u ∈ D, T u = F u) ∧
      (∀ u u' : H, T (u + u') =ᵐ[μ] fun x => T u x + T u' x) ∧
      (∀ (b : ℂ) (u : H), T (b • u) =ᵐ[μ] fun x => b • T u x) ∧
      (∀ n, ∃ C : ℝ, ∀ u : H, AEStronglyMeasurable (T u) (μ.restrict (K n)) ∧
        ∫⁻ x in K n, (‖T u x‖₊ : ENNReal) ^ 2 ∂μ ≤ ENNReal.ofReal (C * ‖u‖ ^ 2)) := by
  first | exact @GlobalTheory.extend_ae_linear_of_local_sq | exact GlobalTheory.extend_ae_linear_of_local_sq | (intros; apply GlobalTheory.extend_ae_linear_of_local_sq <;> assumption)
end

section

open MeasureTheory Matrix Filter Topology

theorem _root_.GlobalTheory.T.tendsto_integral_normalised_pow_smul_of_unique_peak : ∀ (X : Type) [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X), IsProbabilityMeasure μ → ∀ (K : Set X) (x₀ : X) (f : X → ℝ), IsCompact K → μ Kᶜ = 0 → x₀ ∈ K → (∀ U : Set X, IsOpen U → x₀ ∈ U → 0 < μ U) → Continuous f → f x₀ = 1 → (∀ x ∈ K, 0 ≤ f x ∧ f x ≤ 1) → (∀ U ∈ 𝓝 x₀, ∃ δ < 1, ∀ x ∈ K, x ∉ U → f x ≤ δ) → ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (F : X → E), ContinuousOn F K → Tendsto (fun m : ℕ => ∫ x, ((f x ^ m / ∫ y, f y ^ m ∂μ : ℝ) : ℂ) • F x ∂μ) atTop (𝓝 (F x₀)) := by
  first | exact @GlobalTheory.tendsto_integral_normalised_pow_peak | exact GlobalTheory.tendsto_integral_normalised_pow_peak | (intros; apply GlobalTheory.tendsto_integral_normalised_pow_peak <;> assumption)
end
