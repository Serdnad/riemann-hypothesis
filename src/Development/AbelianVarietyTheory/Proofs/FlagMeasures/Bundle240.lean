module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle006
public import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle105
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle141
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle143
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle230
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle142
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle013
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle232
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHasFlag
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneParameterConjugationBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients

@[expose] public section

section

noncomputable section

namespace GlobalTheory.Diag.PG

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

theorem data_of_rows (eps CD : ℝ) (he : 0 < eps) (he' : eps < 1 / 52) (hCD : 3 ≤ CD) :
    ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (D : D7) (Cg C0 : ℝ), Glob0 D x eps CD Cg → Nodes D x eps → ArithmeticConditionsOfDatum D →
      DuWin D C0 → StandingNumericalData D C0 := by
  obtain ⟨x1, hx1⟩ := GlobalTheory.T.globalRankNumberBounds_size_comparisons eps CD he he' hCD 1 one_pos
  refine ⟨max x1 1, fun x hx D Cg C0 hG hN hA hW => ?_⟩
  have hxx1 : x1 ≤ x := le_trans (le_max_left _ _) hx
  have hxone : 1 ≤ x := le_trans (le_max_right _ _) hx
  obtain ⟨-, -, -, h12, -⟩ := hx1 x hxx1 _ _ _ _ _ hG.nums
  have hk : 5 ≤ D.R.k := by
    have := D.R.two_le_m
    have := D.R.m_add_three_le_k
    omega
  have hm2 := D.R.two_le_m
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl

  have hF : ∀ {n : ℕ} (g : Fin n → ℚ) (a b : ℕ) (ha : a < n) (hb : b < n), a = b →
      g ⟨a, ha⟩ = g ⟨b, hb⟩ := by
    intro n g a b ha hb h
    subst h
    rfl

  have huO : ∀ u τ (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ D.R.k),
      Formalism.MainNotions.S.uOne D u τ i = (((D.hcW u τ).u ⟨i - 1, by omega⟩ : ℚ) : ℝ) := by
    intro u τ i h1 h2
    unfold Formalism.MainNotions.S.uOne Formalism.MainNotions.S.uS
    rw [dite_eq_left ⟨h1, h2⟩]
  have hvO : ∀ τ (l : ℕ) (h1 : 1 ≤ l) (h2 : l ≤ D.R.k - 1),
      Formalism.MainNotions.S.vOne D τ l = (((D.hc τ).v ⟨l - 1, by omega⟩ : ℚ) : ℝ) := by
    intro τ l h1 h2
    unfold Formalism.MainNotions.S.vOne
    rw [dite_eq_left ⟨h1, h2⟩]
  have hbO : ∀ τ, Formalism.MainNotions.S.bOne D τ 1 = bFirst D τ := by
    intro τ
    unfold Formalism.MainNotions.S.bOne bFirst
    rw [dite_eq_left ⟨le_rfl, by have := D.R.two_le_m; omega⟩]
  have hu1 : ∀ u τ, Formalism.MainNotions.S.uOne D u τ 1 = uFirst D τ := by
    intro u τ
    rw [huO u τ 1 le_rfl (by omega)]
    unfold uFirst
    exact congrArg (fun q : ℚ => (q : ℝ))
      ((hF _ (1 - 1) 0 _ (by omega) (by norm_num)).trans (D.hcW_first u τ (by omega)))
  have huk : ∀ u τ, Formalism.MainNotions.S.uOne D u τ D.R.k = uLast D τ := by
    intro u τ
    rw [huO u τ D.R.k (by omega) le_rfl]
    unfold uLast
    exact congrArg (fun q : ℚ => (q : ℝ)) (D.hcW_last u τ (by omega))
  have hv1 : ∀ τ, Formalism.MainNotions.S.vOne D τ 1 = vFirst D τ := by
    intro τ
    rw [hvO τ 1 le_rfl (by omega)]
    unfold vFirst
    exact congrArg (fun q : ℚ => (q : ℝ)) (hF _ _ _ _ _ (by norm_num))
  have hvk : ∀ τ, Formalism.MainNotions.S.vOne D τ (D.R.k - 1) = vLast D τ := by
    intro τ
    rw [hvO τ (D.R.k - 1) (by omega) le_rfl]
    unfold vLast
    exact congrArg (fun q : ℚ => (q : ℝ)) (hF _ _ _ _ _ (by omega))
  have hDel : (0 : ℝ) < D.s.Del := by exact_mod_cast D.s.Del_pos
  have hkDel : (0 : ℝ) ≤ (D.R.k : ℝ) * D.s.Del := mul_nonneg (Nat.cast_nonneg _) hDel.le

  have hbx : 1 ≤ bx x eps := by
    unfold bx
    exact Real.one_le_exp (Real.rpow_nonneg (by linarith) _)
  have hg : ∀ i, 2 ≤ D.host.g i := by
    intro i
    have h := (hG.g_win i).1
    have hk' : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hk
    have h5 : (5 : ℝ) ≤ (D.R.k : ℝ) * bx x eps := by nlinarith
    have h2 : (2 : ℝ) ≤ ((D.R.k : ℝ) * bx x eps) ^ 8 :=
      calc (2 : ℝ) ≤ 5 := by norm_num
        _ ≤ (D.R.k : ℝ) * bx x eps := h5
        _ ≤ ((D.R.k : ℝ) * bx x eps) ^ 8 := le_self_pow₀ (by linarith) (by norm_num)
    exact_mod_cast h2.trans h
  unfold Formalism.MainNotions.S.StandingNumericalData
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hW, hA.2.1, hA.2.2.1, hA.2.2.2, ?_⟩
  ·
    intro τ l h1 h2
    rw [hvO τ l h1 h2]
    exact hG.cloud τ ⟨l - 1, by omega⟩
  ·
    intro u l h1 h2
    have key : ∀ τ, Formalism.MainNotions.S.uOne D u τ (l + 1) = Formalism.MainNotions.S.vOne D τ l - 1 / 2 -
        (if D.s.letter u ⟨l - 1, by omega⟩ then (D.s.Del : ℝ) else 0) := by
      intro τ
      rw [huO u τ (l + 1) (by omega) (by omega), hvO τ l h1 (by omega)]
      have e := D.s.u_letter u τ (l - 1) (by omega)
      rw [D.hcW_v u τ] at e
      have e' : (D.hcW u τ).u ⟨l + 1 - 1, by omega⟩ = (D.hcW u τ).u ⟨l - 1 + 1, by omega⟩ :=
        hF _ _ _ _ _ (by omega)
      rw [e', e]
      split_ifs <;> push_cast <;> ring
    by_cases hL : D.s.letter u ⟨l - 1, by omega⟩ = true
    · right
      intro τ
      rw [key τ, if_pos hL]
    · left
      intro τ
      rw [key τ, if_neg hL]
      ring
  ·
    intro u τ
    rw [hu1 u τ, hv1 τ]
    by_cases ht : Top D τ
    · have h1 := (hN.top τ ht).1
      have h2 := (hG.cloud τ ⟨0, by omega⟩).2
      have hvF : vFirst D τ = (((D.hc τ).v ⟨0, by omega⟩ : ℚ) : ℝ) := by
        unfold vFirst
        rfl
      rw [hvF]
      nlinarith
    · exact (hG.off τ ht).1
  ·
    intro u τ ht
    rw [hu1 u τ, hv1 τ]
    exact (hG.off τ ht).2.1
  ·
    intro u τ ht
    rw [huk u τ, hvk τ]
    exact (hG.off τ ht).2.2
  ·
    intro τ ht
    unfold Formalism.MainNotions.S.bTop
    rw [huk D.u₀ τ, hbO τ]
    obtain ⟨-, -, h3, h4⟩ := hN.top τ ht
    constructor <;> linarith
  ·
    intro u τ
    constructor
    · intro i hi
      have hl : Formalism.MainNotions.S.lamS D.R (D.hc τ) ⟨i, by omega⟩ = (((D.hcW u τ).v ⟨i, by omega⟩ : ℚ) : ℝ) := by
        unfold Formalism.MainNotions.S.lamS
        rw [dite_eq_left (show i < D.R.k - 1 by omega), D.hcW_v u τ]
      rw [hl]
      unfold Formalism.MainNotions.S.uS
      exact ⟨by exact_mod_cast (D.hcW u τ).u_gt_v ⟨i, by omega⟩,
        by exact_mod_cast (D.hcW u τ).v_gt_u ⟨i, by omega⟩⟩
    · intro h
      have hm : 0 < D.R.m := by
        have := D.R.two_le_m
        omega
      have hl : Formalism.MainNotions.S.lamS D.R (D.hc τ) ⟨D.R.k - 1, by omega⟩ =
          -(((D.hcW u τ).b ⟨0, hm⟩ : ℚ) : ℝ) := by
        unfold Formalism.MainNotions.S.lamS
        rw [dite_eq_right (show ¬ (D.R.k - 1 < D.R.k - 1) by omega),
          dite_eq_left (show D.R.k - 1 - (D.R.k - 1) < D.R.m by omega), D.hcW_b u τ]
        exact congrArg (fun q : ℚ => -(q : ℝ)) (hF _ _ _ _ _ (by simp))
      rw [hl]
      unfold Formalism.MainNotions.S.uS
      exact_mod_cast (D.hcW u τ).u_last_gt h hm
  ·
    intro u u' hne τ heq
    have hl : D.s.letter u ≠ D.s.letter u' := fun h => hne (D.s.letter_inj h)
    obtain ⟨⟨j, hj⟩, hjl⟩ := Function.ne_iff.mp hl
    have e := congrFun heq ⟨j + 1, by omega⟩
    simp only [Formalism.MainNotions.S.uS] at e
    have e' : (D.hcW u τ).u ⟨j + 1, by omega⟩ = (D.hcW u' τ).u ⟨j + 1, by omega⟩ := by
      exact_mod_cast e
    rw [D.s.u_letter u τ j hj, D.s.u_letter u' τ j hj, D.hcW_v, D.hcW_v] at e'
    have hQ := D.s.Del_pos
    cases h1 : D.s.letter u ⟨j, hj⟩ <;> cases h2 : D.s.letter u' ⟨j, hj⟩ <;>
      simp only [h1, h2] at e' hjl <;> simp at e' hjl <;> linarith
  ·
    intro u
    exact ⟨hA.1 u, Formalism.MainNotions.S.T_mod D u⟩
  ·
    intro u
    exact Formalism.MainNotions.S.ne_of_mod (hg 0) (hg 1) (Formalism.MainNotions.S.T_mod D u)

end GlobalTheory.Diag.PG

end
end

section

noncomputable section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt.NormalPos

section
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}

theorem mem_smul_iff (s : V ≃ₗ[K] V) (Λ : Submodule (𝓞 K) V) (y : V) :
    y ∈ s • Λ ↔ ∃ x ∈ Λ, s x = y := by
  rw [Submodule.mem_smul_pointwise_iff_exists]
  rfl

theorem smul_inf_eq (s : V ≃ₗ[K] V) (Λ : Submodule (𝓞 K) V) (S : Submodule K V)
    (h : ∀ y ∈ S, s y = y) : (s • Λ) ⊓ rs (𝓞 K) S = Λ ⊓ rs (𝓞 K) S := by
  ext y
  simp only [Submodule.mem_inf, Submodule.restrictScalars_mem, mem_smul_iff]
  constructor
  · rintro ⟨⟨x, hx, hxy⟩, hy⟩
    have : x = y := s.injective (hxy.trans (h y hy).symm)
    exact ⟨this ▸ hx, hy⟩
  · rintro ⟨hx, hy⟩
    exact ⟨⟨y, hx, h y hy⟩, hy⟩

theorem line_le (A : Submodule (𝓞 K) K) (v : V) (S : Submodule K V) (hv : v ∈ S) :
    line A v ≤ rs (𝓞 K) S := by
  rintro _ ⟨t, -, rfl⟩
  exact S.smul_mem t hv

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem e_mem_II (N : NF H r) (a : Fin r) (ha : N.j ≤ a.val) : N.F.e a.castSucc ∈ II N.F N.F' := by
  have hc : N.c ≠ 0 := by
    intro h
    have := N.c_norm
    rw [h, zero_mul] at this
    exact zero_ne_one this
  refine ⟨Submodule.subset_span ⟨a, a.2, rfl⟩, ?_⟩
  have h1 : N.F'.e a.castSucc ∈ N.F'.X := Submodule.subset_span ⟨a, a.2, rfl⟩
  have h2 := N.F'.X.smul_mem N.c⁻¹ h1
  rwa [N.same a.castSucc ha, smul_smul, inv_mul_cancel₀ hc, one_smul] at h2

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem isotropicMeet_le_jointSpan (N : NF H r) : II N.F N.F' ≤ V0 N.F N.F' :=
  inf_le_left.trans (le_sup_left.trans le_sup_left)

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem eq_zero_of_mem (N : NF H r)
    (hrad : ∀ v ∈ V0 N.F N.F', (∀ w ∈ V0 N.F N.F', H.B v w = 0) ↔ v ∈ II N.F N.F')
    (d : V) (hd : d ∈ N.Ist) (hd' : d ∈ V0 N.F N.F') : d = 0 := by
  let φ : V →ₗ[K] V := ∑ a ∈ Finset.univ.filter (fun a : Fin r => N.j ≤ a.val),
    (H.B.flip (N.F.e a.castSucc)).smulRight (N.ist a)
  have h1 : N.Ist ≤ LinearMap.eqLocus φ LinearMap.id := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, hb, rfl⟩
    have hb' : N.j ≤ b.val := hb
    show φ (N.ist b) = N.ist b
    simp only [φ, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.flip_apply]
    rw [Finset.sum_eq_single b]
    · rw [← H.herm, N.ist_e b b hb']; simp
    · intro a _ hab
      rw [← H.herm, N.ist_e a b hb']; simp [hab]
    · intro h; exact absurd (by simpa using hb') h
  have h2 : φ d = d := h1 hd
  rw [← h2]
  simp only [φ, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.flip_apply]
  refine Finset.sum_eq_zero fun a ha => ?_
  have ha' : N.j ≤ a.val := by simpa using ha
  have he := e_mem_II N a ha'
  rw [← H.herm, (hrad _ (isotropicMeet_le_jointSpan N he)).2 he d hd']
  simp

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem Xa_le_X (F : FlagD H r) (j : ℕ) : F.Xa j ≤ F.X :=
  Submodule.span_mono (Set.image_mono fun b _ => b.2)

theorem P0_inf_V0_le_sup_of_radical (N : NF H r)
    (hrad : ∀ v ∈ V0 N.F N.F', (∀ w ∈ V0 N.F N.F', H.B v w = 0) ↔ v ∈ II N.F N.F') :
    N.P0 ⊓ rs (𝓞 K) (V0 N.F N.F') ≤ (N.P0 ⊓ rs (𝓞 K) (N.F.Xa N.j)) ⊔ (N.P0 ⊓ rs (𝓞 K) (N.F'.Xa N.j)) ⊔
      (N.P0 ⊓ rs (𝓞 K) (II N.F N.F')) ⊔ line 1 N.F.z := by
  set Q := (N.P0 ⊓ rs (𝓞 K) (N.F.Xa N.j)) ⊔ (N.P0 ⊓ rs (𝓞 K) (N.F'.Xa N.j)) ⊔
      (N.P0 ⊓ rs (𝓞 K) (II N.F N.F')) ⊔ line 1 N.F.z with hQ
  have hQV : Q ≤ rs (𝓞 K) (V0 N.F N.F') := by
    refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
    · exact inf_le_right.trans fun x hx =>
        ((Xa_le_X N.F N.j).trans (le_sup_left.trans le_sup_left) : N.F.Xa N.j ≤ V0 N.F N.F') hx
    · exact inf_le_right.trans fun x hx =>
        ((Xa_le_X N.F' N.j).trans (le_sup_right.trans le_sup_left) : N.F'.Xa N.j ≤ V0 N.F N.F') hx
    · exact inf_le_right.trans fun x hx => isotropicMeet_le_jointSpan N hx
    · exact line_le _ _ _ (Submodule.mem_sup_right (Submodule.subset_span (by simp)))
  have hP : N.P0 ≤ Q ⊔ rs (𝓞 K) N.Ist := by
    refine sup_le (le_sup_of_le_left (sup_le (sup_le ?_ ?_) le_sup_right)) (le_sup_of_le_right ?_)
    · refine iSup_le fun a => ?_
      have h0 : line (N.aa a) (N.F.e a.castSucc) ≤ N.P0 :=
        le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
          (le_iSup (fun a : Fin r => line (N.aa a) (N.F.e a.castSucc)) a)))
      by_cases ha : a.val < N.j
      · exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
          (le_inf h0 (line_le _ _ _ (Submodule.subset_span ⟨a, ha, rfl⟩)))))
      · exact le_sup_of_le_left (le_sup_of_le_right
          (le_inf h0 (line_le _ _ _ (e_mem_II N a (not_lt.1 ha)))))
    · refine iSup₂_le fun a ha => ?_
      have h0 : line (N.aa a) (N.F'.e a.castSucc) ≤ N.P0 :=
        le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_right
          (le_iSup₂ (f := fun (a : Fin r) (_ : a.val < N.j) => line (N.aa a) (N.F'.e a.castSucc)) a ha)))
      exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_right
          (le_inf h0 (line_le _ _ _ (Submodule.subset_span ⟨a, ha, rfl⟩)))))
    · exact iSup₂_le fun a ha => line_le _ _ _ (Submodule.subset_span ⟨a, ha, rfl⟩)
  rintro p ⟨hp, hpV⟩
  obtain ⟨u, hu, d, hd, rfl⟩ := Submodule.mem_sup.1 (hP hp)
  have hdV : d ∈ V0 N.F N.F' := by
    have := (V0 N.F N.F').sub_mem hpV (hQV hu)
    rwa [add_sub_cancel_left] at this
  rw [eq_zero_of_mem N hrad d hd hdV, add_zero]
  exact hu

theorem fix_of_mem_Rs (N : NF H r) {s : V ≃ₗ[K] V} (hs : s ∈ N.Rs) : ∀ y ∈ N.Wt, s y = y :=
  fun y hy => (mem_fixingSubgroup_iff _).1 hs.2 y hy

theorem split_smul (N : NF H r) {s : V ≃ₗ[K] V} (hs : s ∈ N.Rs) {Λ : Submodule (𝓞 K) V}
    (hT : latTh N.F N.F' (s • Λ) = latTh N.F N.F' Λ) (h : N.Split Λ) : N.Split (s • Λ) := by
  unfold NF.Split at h ⊢
  rw [hT, smul_inf_eq s Λ _ (fix_of_mem_Rs N hs), h]

theorem near_mono (N : NF H r) {𝔞 𝔟 : Ideal (𝓞 K)} (h : 𝔞 ≤ 𝔟) {Λ : Submodule (𝓞 K) V}
    (hn : N.Near 𝔟 Λ) : N.Near 𝔞 Λ :=
  ⟨(Submodule.smul_mono_left h).trans hn.1, (Submodule.smul_mono_left h).trans hn.2⟩

end

theorem exists_near : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ 𝔠 : Ideal (𝓞 K), 𝔠 ≠ ⊥ → (∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) → (∀ x ∈ 𝔠, (N.T : 𝓞 K) ∣ x) → (∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠, ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)), (x : K) * y / Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) ∧ (x : K) * y / star (Dl N.F N.F' l hl) ∈ (1 : Submodule (𝓞 K) K)) → N.Split Λ → ∃ s ∈ N.Rs, N.Split (s • Λ) ∧ N.Near (𝔠 ^ (12 * r + 50)) (s • Λ) := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ hg hΛ 𝔠 h0 hst hT hD hS
  have hrad := (GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N).1.2.2.2.1
  obtain ⟨s₁, hs₁, -, h₁⟩ := GlobalTheory.T.normalForm_flag_lattices_near_under_stabiliser K V H hK r N g Λ hg hΛ 𝔠 h0 hst hT hD
  obtain ⟨a₁, a₂, a₃, a₄⟩ := h₁ _ rfl
  obtain ⟨t₁, -, th₁, -⟩ := GlobalTheory.T.commonUnipotent_stabiliser_preserves_terms_and_datum K V H hK r N g Λ hg hΛ s₁ hs₁.1
  have hS₁ := split_smul N hs₁ th₁ hS
  obtain ⟨s₂, hs₂, hfix, h₂⟩ := GlobalTheory.T.normal_form_ideal_divisibility K V H hK r N g _ hg t₁ 𝔠 h0 hst hT hD
  obtain ⟨b₁, b₂, b₃⟩ := h₂ _ rfl
  obtain ⟨t₂, -, th₂, -⟩ := GlobalTheory.T.commonUnipotent_stabiliser_preserves_terms_and_datum K V H hK r N g _ hg t₁ s₂ hs₂.1
  have hS₂ := split_smul N hs₂ th₂ hS₁
  have e₁ := smul_inf_eq s₂ (s₁ • Λ) (N.F.Xa N.j) fun y hy => hfix y (Submodule.mem_sup_left hy)
  have e₂ := smul_inf_eq s₂ (s₁ • Λ) (N.F'.Xa N.j) fun y hy => hfix y (Submodule.mem_sup_right hy)
  have key : 𝔠 ^ (2 * r + 2) • (N.P0 ⊓ rs (𝓞 K) (V0 N.F N.F')) ≤ s₂ • s₁ • Λ := by
    refine (smul_mono_right _ (P0_inf_V0_le_sup_of_radical N hrad)).trans ?_
    rw [Submodule.smul_sup, Submodule.smul_sup, Submodule.smul_sup]
    refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
    · refine le_trans ?_ (e₁.ge.trans inf_le_left)
      exact le_inf a₁ (Submodule.smul_le_right.trans inf_le_right)
    · refine le_trans ?_ (e₂.ge.trans inf_le_left)
      exact le_inf a₂ (Submodule.smul_le_right.trans inf_le_right)
    · exact (Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))).trans b₁
    · exact (Submodule.smul_mono_left (Ideal.pow_le_self (by omega))).trans b₃
  obtain ⟨s₃, hs₃, hn⟩ := GlobalTheory.T.hermFramePair_split_term_near_reference_by_skew K V H hK r N g _ hg t₂ 𝔠 h0 hst hT hD hS₂ (2 * r + 2) (by omega)
    key (by rw [e₁]; exact a₃) (by rw [e₂]; exact a₄) b₂
  have hs₃' : s₃ ∈ N.Rs := ⟨hs₃.1.1, hs₃.2⟩
  obtain ⟨-, -, th₃, -⟩ := GlobalTheory.T.commonUnipotent_stabiliser_preserves_terms_and_datum K V H hK r N g _ hg t₂ s₃ hs₃'.1
  refine ⟨s₃ * (s₂ * s₁), N.Rs.mul_mem hs₃' (N.Rs.mul_mem hs₂ hs₁), ?_, ?_⟩
  · rw [mul_smul, mul_smul]
    exact split_smul N hs₃' th₃ hS₂
  · rw [mul_smul, mul_smul]
    exact near_mono N (Ideal.pow_le_pow_right (by omega)) hn

end GlobalTheory.DegCnt.NormalPos
end
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean Filter Topology

namespace GlobalTheory.GaussMean.Limit

theorem tendsto_tsum_of_monotone {ι : Type*} (f : ℕ → ι → ENNReal) (g : ι → ENNReal)
    (hm : ∀ y, Monotone fun k => f k y) (ht : ∀ y, Tendsto (fun k => f k y) atTop (𝓝 (g y))) :
    Tendsto (fun k => ∑' y, f k y) atTop (𝓝 (∑' y, g y)) := by
  letI : MeasurableSpace ι := ⊤
  have h := lintegral_tendsto_of_tendsto_of_monotone (μ := (Measure.count : Measure ι)) (f := f) (F := g)
    (fun k => (measurable_from_top).aemeasurable) (ae_of_all _ hm) (ae_of_all _ ht)
  simpa only [lintegral_count] using h

theorem tendsto_lintegral_tsum {α ι : Type*} [MeasurableSpace α] [Countable ι] (μ : Measure α)
    (p : ι → α → Prop) (hp : ∀ y, MeasurableSet {x | p y x}) (f : ℕ → ι → α → ENNReal) (g : ι → α → ENNReal)
    (hf : ∀ k y, Measurable (f k y)) (hm : ∀ y x, Monotone fun k => f k y x)
    (ht : ∀ y x, Tendsto (fun k => f k y x) atTop (𝓝 (g y x))) :
    Tendsto (fun k => ∫⁻ x, (∑' y : {y // p y x}, f k y.1 x) ∂μ) atTop
      (𝓝 (∫⁻ x, (∑' y : {y // p y x}, g y.1 x) ∂μ)) := by
  refine lintegral_tendsto_of_tendsto_of_monotone (fun k => Measurable.aemeasurable ?_)
    (ae_of_all _ fun x a b hab => ENNReal.tsum_le_tsum fun y => hm y.1 x hab)
    (ae_of_all _ fun x => tendsto_tsum_of_monotone (fun k (y : {y // p y x}) => f k y.1 x) _
      (fun y => hm y.1 x) fun y => ht y.1 x)
  have e : (fun x => ∑' y : {y // p y x}, f k y.1 x) = fun x => ∑' y, {x | p y x}.indicator (f k y) x := by
    funext x
    exact (tsum_subtype {y | p y x} fun y => f k y x).trans (tsum_congr fun y => rfl)
  rw [e]
  exact Measurable.tsum fun y => (hf k y).indicator (hp y)

theorem measurable_coord (I : AutInst) (v : InfinitePlace I.F) (w : Fin I.n → ℂ) :
    Measurable fun x : I.GA => ((uMat (x.1 v))⁻¹ * (I.P v)⁻¹) *ᵥ w := by
  have h0 : Continuous fun g : Formalism.REAL.UJ (I.ε v) => uMat g :=
    Units.continuous_val.comp continuous_subtype_val
  have h1 : Continuous fun g : Formalism.REAL.UJ (I.ε v) => (uMat g)⁻¹ := by
    have e : (fun g : Formalism.REAL.UJ (I.ε v) => (uMat g)⁻¹) = fun g => uMat g⁻¹ := by
      funext g
      exact (Matrix.coe_units_inv g.1).symm
    rw [e]
    exact h0.comp continuous_inv
  have h2 : Continuous fun g : Formalism.REAL.UJ (I.ε v) => ((uMat g)⁻¹ * (I.P v)⁻¹) *ᵥ w :=
    (h1.matrix_mul continuous_const).matrix_mulVec continuous_const
  exact h2.measurable.comp ((measurable_pi_apply v).comp measurable_fst)

theorem siegelMean_of_cc : SiegelMeanCc → SiegelMean := by
  intro H I hn s μf _ _ fund hfund
  obtain ⟨hfin, hH⟩ := H I hn s μf fund hfund
  refine ⟨hfin, ?_⟩
  choose φ D h1 h2 h3 using fun v => GlobalTheory.T.exists_truncated_gaussians_with_densities I.n (I.ε v)
  haveI := countable_V I
  have hs : sgn ℝ s ≠ 0 := by cases s <;> simp [sgn]
  have hL := tendsto_lintegral_tsum ((I.muA μf).restrict fund)
    (fun (y : Fin I.n → I.E) (x : I.GA) => y ∈ lamX I x ∧ star y ⬝ᵥ (I.J *ᵥ y) = sgn I.E s)
    (fun y => mand (measurableSet_mem_lam I y) (MeasurableSet.const _))
    (fun k y x => ENNReal.ofReal (∏ v, φ v k (((uMat (x.1 v))⁻¹ * (I.P v)⁻¹) *ᵥ fun i => I.φ v (y i))))
    (fun y x => ENNReal.ofReal (∏ v, gauss (((uMat (x.1 v))⁻¹ * (I.P v)⁻¹) *ᵥ fun i => I.φ v (y i))))
    (fun k y => ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun v _ =>
      (h1 v k).1.continuous.measurable.comp (measurable_coord I v _)))
    (fun y x a b hab => ENNReal.ofReal_le_ofReal
      (Finset.prod_le_prod₀ (fun v _ => (h1 v a).2.2.1 _) fun v _ => (h2 v _).1 hab))
    (fun y x => ENNReal.tendsto_ofReal (tendsto_finsetProd _ fun v _ => (h2 v _).2))
  have hR : Tendsto (fun k => I.muA μf fund * ENNReal.ofReal (meanConst I.E I.n * ∏ v, D v k (sgn ℝ s))) atTop
      (𝓝 (I.muA μf fund * ENNReal.ofReal (meanConst I.E I.n * ∏ v, gaussDens (I.ε v) (sgn ℝ s)))) :=
    ENNReal.Tendsto.const_mul
      (ENNReal.tendsto_ofReal ((tendsto_finsetProd _ fun v _ => h3 v _ hs).const_mul _)) (Or.inr hfin.ne)
  exact tendsto_nhds_unique hL (hR.congr fun k => (hH (fun v => φ v k) (fun v => D v k) fun v => h1 v k).symm)

end GlobalTheory.GaussMean.Limit
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

theorem _root_.GlobalTheory.T.one_parameter_conjugation_bound : ∀ (n : ℕ) (ε : Fin n → Bool) (W : Submodule ℂ (Fin n → ℂ)) (ν : Measure (UJ ε)), IsIsoC ε W → IsHaarSub (NW ε W) ν → ∀ β : UJ ε → ENNReal, Measurable β → (∀ y, β y ≠ ⊤) → (∀ y, ∫⁻ m, β (m⁻¹ * y) ∂ν = 1) → ∀ (a : ℝ → UJ ε) (Hm : Matrix (Fin n) (Fin n) ℂ), inP ε Hm → (∀ s : ℝ, umat (a s) = NormedSpace.exp ((s : ℂ) • Hm)) → (∀ g : UJ ε, ∃ k : UJ ε, umat k ∈ Kset ε ∧ ∀ s, a s * g * (k⁻¹ * a s * k)⁻¹ * g⁻¹ ∈ NW ε W) → ∀ κ : ℝ, (∀ s, ν.map (fun m => a s * m * (a s)⁻¹) = ENNReal.ofReal (Real.exp (κ * s)) • ν) → ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (d c : ℝ) (w : H) (L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] H), IsURepOn (UJset ε) σ → IsFdeg (muG ε) σ d → 8 * n * rkR ε < c → (∀ X, inG ε X → HasDerivAt (fun s : ℝ => σ (NormedSpace.exp ((s : ℂ) • X)) w) (L X) 0) → ∃ C₀ : ℝ, ∀ v : H, (∃ C : ℝ, ∀ g : UJ ε, ‖⟪v, σ (umat g) w⟫_ℂ‖ ≤ C * Real.exp (-(c * dOp (umat g)))) → (∃ C : ℝ, ∀ g : UJ ε, ‖⟪v, σ (umat g) v⟫_ℂ‖ ≤ C * Real.exp (-(c * dOp (umat g)))) → (∀ X, inG ε X → (∃ C : ℝ, ∀ g : UJ ε, ‖⟪v, σ (umat g) (L X)⟫_ℂ‖ ≤ C * Real.exp (-(c * dOp (umat g))))) → ∀ s : ℝ, |s| ≤ 1 → ∫ g : UJ ε, (β g).toReal * ‖(∫ m, ⟪v, σ (umat (m * (a s * g))) w⟫_ℂ ∂ν) - (∫ m, ⟪v, σ (umat (m * g)) w⟫_ℂ ∂ν)‖ ^ 2 ∂(muG ε) ≤ C₀ * s ^ 2 * (∫ m, ⟪v, σ (umat m) v⟫_ℂ ∂ν).re := by
  first | exact @GlobalTheory.TorusLip.torus_lipschitz | exact GlobalTheory.TorusLip.torus_lipschitz | (intros; apply GlobalTheory.TorusLip.torus_lipschitz <;> assumption)
end
