module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle387
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle425
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitBallLeadingGramMinorLowerBoundFirst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitBallLeadingGramMinorLowerBoundLast
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle424
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle400
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle401
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle002

@[expose] public section

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix

theorem _root_.GlobalTheory.T.ofReal_gramDeterminantBound_le_prod_cutoff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (z : V (nd X)), z ∈ Om X → ENNReal.ofReal (bnd X z) ≤ ∏ τ, hB X.p0 (zOf X z τ) := by
  first | exact @GlobalTheory.IntBall.Cutoff.ofReal_bnd_le | exact GlobalTheory.IntBall.Cutoff.ofReal_bnd_le | (intros; apply GlobalTheory.IntBall.Cutoff.ofReal_bnd_le <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix

theorem _root_.GlobalTheory.T.unitBall_leadingGramMinor_lower_bound_first : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), X.p0 = 1 → ∀ (x0 : Base X) (z : V (nd X)), z ∈ Om X → ∀ (τ : X.Ψ) (k : Fin (r - 1)), zDet X z τ * colGram (blkW X.p0 (zOf X z τ)) k.castSucc ≤ ‖dmin X.Gm (point X x0 z) τ ⟨(k : ℕ) + 1, by omega⟩‖ := by
  first | exact @GlobalTheory.IntBallMinorOne.zDet_mul_colGram_le_norm_dmin | exact GlobalTheory.IntBallMinorOne.zDet_mul_colGram_le_norm_dmin | (intros; apply GlobalTheory.IntBallMinorOne.zDet_mul_colGram_le_norm_dmin <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix

theorem _root_.GlobalTheory.T.unitBall_leadingGramMinor_lower_bound_last : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), X.p0 + 1 = r → ∀ (x0 : Base X) (z : V (nd X)), z ∈ Om X → ∀ (τ : X.Ψ) (k : Fin (r - 1)), zDet X z τ * colGram (blkW X.p0 (zOf X z τ)) k.succ ≤ ‖dmin X.Gm (point X x0 z) τ ⟨(k : ℕ) + 1, by omega⟩‖ := by
  first | exact @GlobalTheory.IntBall.MinorLast.zDet_mul_colGram_le_dmin | exact GlobalTheory.IntBall.MinorLast.zDet_mul_colGram_le_dmin | (intros; apply GlobalTheory.IntBall.MinorLast.zDet_mul_colGram_le_dmin <;> assumption)
end

section

open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix

theorem _root_.GlobalTheory.T.lintegral_cutoffGramBoundMixedBlock_two_lt_top : ∫⁻ w : Low 2 → ℂ, hB 1 w < ⊤ := by
  first | exact @GlobalTheory.IntBall.lintegral_hB_one_two_lt_top | exact GlobalTheory.IntBall.lintegral_hB_one_two_lt_top | (intros; apply GlobalTheory.IntBall.lintegral_hB_one_two_lt_top <;> assumption)
end

section

open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix

theorem _root_.GlobalTheory.T.measurable_cutoffGramBoundMixedBlock : ∀ (r p0 : ℕ), Measurable (hB (r := r) p0) := by
  first | exact @GlobalTheory.IntBall.measurable_hB | exact GlobalTheory.IntBall.measurable_hB | (intros; apply GlobalTheory.IntBall.measurable_hB <;> assumption)
end

section

open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix

theorem _root_.GlobalTheory.T.columnGramDeterminant_diagonalBlockUnitLower_pos : ∀ (r p0 : ℕ) (w : Low r → ℂ) (k : Fin (r - 1 + 1)), 0 < colGram (blkW p0 w) k := by
  first | exact @GlobalTheory.IntBall.ColGramPos.colGram_blkW_pos | exact GlobalTheory.IntBall.ColGramPos.colGram_blkW_pos | (intros; apply GlobalTheory.IntBall.ColGramPos.colGram_blkW_pos <;> assumption)
end

section

open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix

theorem _root_.GlobalTheory.T.columnGramDeterminant_unitLowerBlock_last_eq_one : ∀ (r p0 : ℕ) (w : Low r → ℂ), colGram (blkW p0 w) (Fin.last (r - 1)) = 1 := by
  first | exact @GlobalTheory.IntBall.colGramLast | exact GlobalTheory.IntBall.colGramLast | (intros; apply GlobalTheory.IntBall.colGramLast <;> assumption)
end

section

open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix

theorem _root_.GlobalTheory.T.columnGramDeterminant_unitLower_three : ∀ M : Matrix (Fin 3) (Fin 3) ℂ, (∀ i, M i i = 1) → (∀ i j : Fin 3, i < j → M i j = 0) → colGram M 1 = 1 + ‖M 1 0‖ ^ 2 + ‖M 2 0‖ ^ 2 ∧ colGram M 2 = 1 + ‖M 2 1‖ ^ 2 + ‖M 1 0 * M 2 1 - M 2 0‖ ^ 2 := by
  first | exact @GlobalTheory.IntBall.colGram_three_unitLower | exact GlobalTheory.IntBall.colGram_three_unitLower | (intros; apply GlobalTheory.IntBall.colGram_three_unitLower <;> assumption)
end

section

open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix

theorem _root_.GlobalTheory.T.lintegral_cutoffGramBoundMixedBlock_rankThree_lt_top : ∀ p0 : ℕ, (p0 = 1 ∨ p0 = 2) → ∫⁻ w : Low 3 → ℂ, hB p0 w < ⊤ := by
  first | exact @GlobalTheory.IntBall.Fin3.lintegral_hB_lt_top | exact GlobalTheory.IntBall.Fin3.lintegral_hB_lt_top | (intros; apply GlobalTheory.IntBall.Fin3.lintegral_hB_lt_top <;> assumption)
end

section

open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal

theorem _root_.GlobalTheory.T.diagonalPhaseFrame_small_angles : ∀ (E : Type) [Field E] (Ψ : Finset (E →+* ℂ)) (r : ℕ) (δ : ℝ), 0 < δ → ∃ η : ℝ, 0 < η ∧ ∀ θ : Ψ → Fin (r - 1) → ℝ, (∀ τ (a : Fin r), ‖phaseFrame θ τ a a - 1‖ < η) → ∃ θ' : Ψ → Fin (r - 1) → ℝ, ‖θ'‖ < δ ∧ phaseFrame θ' = phaseFrame θ := by
  first | exact @GlobalTheory.RiemConst.phaseFrame_small_angles | exact GlobalTheory.RiemConst.phaseFrame_small_angles | (intros; apply GlobalTheory.RiemConst.phaseFrame_small_angles <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.PbfNatl

theorem pull_htCast' (q : ℕ) {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E' n i) :
    pull _ f _ _ (Ht.cast hn hi x) = Ht.cast hn hi (pull _ f _ _ x : Ht q E n i) := by
  subst hn; subst hi; rfl

theorem pull_cpow' (q : ℕ) [NeZero q] (hA : DivisorNaturality) {E E' : Spc} (f : E ⟶ E') (hE' : Inv q E') (x : Ht q E' 2 1) (k : ℕ) :
    pull _ f _ _ (cpow q x k) = cpow q (pull _ f _ _ x : Ht q E 2 1) k := by
  induction k with
  | zero => rw [cpow_zero, cpow_zero, pull_htCast', (hA q).2.1 f hE']
  | succ k ih => rw [cpow_succ, cpow_succ, pull_htCast', (hA q).1, ih]

theorem pull_pbfMap_of_factor : DivisorNaturality → ∀ (q : ℕ) [NeZero q] {E B P : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N))
    (L : B ⟶ ofCat (glCat 1)) (θ : P ⟶ pullback V (PGL.pr N)) (f : P ⟶ E) (g : P ⟶ B), Inv q B →
    Inv q (pullback V (PGL.pr N)) → θ ≫ pullback.fst _ _ = f → θ ≫ pullback.snd _ _ ≫ PGL.line N = g ≫ L →
    ∀ (n i : ℤ) (a : ∀ j : Fin N, Ht q E (n - 2 * (j : ℕ)) (i - (j : ℕ))),
    pull _ θ _ _ (pbfMap q V n i a) = ∑ j : Fin N, ((cup q (pull _ f _ _ (a j)) (pull _ g _ _ (cpow q (c1 q L) j))).cast (by ring) (by ring) : Ht q P n i) := by
  intro hA q _ E B P N V L θ f g hB hP hf hg n i a
  unfold pbfMap

  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pull_htCast', (hA q).1, ← pull_comp, hf, pull_cpow' q hA _ hP, (hA q).2.2.1 _ _ hP,
    pull_cpow' q hA _ hB, (hA q).2.2.1 _ _ hB, hg]

end GlobalTheory.EtC.PbfNatl

end
end

section

open MeasureTheory Matrix ValuativeRel

namespace GlobalTheory.HeisUnit

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


open scoped Classical in
open Classical in
theorem intInd_apply {n d : ℕ} (M : Matrix (Fin n) (Fin d) k) :
    intInd k n d M = if ∀ i j, M i j ∈ 𝒪[k] then 1 else 0 := by
  classical
  simp only [intInd, Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]

theorem sub_inv_mul_out_mem_iff {ϖ : kˣ} (hϖ : SplitFlip.IsUnif ϖ) (y : k)
    (t : SplitFlip.Res (k := k) 1) :
    y - (ϖ : k)⁻¹ * ((Quotient.out t : 𝒪[k]) : k) ∈ 𝒪[k] ↔
      ∃ h : (ϖ : k) * y ∈ 𝒪[k], t = Ideal.Quotient.mk _ ⟨(ϖ : k) * y, h⟩ := by
  have ht : t = Ideal.Quotient.mk _ (Quotient.out t) := (Quotient.out_eq t).symm
  set a := Quotient.out t
  have hϖ0 : (ϖ : k) ≠ 0 := ϖ.ne_zero
  constructor
  · intro hc
    have hy : (ϖ : k) * y = ϖ * (y - (ϖ : k)⁻¹ * a) + a := by field_simp; ring
    have hmem : (ϖ : k) * y ∈ 𝒪[k] := hy ▸ add_mem (mul_mem hϖ.mem hc) a.2
    refine ⟨hmem, ?_⟩
    rw [ht, Ideal.Quotient.eq, pow_one, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton']
    refine ⟨-⟨_, hc⟩, Subtype.ext ?_⟩
    push_cast
    field_simp
    ring
  · rintro ⟨h, e⟩
    have e' := ht.symm.trans e
    rw [Ideal.Quotient.eq, pow_one, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at e'
    obtain ⟨c, hc⟩ := e'
    have hc' : (c : k) * ϖ = a - ϖ * y := by simpa using congrArg Subtype.val hc
    have hinv : (ϖ : k)⁻¹ * ϖ = 1 := inv_mul_cancel₀ hϖ0
    have : y - (ϖ : k)⁻¹ * a = -(c : k) := by
      linear_combination (ϖ : k)⁻¹ * hc' - (y + c) * hinv
    rw [this]
    exact neg_mem c.2

theorem intInd_diagAt_eq_sum : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ} (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (i0 : Fin n) (Y : Matrix (Fin n) (Fin d) k),
    GlobalTheory.HeisUnit.intInd k n d ((GlobalTheory.HeisUnit.diagAt ϖ i0).valᵀ * Y) =
      ∑ T : Fin d → GlobalTheory.SplitFlip.Res (k := k) 1, GlobalTheory.HeisUnit.intInd k n d (Y + GlobalTheory.HeisUnit.cosetRep ϖ i0 T) := by
  intro k _ _ _ _ n d ϖ hϖ i0 Y
  classical
  have hL : ∀ i j, ((diagAt ϖ i0).valᵀ * Y) i j = (if i = i0 then (ϖ : k) else 1) * Y i j := by
    intro i j
    rw [diagAt_val, diagonal_transpose, diagonal_mul]
  have hR : ∀ (T : Fin d → SplitFlip.Res (k := k) 1) i j, (Y + cosetRep ϖ i0 T) i j =
      if i = i0 then Y i j - (ϖ : k)⁻¹ * ((Quotient.out (T j) : 𝒪[k]) : k) else Y i j := by
    intro T i j
    simp only [cosetRep, Matrix.add_apply, Matrix.of_apply]
    split_ifs <;> ring
  by_cases hQR : (∀ i j, i ≠ i0 → Y i j ∈ 𝒪[k]) ∧ ∀ j, (ϖ : k) * Y i0 j ∈ 𝒪[k]
  · obtain ⟨hQ, hRR⟩ := hQR
    let T0 : Fin d → SplitFlip.Res (k := k) 1 := fun j => Ideal.Quotient.mk _ ⟨_, hRR j⟩
    have hl : intInd k n d ((diagAt ϖ i0).valᵀ * Y) = 1 := by
      rw [intInd_apply, if_pos]
      intro i j
      rw [hL]
      split_ifs with h
      · subst h; exact hRR j
      · rw [one_mul]; exact hQ i j h
    have hs : ∀ T, intInd k n d (Y + cosetRep ϖ i0 T) = if T = T0 then 1 else 0 := by
      intro T
      rw [intInd_apply]
      by_cases hT : T = T0
      · rw [if_pos hT, if_pos]
        intro i j
        rw [hR]
        split_ifs with h
        · subst h; exact (sub_inv_mul_out_mem_iff hϖ _ _).2 ⟨hRR j, by rw [hT]⟩
        · exact hQ i j h
      · rw [if_neg hT, if_neg]
        intro hm
        apply hT
        funext j
        have := hm i0 j
        rw [hR, if_pos rfl] at this
        obtain ⟨_, e⟩ := (sub_inv_mul_out_mem_iff hϖ _ _).1 this
        exact e
    rw [hl, Finset.sum_congr rfl (fun T _ => hs T), Finset.sum_ite_eq']
    simp
  · have hl : intInd k n d ((diagAt ϖ i0).valᵀ * Y) = 0 := by
      rw [intInd_apply, if_neg]
      intro hm
      refine hQR ⟨fun i j h => ?_, fun j => ?_⟩
      · have := hm i j; rwa [hL, if_neg h, one_mul] at this
      · have := hm i0 j; rwa [hL, if_pos rfl] at this
    rw [hl]
    symm
    apply Finset.sum_eq_zero
    intro T _
    rw [intInd_apply, if_neg]
    intro hm
    refine hQR ⟨fun i j h => ?_, fun j => ?_⟩
    · have := hm i j; rwa [hR, if_neg h] at this
    · have := hm i0 j
      rw [hR, if_pos rfl] at this
      exact ((sub_inv_mul_out_mem_iff hϖ _ _).1 this).1

end GlobalTheory.HeisUnit
end
