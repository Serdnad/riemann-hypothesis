module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GenericBlockMatrixIsBlockDiag
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle098
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle080
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartQContinuousAtAndLocalSolution
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartQHermitianAndRealPairing
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle085
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle006
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncResolutionRegularLocalRing
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle088
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle102
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle103
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle101
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle090
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle089
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.FubiniLevi

@[expose] public section

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.TransvOther

theorem mul_transv_apply {N : ℕ} (h : Matrix (Fin N) (Fin N) ℂ) (t : ℂ) (ca cb r c : Fin N) :
    (h * (1 + Matrix.single cb ca t)) r c = h r c + if c = ca then t * h r cb else 0 := by
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]
  congr 1
  by_cases hc : c = ca
  · subst hc
    simp [Matrix.mul_apply, Matrix.single_apply, mul_comm]
  · simp [Matrix.mul_apply, Matrix.single_apply, hc, Ne.symm hc]

private lemma det_submatrix_mul_transvection_eq {N k : ℕ} (h : Matrix (Fin N) (Fin N) ℂ) (t : ℂ) (ca cb : Fin N)
    (hne : ca ≠ cb) (f g : Fin k → Fin N) (hg : Function.Injective g)
    (hJ : ca ∈ Set.range g ↔ cb ∈ Set.range g) :
    ((h * (1 + Matrix.single cb ca t)).submatrix f g).det = (h.submatrix f g).det := by
  by_cases hca : ca ∈ Set.range g
  · obtain ⟨qa, hqa⟩ := hca
    obtain ⟨qb, hqb⟩ := hJ.mp ⟨qa, hqa⟩
    have hq : qb ≠ qa := by
      rintro rfl
      exact hne (hqa.symm.trans hqb)
    have hiff : ∀ q, g q = ca ↔ q = qa := fun q => by
      rw [← hqa]
      exact hg.eq_iff
    have hM : (h * (1 + Matrix.single cb ca t)).submatrix f g
        = h.submatrix f g * (1 + Matrix.single qb qa t) := by
      ext p q
      simp only [Matrix.submatrix_apply, mul_transv_apply, hqb, hiff]
    have h1 : (1 + Matrix.single qb qa t : Matrix (Fin k) (Fin k) ℂ) = Matrix.transvection qb qa t :=
      rfl
    rw [hM, Matrix.det_mul, h1, Matrix.det_transvection_of_ne qb qa hq t, mul_one]
  · congr 1
    ext p q
    have hq : g q ≠ ca := fun hh => hca ⟨q, hh⟩
    simp only [Matrix.submatrix_apply, mul_transv_apply, hq, if_false, add_zero]

theorem minorIJ_transv {N : ℕ} (h : Matrix (Fin N) (Fin N) ℂ) (t : ℂ) (ca cb : Fin N) (hne : ca ≠ cb)
    (I J : Finset (Fin N)) (hJ : ca ∈ J ↔ cb ∈ J) :
    minorIJ (h * (1 + Matrix.single cb ca t)) I J = minorIJ h I J := by
  unfold minorIJ
  split_ifs with e
  · apply det_submatrix_mul_transvection_eq h t ca cb hne
    · exact (J.orderEmbOfFin _).injective
    · rw [Finset.range_orderEmbOfFin, Finset.mem_coe, Finset.mem_coe]
      exact hJ
  · rfl

theorem minorIJ_other_step : ∀ (N j : ℕ) (a b ca cb : Fin N), j ≤ N → (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (h : Matrix (Fin N) (Fin N) ℂ) (t : ℂ) (i : Fin N), i ≠ a → ∀ I, minorIJ (h * (1 + Matrix.single cb ca t)) I (stepCols N j i) = minorIJ h I (stepCols N j i) := by
  intro N j a b ca cb hjN hb hab hca hcb h t i hi I
  apply minorIJ_transv h t ca cb
  · intro heq
    have := congrArg Fin.val heq
    omega
  · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
    unfold lastCol at hca
    have hi' : (i : ℕ) ≠ a := fun h' => hi (Fin.ext h')
    have := a.isLt
    have := b.isLt
    have := i.isLt
    have := ca.isLt
    have := cb.isLt
    split_ifs at hca ⊢ <;> omega

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.TransvOther
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.Transv

theorem lastCol_mem {N j : ℕ} {a ca : Fin N} (hj : j ≤ N) (hca : (ca : ℕ) = lastCol N j a) :
    ca ∈ stepCols N j a ∧ ∀ r ∈ stepCols N j a, r ≤ ca := by
  unfold lastCol at hca
  refine ⟨?_, ?_⟩
  · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs at hca ⊢ <;> omega
  · intro r hr
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at hr
    rw [Fin.le_iff_val_le_val]
    split_ifs at hca hr <;> omega

theorem transv_mul_transv {N : ℕ} {ca cb : Fin N} (hne : ca ≠ cb) (s : ℂ) :
    (1 + Matrix.single cb ca s) * (1 + Matrix.single cb ca (-s)) = (1 : Matrix (Fin N) (Fin N) ℂ) := by
  rw [add_mul, one_mul, mul_add, mul_one, Matrix.single_mul_single_of_ne s cb ca cb hne (-s), add_zero,
    add_assoc, ← Matrix.single_add, neg_add_cancel, Matrix.single_zero, add_zero]

theorem main : ∀ (N j : ℕ) (a ca cb : Fin N) (L U : Matrix (Fin N) (Fin N) ℂ) (t' : ℂ), j ≤ N → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ((ca : ℕ) < N - j ↔ (cb : ℕ) < N - j) → IsBlockDiag j L → IsLowerUni L → IsBlockDiag j U → U.BlockTriangular id → (∀ c, U c c ≠ 0) → minorIJ (L * U * (1 + Matrix.single cb ca t')) (stepCols N j a) (stepCols N j a) ≠ 0 → ∃ (t : ℂ) (V : Matrix (Fin N) (Fin N) ℂ), IsBlockDiag j V ∧ V.BlockTriangular id ∧ (∀ c ∈ stepCols N j a, V c c ≠ 0) ∧ U * (1 + Matrix.single cb ca t') = (1 + Matrix.single cb ca t) * V := by
  intro N j a ca cb L U t' hj hca hcb hblk hL hLu hU hUt hUd hmin
  have hne : ca ≠ cb := by
    intro h
    have h1 := congrArg Fin.val h
    omega
  obtain ⟨hcaS, hmax⟩ := lastCol_mem hj hca
  have hLM : L * U * (1 + Matrix.single cb ca t') = L * (U * (1 + Matrix.single cb ca t')) :=
    Matrix.mul_assoc _ _ _
  set M := U * (1 + Matrix.single cb ca t') with hMdef
  have hMe : ∀ x y, M x y = U x y + if y = ca then U x cb * t' else 0 := by
    intro x y
    rw [hMdef, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]
    split_ifs with hy
    · rw [hy, Matrix.mul_single_apply_same]
    · rw [Matrix.mul_single_apply_of_ne t' cb ca x y hy U]
  have hUz : ∀ x y : Fin N, y < x → U x y = 0 := fun x y h => hUt (show id y < id x from h)
  have hMut : ∀ x y : Fin N, y < x → x ≠ cb → M x y = 0 := by
    intro x y hxy hx
    rw [hMe, hUz x y hxy]
    split_ifs with hy
    · rw [hy] at hxy
      have h1 : cb < x := by
        rw [Fin.lt_iff_val_lt_val] at hxy ⊢
        have h2 : (x : ℕ) ≠ cb := fun h => hx (Fin.ext h)
        omega
      rw [hUz x cb h1]
      simp
    · simp
  have hMca : M ca ca ≠ 0 := by
    intro h0
    apply hmin
    rw [hLM]
    unfold minorIJ
    rw [dite_eq_left rfl]
    set f := (stepCols N j a).orderEmbOfFin (rfl : (stepCols N j a).card = (stepCols N j a).card) with hf
    have hfmem : ∀ r, f r ∈ stepCols N j a := fun r => Finset.orderEmbOfFin_mem _ _ r
    have hSmap : Finset.univ.map f.toEmbedding = stepCols N j a := Finset.map_orderEmbOfFin_univ _ _
    have hrange : Set.range f = ↑(stepCols N j a) := Finset.range_orderEmbOfFin _ _
    have hprod : (L * M).submatrix f f = L.submatrix f f * M.submatrix f f := by
      ext p q
      simp only [Matrix.submatrix_apply, Matrix.mul_apply]
      have hfpS := hfmem p
      have hz : ∀ i ∈ (Finset.univ : Finset (Fin N)), i ∉ stepCols N j a → L (f p) i * M i (f q) = 0 := by
        intro i _ hi
        by_cases hic : (ca : ℕ) < i
        · have hfp := hmax (f p) hfpS
          have hlt : f p < i := by
            rw [Fin.le_iff_val_le_val] at hfp
            rw [Fin.lt_iff_val_lt_val]
            omega
          rw [hLu.2 (f p) i hlt, zero_mul]
        · have hLz : L (f p) i = 0 := by
            apply hL
            intro hiff
            simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at hi hfpS
            unfold lastCol at hca
            split_ifs at hi hfpS hca
            · have h3 := hiff.mpr (by omega)
              omega
            · omega
          rw [hLz, zero_mul]
      have hm := Finset.sum_map Finset.univ f.toEmbedding (fun x => L (f p) x * M x (f q))
      rw [hSmap] at hm
      rw [← Finset.sum_subset (Finset.subset_univ (stepCols N j a)) hz]
      exact hm
    have hUT : (M.submatrix f f).IsUpperTriangular := by
      intro p q hpq
      rw [Matrix.submatrix_apply]
      have hfpcb : f p ≠ cb := by
        intro hfp
        have h4 := hmax (f p) (hfmem p)
        rw [hfp, Fin.le_iff_val_le_val] at h4
        omega
      exact hMut (f p) (f q) (f.strictMono hpq) hfpcb
    have hdetM : (M.submatrix f f).det = 0 := by
      rw [Matrix.det_of_upperTriangular hUT]
      obtain ⟨p0, hp0⟩ : ∃ p0, f p0 = ca := by
        have h1 : ca ∈ Set.range f := by
          rw [hrange]
          exact hcaS
        exact h1
      exact Finset.prod_eq_zero (Finset.mem_univ p0) (by rw [Matrix.submatrix_apply, hp0]; exact h0)
    rw [hprod, Matrix.det_mul, hdetM, mul_zero]
  have hMb : ∀ x y : Fin N, ¬((x : ℕ) < N - j ↔ (y : ℕ) < N - j) → M x y = 0 := by
    intro x y hxy
    rw [hMe, hU x y hxy]
    split_ifs with hy
    · rw [hy] at hxy
      rw [hU x cb (fun h => hxy (h.trans hblk.symm))]
      simp
    · simp
  set t := M cb ca / M ca ca with ht
  have hVe : ∀ x y, ((1 + Matrix.single cb ca (-t)) * M) x y = M x y + if x = cb then -t * M ca y else 0 := by
    intro x y
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.add_apply]
    split_ifs with hx
    · rw [hx, Matrix.single_mul_apply_same]
    · rw [Matrix.single_mul_apply_of_ne (-t) cb ca x y hx M]
  refine ⟨t, (1 + Matrix.single cb ca (-t)) * M, ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    rw [hVe, hMb x y hxy]
    split_ifs with hx
    · rw [hx] at hxy
      rw [hMb ca y (fun h => hxy (hblk.symm.trans h))]
      simp
    · simp
  · intro x y hxy
    change y < x at hxy
    rw [hVe]
    by_cases hx : x = cb
    · rw [if_pos hx, hx]
      rw [hx] at hxy
      by_cases hy : y = ca
      · rw [hy, ht, neg_mul, div_mul_cancel₀ _ hMca, add_neg_cancel]
      · have hylt : y < ca := by
          rw [Fin.lt_iff_val_lt_val] at hxy ⊢
          have h2 : (y : ℕ) ≠ ca := fun h => hy (Fin.ext h)
          omega
        rw [hMe cb y, if_neg hy, hUz cb y hxy, hMe ca y, if_neg hy, hUz ca y hylt]
        simp
    · rw [if_neg hx, add_zero]
      exact hMut x y hxy hx
  · intro c hc
    rw [hVe]
    have hcle := hmax c hc
    have hccb : c ≠ cb := by
      intro h
      rw [h, Fin.le_iff_val_le_val] at hcle
      omega
    rw [if_neg hccb, add_zero]
    by_cases hcc : c = ca
    · rw [hcc]
      exact hMca
    · rw [hMe, if_neg hcc, add_zero]
      exact hUd c
  · rw [← Matrix.mul_assoc, transv_mul_transv hne t, Matrix.one_mul]

end GlobalTheory.CompanionTheory.Ar.PB.WMan.Transv
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.ChartCount

theorem sum_range_eq_choose (m : ℕ) : ∑ i ∈ Finset.range m, i = m.choose 2 := by
  rw [Finset.sum_range_id, Nat.choose_two_right]

theorem card_row (N j : ℕ) (hj : j ≤ N) (a : Fin N) :
    Fintype.card {b : Fin N // b < a ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)} =
      if (a : ℕ) < N - j then (a : ℕ) else (a : ℕ) - (N - j) := by
  rw [Fintype.card_subtype]
  have key : (Finset.univ.filter fun b : Fin N => b < a ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)).map
      Fin.valEmbedding = Finset.Ico (if (a : ℕ) < N - j then 0 else N - j) (a : ℕ) := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_Ico]
    constructor
    · rintro ⟨b, ⟨hba, hiff⟩, rfl⟩
      have hba' : (b : ℕ) < a := hba
      split_ifs with h
      · exact ⟨Nat.zero_le _, hba'⟩
      · exact ⟨Nat.le_of_not_lt (fun hb => h (hiff.mpr hb)), hba'⟩
    · rintro ⟨h1, h2⟩
      refine ⟨⟨x, lt_trans h2 a.isLt⟩, ⟨h2, ?_⟩, rfl⟩
      show (a : ℕ) < N - j ↔ x < N - j
      split_ifs at h1 with h
      · exact ⟨fun _ => lt_trans h2 h, fun _ => h⟩
      · exact ⟨fun h' => absurd h' h, fun h' => absurd h1 (Nat.not_le.mpr h')⟩
  rw [← Finset.card_map Fin.valEmbedding, key, Nat.card_Ico]
  split_ifs <;> simp

theorem card_pairs (N j : ℕ) (hj : j ≤ N) :
    Fintype.card {p : Fin N × Fin N // p.2 < p.1 ∧ ((p.1 : ℕ) < N - j ↔ (p.2 : ℕ) < N - j)} =
      j.choose 2 + (N - j).choose 2 := by
  rw [Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype
      (fun (a b : Fin N) => b < a ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j))), Fintype.card_sigma]
  have h1 : ∀ a : Fin N, Fintype.card {b : Fin N // b < a ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)} =
      if (a : ℕ) < N - j then (a : ℕ) else (a : ℕ) - (N - j) := card_row N j hj
  simp only [h1]
  have hs : ∑ a : Fin N, (if (a : ℕ) < N - j then (a : ℕ) else (a : ℕ) - (N - j)) =
      ∑ i ∈ Finset.range N, (if i < N - j then i else i - (N - j)) :=
    Fin.sum_univ_eq_sum_range (fun i => if i < N - j then i else i - (N - j)) N
  rw [hs]
  obtain ⟨M, rfl⟩ : ∃ M, N = M + j := ⟨N - j, by omega⟩
  have hM : M + j - j = M := by omega
  rw [hM, Finset.sum_range_add]
  have e1 : ∑ x ∈ Finset.range M, (if x < M then x else x - M) = ∑ x ∈ Finset.range M, x :=
    Finset.sum_congr rfl (fun x hx => if_pos (Finset.mem_range.mp hx))
  have e2 : ∑ x ∈ Finset.range j, (if M + x < M then M + x else M + x - M) =
      ∑ x ∈ Finset.range j, x :=
    Finset.sum_congr rfl (fun x _ => by rw [if_neg (by omega)]; omega)
  rw [e1, e2, sum_range_eq_choose, sum_range_eq_choose, add_comm]

theorem card_lowIdx (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (hj : j ≤ N) :
    Fintype.card (LowIdx Ψ N j) = Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) := by
  rw [← card_pairs N j hj, ← Fintype.card_prod]
  exact Fintype.card_congr
    { toFun := fun q => (q.1.1, ⟨q.1.2, q.2⟩)
      invFun := fun x => ⟨(x.1, x.2.1), x.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem nonempty_paramEquiv : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j n d : ℕ), j ≤ N →
    d + 1 = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) →
    Nonempty (Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin (d + 2)) := by
  intro Ψ _ _ N j n d hj hd
  apply Fintype.card_eq.mp
  rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_fin, card_lowIdx Ψ N j hj,
    Fintype.card_unit, Fintype.card_fin]
  generalize Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) = t at hd ⊢
  omega

end GlobalTheory.CompanionTheory.Ar.PB.WMan.ChartCount
end

section

noncomputable section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.MinorSmooth

theorem contDiffOn_finsetProd {e : ℕ} {Un : Set (Fin e → ℂ)} {ι : Type} (s : Finset ι)
    (f : ι → (Fin e → ℂ) → ℂ)
    (h : ∀ i ∈ s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f i) Un) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => ∏ i ∈ s, f i w) Un := by
  induction s using Finset.induction_on with
  | empty => simpa using (contDiffOn_const : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : Fin e → ℂ => (1 : ℂ)) Un)
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem contDiffOn_det {e : ℕ} {Un : Set (Fin e → ℂ)} {σ : Type} [Fintype σ] [DecidableEq σ]
    (m : (Fin e → ℂ) → Matrix σ σ ℂ)
    (h : ∀ a b, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => m w a b) Un) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => (m w).det) Un := by
  have hdet : (fun w => (m w).det) =
      fun w => ∑ τ : Equiv.Perm σ, ((Equiv.Perm.sign τ : ℤ) : ℂ) * ∏ i, m w (τ i) i := by
    funext w
    exact Matrix.det_apply' _
  rw [hdet]
  exact ContDiffOn.sum fun τ _ => contDiffOn_const.mul
    (contDiffOn_finsetProd Finset.univ (fun i w => m w (τ i) i) fun i _ => h _ _)

theorem contDiffOn_minorIJ (N e : ℕ) (Un : Set (Fin e → ℂ))
    (A : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ) (I J : Finset (Fin N))
    (h : ∀ r s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => A w r s) Un) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => minorIJ (A w) I J) Un := by
  by_cases hc : I.card = J.card
  · have hm : (fun w => minorIJ (A w) I J) =
        fun w => ((A w).submatrix (I.orderEmbOfFin hc) (J.orderEmbOfFin rfl)).det := by
      funext w
      rw [minorIJ, dite_eq_left hc]
    rw [hm]
    exact contDiffOn_det _ fun a b => h _ _
  · have hm : (fun w => minorIJ (A w) I J) = fun _ => (0 : ℂ) := by
      funext w
      rw [minorIJ, dite_eq_right hc]
    rw [hm]
    exact contDiffOn_const

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.MinorSmooth
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

theorem _root_.GlobalTheory.T.block_minor_sum_frame_identity : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (S : Type) [CommRing S] (ρ : M.Ω →+* S) (F : FrameData ι Ψ N M.Ω M.blk), M.IsFrame F → ∀ (p : Ψ × Fin N) (k : K), M.blk p = some k → ∀ (m : ι k) (h : Matrix (Fin N) (Fin N) S), IsBlockDiag j h → detFac j p.2 ((F.T p.1).map ρ) * ∑ I, ρ (M.coef ⟨k, m⟩ I) * minorIJ ((F.T p.1).map ρ * h) I (stepCols N j p.2) = ρ (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b p k') * ∑ I, ρ (F.u ⟨k, m⟩ I) * minorIJ h I (stepCols N j p.2) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovGraph.FrameExt.frame_identity_map | exact GlobalTheory.CompanionTheory.Ar.PB.CovGraph.FrameExt.frame_identity_map | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovGraph.FrameExt.frame_identity_map <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

theorem _root_.GlobalTheory.T.minor_of_regular_matrix_value : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (x : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) (N : ℕ) (A : Matrix (Fin N) (Fin N) Ω), z ∈ mcPts (mCoordIdeal x) → (∀ a b, RegAt x (mCoordIdeal z) (A a b)) → ∀ I J : Finset (Fin N), RegAt x (mCoordIdeal z) (minorIJ A I J) ∧ valAt x (minorIJ A I J) z = minorIJ (Matrix.of fun a b => valAt x (A a b) z) I J := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovGraph.regAt_minorIJ_valAt | exact GlobalTheory.CompanionTheory.Ar.PB.CovGraph.regAt_minorIJ_valAt | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovGraph.regAt_minorIJ_valAt <;> assumption)
end

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

theorem _root_.GlobalTheory.T.chartQ_continuousAt_and_local_solution : ∀ (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ) (bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ) (A T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (c ρ : ℝ) (Pr : Matrix (Fin g) (Fin g) ℝ), IsChart L bas A T0 B c ρ → IsKerProj (∑ j, B j) Pr → ContinuousAt (chartQ Pr A T0) 0 ∧ ∃ ρ' : ℝ, 0 < ρ' ∧ ∀ w ∈ logCover L.a_le, ‖expCover a w‖ < ρ' → ∀ y : Fin g → ℂ, ∃ p : Fin g → ℂ, p - y ∈ Submodule.span ℂ {u | ∃ x : chartW bas B, (∀ x' : chartW bas B, L.E x x' = 0) ∧ u = L.P w x} ∧ (∀ x : chartW bas B, (∀ x' : chartW bas B, L.E x x' = 0) → p ⬝ᵥ L.H (expCover a w) *ᵥ star (L.P w x) = 0) ∧ ∀ y' : Fin g → ℂ, y' ⬝ᵥ L.H (expCover a w) *ᵥ star p = y' ⬝ᵥ chartQ Pr A T0 (expCover a w) *ᵥ star y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.QuotientForm.quotient_form_rep | exact GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.QuotientForm.quotient_form_rep | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.QuotientForm.quotient_form_rep <;> assumption)
end

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

theorem _root_.GlobalTheory.T.chartQ_hermitian_and_real_pairing : ∀ (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ) (bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ) (A T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (c ρ : ℝ) (Pr : Matrix (Fin g) (Fin g) ℝ), IsChart L bas A T0 B c ρ → IsKerProj (∑ j, B j) Pr → (chartQ Pr A T0 0).IsHermitian ∧ (∀ x x' : chartW bas B, (chartPer bas A T0 B x ⬝ᵥ chartQ Pr A T0 0 *ᵥ star (chartPer bas A T0 B x')).im = L.E x x') ∧ (∀ x : chartW bas B, (∀ x' : chartW bas B, L.E x x' = 0) → chartQ Pr A T0 0 *ᵥ star (chartPer bas A T0 B x) = 0) ∧ ∀ v : Fin g → ℂ, 0 ≤ (v ⬝ᵥ chartQ Pr A T0 0 *ᵥ star v).re ∧ ((v ⬝ᵥ chartQ Pr A T0 0 *ᵥ star v).re = 0 → v ∈ Submodule.span ℂ {p | ∃ x : chartW bas B, (∀ x' : chartW bas B, L.E x x' = 0) ∧ p = chartPer bas A T0 B x}) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.LimitForm.limit_form | exact GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.LimitForm.limit_form | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.LimitForm.limit_form <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Cmp

theorem _root_.GlobalTheory.T.snc_resolution_regular_local_ring : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (J : Ideal (MRing ι)), IsArithVar (mCoordIdeal y) (e + 1) → IsSncModel y e J → ∀ p : (k : K) → ι k, ∀ x ∈ SncRes.src (pC (mCoordIdeal y)) p, IsRegularLocalRing (ReciprocityTheory.AnForm.R.locRing (SncRes.ideal (pC (mCoordIdeal y)) p) (SncRes.coord (pC (mCoordIdeal y)) p x)) ∧ ringKrullDim (ReciprocityTheory.AnForm.R.locRing (SncRes.ideal (pC (mCoordIdeal y)) p) (SncRes.coord (pC (mCoordIdeal y)) p x)) = e := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg.isRegularLocalRing_chart | exact GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg.isRegularLocalRing_chart | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg.isRegularLocalRing_chart <;> assumption)
end
