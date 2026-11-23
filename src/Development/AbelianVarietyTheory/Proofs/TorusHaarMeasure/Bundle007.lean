module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.NormOrderStatement
public import Mathlib.RingTheory.Kaehler.Basic
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent
public import ReciprocityTheory.SemistableReduction.Bundle002
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle002

@[expose] public section

section

open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise
theorem _root_.GlobalTheory.T.gramDet_inequalities_closed_forms : (∀ (m α β γ : Type) [Fintype m] [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β] [DecidableEq γ] (M : Matrix m (α ⊕ β ⊕ γ) ℂ), (((M.submatrix id (Sum.inl : α → α ⊕ β ⊕ γ))ᴴ * (M.submatrix id (Sum.inl : α → α ⊕ β ⊕ γ))).det.re) * (((M)ᴴ * (M)).det.re) ≤ (((M.submatrix id (Sum.map id Sum.inl : α ⊕ β → α ⊕ β ⊕ γ))ᴴ * (M.submatrix id (Sum.map id Sum.inl : α ⊕ β → α ⊕ β ⊕ γ))).det.re) * (((M.submatrix id (Sum.map id Sum.inr : α ⊕ γ → α ⊕ β ⊕ γ))ᴴ * (M.submatrix id (Sum.map id Sum.inr : α ⊕ γ → α ⊕ β ⊕ γ))).det.re)) ∧ (∀ (r : ℕ) (a : Matrix (Fin r) (Fin r) ℂ), ∃ ω : ℝ, 1 ≤ ω ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : Matrix (Fin r) ι ℂ), (((a * M)ᴴ * (a * M)).det.re) ≤ ω * (((M)ᴴ * (M)).det.re)) ∧ (∀ (r : ℕ) (S : Finset (Matrix (Fin r) (Fin r) ℂ)), (∀ a ∈ S, a.IsHermitian ∧ a.det ≠ 0 ∧ a⁻¹ ∈ S) → (∀ W : Submodule ℂ (Fin r → ℂ), (∀ a ∈ S, ∀ v ∈ W, (a * a).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) → ∃ δ c ω : ℝ, 0 < δ ∧ 0 ≤ c ∧ c < 1 ∧ 1 ≤ ω ∧ ∀ (i : ℕ) (M : Matrix (Fin r) (Fin i) ℂ), 0 < (((M)ᴴ * (M)).det.re) → (∀ a ∈ S, (((a * M)ᴴ * (a * M)).det.re) ≤ ω * (((M)ᴴ * (M)).det.re) ∧ (((M)ᴴ * (M)).det.re) ≤ ω * (((a * M)ᴴ * (a * M)).det.re)) ∧ (0 < i → i < r → ∑ a ∈ S, ((((a * M)ᴴ * (a * M)).det.re) / (((M)ᴴ * (M)).det.re)) ^ (-δ) ≤ S.card * c)) ∧ (∀ (r p : ℕ), 0 < p → p < r → ∃ S : Finset (Matrix (Fin r) (Fin r) ℂ), S.Nonempty ∧ (∀ a ∈ S, a.IsHermitian ∧ a.det ≠ 0 ∧ a⁻¹ ∈ S) ∧ (∀ W : Submodule ℂ (Fin r → ℂ), (∀ a ∈ S, ∀ v ∈ W, (a * a).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) ∧ ∀ a ∈ S, (a)ᵀ * (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p then (1 : ℂ) else -1) * (a).map (starRingEnd ℂ) = (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p then (1 : ℂ) else -1) ∧ ∃ s : Matrix (Fin r) (Fin r) ℂ, (s)ᵀ * (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p then (1 : ℂ) else -1) * (s).map (starRingEnd ℂ) = (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p then (1 : ℂ) else -1) ∧ s * a = a⁻¹ * s) := by
  first | exact @GlobalTheory.gramDet_closed_forms | exact GlobalTheory.gramDet_closed_forms | (intros; apply GlobalTheory.gramDet_closed_forms <;> assumption)
end

section

namespace GlobalTheory

open NumberField ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.AlgT


open scoped IntermediateField.algebraAdjoinAdjoin in
theorem trdeg_adjoin_eq_iff_exists_linearIndependent_D {K F κ : Type} [Field K] [CharZero K]
    [Field F] [Algebra K F] {D : ℕ} (hD : Algebra.trdeg K F = D) (x : κ → F) :
    Algebra.trdeg K (IntermediateField.adjoin K (Set.range x)) = D ↔
      ∃ J : Fin D → κ, LinearIndependent F fun k => KaehlerDifferential.D K F (x (J k)) := by
  set L := IntermediateField.adjoin K (Set.range x) with hL
  have htow : Algebra.trdeg K L + Algebra.trdeg L F = D := (trdeg_add_eq K L (A := F)).trans hD
  constructor
  · intro h
    rw [h] at htow
    have h0 : Algebra.trdeg L F = 0 :=
      (Cardinal.add_nat_inj D).mp (by rw [add_comm, htow, zero_add])
    haveI : Algebra.IsAlgebraic L F := trdeg_eq_zero_iff.mp h0
    haveI : Algebra.IsAlgebraic (Algebra.adjoin K (Set.range x)) F :=
      Algebra.IsAlgebraic.trans (Algebra.adjoin K (Set.range x)) L F
    obtain ⟨t, ht, hb⟩ := exists_isTranscendenceBasis_subset (R := K) (Set.range x)
    have hc : Cardinal.mk t = Cardinal.mk (Fin D) := by
      rw [hb.cardinalMk_eq_trdeg, hD, Cardinal.mk_fin]
    obtain ⟨e⟩ := Cardinal.eq.mp hc
    choose J hJ using fun k : Fin D => ht (e.symm k).2
    haveI := hb.isAlgebraic_field
    haveI : CharZero (IntermediateField.adjoin K (Set.range ((↑) : t → F))) :=
      algebraRat.charZero _
    obtain ⟨b, hbD⟩ := exists_basis_kaehler_of_algebraicIndependent hb.1
    refine ⟨J, ?_⟩
    have := b.linearIndependent.comp e.symm e.symm.injective
    convert this using 1
    funext k
    rw [hJ k]
    exact (hbD (e.symm k)).symm
  · rintro ⟨J, hJ⟩
    have hind : AlgebraicIndependent K fun k => x (J k) :=
      ReciprocityTheory.ChartRestriction.G.AR.differentialIndependence K F D _ hJ
    let y : Fin D → L := fun k => ⟨x (J k), IntermediateField.subset_adjoin K _ ⟨J k, rfl⟩⟩
    have hy : AlgebraicIndependent K y := AlgebraicIndependent.of_comp L.val hind
    refine le_antisymm (htow ▸ le_self_add) ?_
    simpa using hy.cardinalMk_le_trdeg

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]

theorem trdegD_iff_exists_linearIndependent_D :
    ∀ (d : Data K ι Ω WT A) (c : ι), Algebra.trdeg K (Ω c) = d.D → d.w (d.jc c) c ≠ 0 →
    (TrdegD d c ↔ ∃ J : Fin d.D → Fin d.N,
      LinearIndependent (Ω c) fun k => KaehlerDifferential.D K (Ω c) (d.x c (J k))) := by
  intro d c hD hw
  have hone : ratio (Ω := Ω c) (d.w (d.jc c) c) (d.w (d.jc c) c) = 1 := by
    have hex : ∃ a : Ω c, d.w (d.jc c) c = a • d.w (d.jc c) c := ⟨1, (one_smul _ _).symm⟩
    have h := hex.choose_spec
    rw [ratio, dite_eq_left hex]
    exact smul_left_injective (Ω c) hw (h.symm.trans (one_smul _ _).symm)
  have heq : IntermediateField.adjoin K (Set.range fun j =>
      ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c)) =
      IntermediateField.adjoin K (Set.range (d.x c)) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨j, rfl⟩
      rcases Fin.eq_self_or_eq_succAbove (d.jc c) j with rfl | ⟨k, rfl⟩
      · simp only [hone]
        exact one_mem _
      · exact IntermediateField.subset_adjoin K _ ⟨k, rfl⟩
    · apply IntermediateField.adjoin.mono
      rintro _ ⟨k, rfl⟩
      exact ⟨(d.jc c).succAbove k, rfl⟩
  rw [TrdegD, heq]
  exact trdeg_adjoin_eq_iff_exists_linearIndependent_D hD (d.x c)

end GlobalTheory
end

section

open Matrix MvPolynomial ReciprocityTheory.MultiplicativeHeights

namespace GlobalTheory

theorem exists_lowerUnitriangular_mul_upperTriangular :
    ∀ (p : ℕ) (x : Matrix (Fin p) (Fin p) ℂ), (∀ i, leadMinor x i ≠ 0) →
      ∃ n b : Matrix (Fin p) (Fin p) ℂ, x = n * b ∧ (∀ i, n i i = 1) ∧
        (∀ i j, i < j → n i j = 0) ∧ (∀ i j, j < i → b i j = 0) := by
  intro p x hx
  have hM : ∀ k : Fin (p + 1), ReciprocityTheory.ChartRestriction.G.FD.lminor x k ≠ 0 := by
    intro k
    refine Fin.cases ?_ (fun i => ?_) k
    · unfold ReciprocityTheory.ChartRestriction.G.FD.lminor
      have : IsEmpty (Fin ((0 : Fin (p + 1)) : ℕ)) := inferInstanceAs (IsEmpty (Fin 0))
      rw [Matrix.det_isEmpty]
      exact one_ne_zero
    · exact hx i
  set L := ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf.Lm x with hL
  have hu : IsUnit L.det := by
    rw [hL, ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf.Lm_det]; exact isUnit_one
  have hup : ∀ i k : Fin p, i < k → L i k = 0 := ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf.Lm_up x
  have hd : ∀ i : Fin p, L i i = 1 := ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf.Lm_diag x
  have hbt : L.BlockTriangular OrderDual.toDual := fun i k h => hup i k h
  let : Invertible L := L.invertibleOfIsUnitDet hu
  have hinv : L⁻¹.BlockTriangular OrderDual.toDual := blockTriangular_inv_of_blockTriangular hbt
  have hup' : ∀ i k : Fin p, i < k → L⁻¹ i k = 0 := fun i k h => hinv h
  refine ⟨L⁻¹, L * x, ?_, fun i => ?_, hup', fun i j h => ?_⟩
  · rw [← Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.one_mul]
  · have h := ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf.row_expand L L⁻¹ i i (hup i) (hd i)
    rw [mul_nonsing_inv _ hu, Matrix.one_apply_eq, Finset.sum_eq_zero, zero_add] at h
    · exact h.symm
    · intro k _
      rw [hup' _ i (by rw [Fin.lt_def]; exact k.isLt), mul_zero]
  · exact ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf.Lm_mul_up x hM i j h

end GlobalTheory
end
