module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerDiagonalBlockAsGLMemIntegralGeneralLinear
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle081
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle073
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle033
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeierstrassPOddMulSubTwoTorsionProduct
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.NumberTheory.Padics.Complex
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle037
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038
import Mathlib.RingTheory.PowerSeries.Basic

@[expose] public section

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section

namespace GlobalTheory.ParHeckeTarget

open GlobalTheory.ParHeckeSource

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A D D' : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D']

theorem inSupp_mul_left {y : Matrix (A ⊕ D') (A ⊕ D) k} (hy : InSupp y) {u : GL (A ⊕ D') k}
    (hu : u ∈ parahoric k A D') : InSupp (u.val * y) ∧
      valuation k ((u.val * y).toBlocks₁₁.det - u.val.toBlocks₁₁.det * y.toBlocks₁₁.det) < 1 := by
  have hJ := GlobalTheory.DatumEigen.int_of_mem hu
  have hl := (mem_parahoric.1 hu).2
  obtain ⟨hyi, hyd, hyl⟩ := hy
  have hprod : ∀ i l, (u.val * y) i l ∈ 𝒪[k] := fun i l => by
    rw [Matrix.mul_apply]; exact sum_mem fun m _ => mul_mem (hJ i m) (hyi m l)
  have hcong : valuation k ((u.val * y).toBlocks₁₁.det - u.val.toBlocks₁₁.det * y.toBlocks₁₁.det) < 1 := by
    rw [← det_mul]
    refine GlobalTheory.DatumEigen.val_det_sub_lt (fun i l => hprod _ _) (fun i l => ?_) (fun i l => ?_)
    · rw [Matrix.mul_apply]; exact sum_mem fun m _ => mul_mem (hJ _ _) (hyi _ _)
    · simp only [toBlocks₁₁, of_apply, Matrix.mul_apply, Fintype.sum_sum_type, add_sub_cancel_left]
      exact Valuation.map_sum_lt _ one_ne_zero fun m _ => GlobalTheory.DatumEigen.val_mul_lt (hJ _ _) (hyl _ _)
  have hd1 : valuation k (u.val.toBlocks₁₁.det * y.toBlocks₁₁.det) = 1 := by
    rw [map_mul, hyd, mul_one, (GlobalTheory.DatumEigen.val_det_blocks hu).1]
  refine ⟨⟨hprod, ?_, ?_⟩, hcong⟩
  · rw [← hd1]
    refine Valuation.map_eq_of_sub_lt _ ?_
    rw [hd1]; exact hcong
  · intro e a
    rw [Matrix.mul_apply, Fintype.sum_sum_type]
    refine Valuation.map_add_lt _ (Valuation.map_sum_lt _ one_ne_zero fun m _ => ?_)
      (Valuation.map_sum_lt _ one_ne_zero fun m _ => ?_)
    · rw [mul_comm]; exact GlobalTheory.DatumEigen.val_mul_lt (hyi _ _) (hl _ _)
    · exact GlobalTheory.DatumEigen.val_mul_lt (hJ _ _) (hyl _ _)

omit [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] in
theorem torusElt_indic_int {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (s : Finset D') :
    IsIntM (torusElt k D' ϖ (indic s)).val := by
  have hlt : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  rw [val_torusElt]
  intro i j
  rw [diagonal_apply]; split_ifs
  · show valuation k _ ≤ 1
    rw [map_zpow₀]
    exact zpow_le_one₀ (zero_lt_iff.2 (by simp)) hlt.le (by unfold indic; split_ifs <;> norm_num)
  · exact zero_mem _

theorem inSupp_diag_mul {y : Matrix (A ⊕ D') (A ⊕ D) k} (hy : InSupp y) {t : Matrix D' D' k} (ht : IsIntM t) :
    InSupp ((fromBlocks (1 : Matrix A A k) 0 0 t : Matrix (A ⊕ D') (A ⊕ D') k) * y) ∧
      ((fromBlocks (1 : Matrix A A k) 0 0 t : Matrix (A ⊕ D') (A ⊕ D') k) * y).toBlocks₁₁ = y.toBlocks₁₁ := by
  obtain ⟨h1, h2, h3⟩ := hy
  obtain ⟨a, b, c, e⟩ := isIntM_toBlocks (show IsIntM y from h1)
  rw [fromBlocks_diag_mul]
  refine ⟨⟨isIntM_fromBlocks_iff.2 ⟨a, b, isIntM_mul ht c, isIntM_mul ht e⟩, by simpa using h2, fun i j => ?_⟩,
    toBlocks_fromBlocks₁₁ _ _ _ _⟩
  rw [fromBlocks_apply₂₁]
  exact val_lt_mul ht (fun a b => h3 a b) i j


open Classical in
theorem coset_term : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D D' : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (ξ : kˣ →* ℂˣ), IsTame ξ → ∀ (s : Finset D') (j : GL (A ⊕ D') k), j ∈ parahoric k A D' → ∀ d : kˣ, (d : k) = j.1.toBlocks₂₂.det → ∀ x : Matrix (A ⊕ D') (A ⊕ D) k, (InSupp (((j * mtor ϖ (indic s))⁻¹).1 * x) → ((ξ d * (ξ (GeneralLinearGroup.det j))⁻¹ : ℂˣ) : ℂ) * datum ξ (((j * mtor ϖ (indic s))⁻¹).1 * x) = datum ξ x) ∧ (¬ InSupp (((j * mtor ϖ (indic s))⁻¹).1 * x) → datum ξ (((j * mtor ϖ (indic s))⁻¹).1 * x) = 0) := by
  intro k _ _ _ _ A D D' _ _ _ _ _ _ ϖ hϖ ξ hξ s j hj d hd x
  set y := ((j * mtor ϖ (indic s))⁻¹).1 * x with hydef
  refine ⟨fun hW => ?_, fun hW => by simp only [datum, dif_neg hW]⟩
  set T := torusElt k D' ϖ (indic s) with hT
  have hg0 : (mtor (A := A) ϖ (indic s)).val = fromBlocks (1 : Matrix A A k) 0 0 T.val := by
    rw [mtor_eq_dg, val_dg]
  have hx : x = j.val * ((mtor (A := A) ϖ (indic s)).val * y) := by
    rw [hydef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.one_mul]
  obtain ⟨hg, hg11⟩ := inSupp_diag_mul hW (torusElt_indic_int hϖ s)
  rw [← hg0] at hg hg11
  obtain ⟨hs, hc⟩ := inSupp_mul_left hg hj
  rw [← hx, hg11] at hc
  rw [← hx] at hs
  obtain ⟨h11, h22⟩ := GlobalTheory.DatumEigen.val_det_blocks hj
  have n11 : j.val.toBlocks₁₁.det ≠ 0 := fun h0 => by rw [h0, map_zero] at h11; exact zero_ne_one h11
  set u₁ : kˣ := Units.mk0 _ n11 with hu₁
  have hdv : valuation k (d : k) = 1 := by rw [hd]; exact h22
  have t1 : ξ (GeneralLinearGroup.det j) = ξ (u₁ * d) := by
    refine GlobalTheory.DatumEigen.tame_eq hξ (by rw [Units.val_mul, map_mul, hdv, mul_one]; exact h11) ?_
    rw [Units.val_mul, hd, GeneralLinearGroup.val_det_apply]
    exact GlobalTheory.DatumEigen.det_cong hj
  have t2 : ξ (Units.mk0 _ hs.det_ne) = ξ (Units.mk0 _ hW.det_ne * u₁) := by
    refine GlobalTheory.DatumEigen.tame_eq hξ (by rw [Units.val_mul, map_mul, Units.val_mk0, hW.2.1, one_mul]; exact h11) ?_
    show valuation k (x.toBlocks₁₁.det - y.toBlocks₁₁.det * j.val.toBlocks₁₁.det) < 1
    rw [mul_comm (y.toBlocks₁₁.det)]
    exact hc
  simp only [datum, dif_pos hs, dif_pos hW]
  rw [t1, t2, ← Units.val_mul]
  congr 1
  simp only [map_mul]
  group

end GlobalTheory.ParHeckeTarget
end
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

theorem _root_.GlobalTheory.T.zonalInt_mul_KO_invariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) [MeasurableSpace (GL (Fin N) k)] [BorelSpace (GL (Fin N) k)] (μK : Measure (GL (Fin N) k)) [μK.IsHaarMeasure], μK (KO k (Fin N)) = 1 → ∀ ψ : GL (Fin N) k → ℂ, (∀ g, ∀ x ∈ KO k (Fin N), ψ (g * x) = ψ g) → ∀ κ ∈ KO k (Fin N), ∀ m, zonalInt μK ψ (κ * m) = zonalInt μK ψ m ∧ zonalInt μK ψ (m * κ) = zonalInt μK ψ m := by
  first | exact @GlobalTheory.ZonalBi.zonalInt_biInvariant | exact GlobalTheory.ZonalBi.zonalInt_biInvariant | (intros; apply GlobalTheory.ZonalBi.zonalInt_biInvariant <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

theorem _root_.GlobalTheory.T.sum_zonalInt_mul_eq_of_eigen : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) [MeasurableSpace (GL (Fin N) k)] [BorelSpace (GL (Fin N) k)] (μK : Measure (GL (Fin N) k)) [μK.IsHaarMeasure], μK (KO k (Fin N)) = 1 → ∀ ψ : GL (Fin N) k → ℂ, (∀ g, ∀ x ∈ KO k (Fin N), ψ (g * x) = ψ g) → ∀ (R : Finset (GL (Fin N) k)) (c : ℂ), (∀ m, ∑ g ∈ R, ψ (m * g) = c * ψ m) → ∀ m, ∑ g ∈ R, zonalInt μK ψ (m * g) = c * zonalInt μK ψ m := by
  first | exact @GlobalTheory.ZonalEig.zonalInt_eig | exact GlobalTheory.ZonalEig.zonalInt_eig | (intros; apply GlobalTheory.ZonalEig.zonalInt_eig <;> assumption)
end

section

open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM

theorem _root_.GlobalTheory.T.omegaK_sq_sub_self_add_eq_zero : ∀ d : ℕ, d % 4 = 3 → omegaK d ^ 2 - omegaK d + (((d + 1) / 4 : ℕ) : ℂ) = 0 := by
  first | exact @GlobalTheory.omegaK_quadratic | exact GlobalTheory.omegaK_quadratic | (intros; apply GlobalTheory.omegaK_quadratic <;> assumption)
end

section

open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM

theorem _root_.GlobalTheory.T.weierstrassP_odd_mul_sub_twoTorsion_product : ∀ (L : PeriodPair) (n : ℕ) (S : Finset ℂ) (t : ℂ), Odd n → Formalism.L2.Th1.F.IsKerReps L (n : ℂ) S → t ∉ L.lattice → 2 * t ∈ L.lattice → ∀ z, (n : ℂ) * z ∉ L.lattice → (n : ℂ) ^ 2 * (L.weierstrassP (n * z) - L.weierstrassP t) * ∏ P ∈ S, (L.weierstrassP z - L.weierstrassP P) = (L.weierstrassP z - L.weierstrassP t) * ∏ P ∈ S, (L.weierstrassP z - L.weierstrassP (t + P)) := by
  first | exact @GlobalTheory.OddHalfProduct.wp_odd_mul_sub_half_prod | exact GlobalTheory.OddHalfProduct.wp_odd_mul_sub_half_prod | (intros; apply GlobalTheory.OddHalfProduct.wp_odd_mul_sub_half_prod <;> assumption)
end

section

open PowerSeries GlobalTheory.Honda

theorem _root_.GlobalTheory.T.lazard_binomial_norm_ultrametric : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ), l.Prime → ‖(l : K)‖ < 1 → ∀ (a : K) (n : ℕ), 2 ≤ n → (∀ k, 0 < k → k < n → ‖a * (n.choose k : K)‖ ≤ ‖(l : K)‖) → ‖a‖ ≤ ‖(l : K)‖ ∨ (‖a‖ ≤ 1 ∧ ∃ i : ℕ, 0 < i ∧ n = l ^ i) := by
  first | exact @GlobalTheory.Honda.Lazard.lazard_binomial | exact GlobalTheory.Honda.Lazard.lazard_binomial | (intros; apply GlobalTheory.Honda.Lazard.lazard_binomial <;> assumption)
end

section

open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM

theorem _root_.GlobalTheory.T.weierstrassP_integral_of_mul_integral_good_reduction : ∀ (L : PeriodPair) (l : ℕ) [Fact l.Prime], 5 ≤ l → ∀ (ι : ℂ ≃+* ℂ_[l]), ‖ι L.g₂‖ ≤ 1 → ‖ι L.g₃‖ ≤ 1 → ‖ι L.g₂ ^ 3 - 27 * ι L.g₃ ^ 2‖ = 1 → ∀ (z : ℂ) (N : ℕ), (N : ℂ) * z ∉ L.lattice → ‖ι (L.weierstrassP (N * z))‖ ≤ 1 → ‖ι (L.weierstrassP z)‖ ≤ 1 := by
  first | exact @GlobalTheory.Honda.integral_of_mul_integral | exact GlobalTheory.Honda.integral_of_mul_integral | (intros; apply GlobalTheory.Honda.integral_of_mul_integral <;> assumption)
end
