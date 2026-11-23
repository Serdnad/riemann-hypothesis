module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
public import Development.AbelianVarietyTheory.Counterexamples.DegenerateExamples.StatementOfTied
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle250
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle261
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle581
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle440
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExtendByZeroTrivialDecomposition
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualOrthAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle350
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StandardAuxiliaryFramesFitGridEnds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1347
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubledWeilSplitPlaceVacuumEigenfunction
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle026
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle342
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle335
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle589
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.TypeStar
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HermitianSymplecticScalars
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.LatticeTranslateSum

theorem sum_pow_le {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (N : ℕ) :
    (∑ i, f i) ^ N ≤ (Fintype.card ι : ℝ) ^ N * ∑ i, f i ^ N := by
  set k : ℝ := (Fintype.card ι : ℝ) with hk_def
  have hk1 : (1 : ℝ) ≤ k := Nat.one_le_cast.mpr Fintype.card_pos
  have hk : (0 : ℝ) < k := by linarith
  have hw : ∑ _i : ι, (1 / k) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hk_def]
    field_simp
  have h := Real.pow_arith_mean_le_arith_mean_pow Finset.univ (fun _ => 1 / k) f
    (fun _ _ => by positivity) hw (fun i _ => hf i) N
  rw [← Finset.mul_sum, ← Finset.mul_sum, mul_pow] at h
  have hs : 0 ≤ ∑ i, f i ^ N := Finset.sum_nonneg fun i _ => pow_nonneg (hf i) _
  calc (∑ i, f i) ^ N = k ^ N * ((1 / k) ^ N * (∑ i, f i) ^ N) := by
        rw [← mul_assoc, ← mul_pow, mul_one_div_cancel hk.ne', one_pow, one_mul]
    _ ≤ k ^ N * (1 / k * ∑ i, f i ^ N) := mul_le_mul_of_nonneg_left h (by positivity)
    _ ≤ k ^ N * ∑ i, f i ^ N := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have : 1 / k ≤ 1 := by rw [div_le_one hk]; exact hk1
        nlinarith

theorem decay (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (θ : InfFam D) (hθ : IsInfFam θ)
    (S T : HSp D) (c : WO S T → ℂ)
    (hder : ∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (k : ℕ), ∃ C : ℝ, ∀ w : WO S T,
      ‖deriv (fun t : ℝ => ψ (symplO S T (lineAt θ τ z t) w)) 0‖ ^ k * ‖c w‖ ≤ C) (N : ℕ) :
    ∃ C : ℝ, ∀ w : WO S T, (1 + GlobalTheory.Unf.realSize θ w) ^ N * ‖c w‖ ≤ C := by
  classical
  choose n zs κ hκ using fun τ => GlobalTheory.T.exists_bound_matrix_by_symplecticFormHomAtRealPlace D S T τ
  choose Cf hCf using hder
  obtain ⟨τ₀⟩ := (GlobalTheory.DataRowsCounterexample.places_nonempty D).1
  let dv : (Σ τ : D.what₂.Tau, Fin (n τ)) → WO S T → ℝ := fun p w =>
    ‖deriv (fun t : ℝ => ψ (symplO S T (lineAt θ p.1 (zs p.1 p.2) t) w)) 0‖
  let r : (Σ τ : D.what₂.Tau, Fin (n τ)) → ℝ := fun p => |κ p.1| / (2 * Real.pi)
  let f : WO S T → Option (Σ τ : D.what₂.Tau, Fin (n τ)) → ℝ := fun w o =>
    match o with
    | none => 1
    | some p => r p * dv p w
  have hf0 : ∀ w o, 0 ≤ f w o := by
    intro w o
    cases o with
    | none => simp [f]
    | some p => exact mul_nonneg (div_nonneg (abs_nonneg _) (by positivity)) (norm_nonneg _)
  have hdv : ∀ p w, r p * dv p w = |κ p.1| * |GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt S T p.1 (zs p.1 p.2) (compAt θ p.1 w)| := by
    intro p w
    simp only [r, dv]
    rw [GlobalTheory.T.norm_deriv_character_symplecticPairing_realLine D ψ hψ θ hθ S T p.1 (zs p.1 p.2) w]
    field_simp
  have hsize : ∀ w, 1 + GlobalTheory.Unf.realSize θ w ≤ ∑ o, f w o := by
    intro w
    rw [Fintype.sum_option]
    simp only [f]
    refine add_le_add le_rfl ?_
    rw [Fintype.sum_sigma]
    unfold GlobalTheory.Unf.realSize
    refine Finset.sum_le_sum fun τ _ => ?_
    simp only [hdv]
    rw [← Finset.mul_sum]
    have hs : 0 ≤ ∑ l, |GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt S T τ (zs τ l) (compAt θ τ w)| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    exact (hκ τ (compAt θ τ w)).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hs)
  refine ⟨(Fintype.card (Option (Σ τ : D.what₂.Tau, Fin (n τ))) : ℝ) ^ N *
    (Cf τ₀ 0 0 + ∑ p, r p ^ N * Cf p.1 (zs p.1 p.2) N), fun w => ?_⟩
  have hrs : 0 ≤ GlobalTheory.Unf.realSize θ w := by
    unfold GlobalTheory.Unf.realSize
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have h1 : (1 + GlobalTheory.Unf.realSize θ w) ^ N ≤ (∑ o, f w o) ^ N := pow_le_pow_left₀ (by positivity) (hsize w) N
  have h2 := sum_pow_le (f w) (hf0 w) N
  calc (1 + GlobalTheory.Unf.realSize θ w) ^ N * ‖c w‖ ≤ (∑ o, f w o) ^ N * ‖c w‖ :=
        mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ ≤ (Fintype.card (Option (Σ τ : D.what₂.Tau, Fin (n τ))) : ℝ) ^ N * (∑ o, f w o ^ N) * ‖c w‖ :=
        mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    _ ≤ _ := by
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [Fintype.sum_option, add_mul, Finset.sum_mul]
        refine add_le_add ?_ (Finset.sum_le_sum fun p _ => ?_)
        · simp only [f, one_pow, one_mul]
          simpa using hCf τ₀ 0 0 w
        · simp only [f]
          rw [mul_pow, mul_assoc]
          exact mul_le_mul_of_nonneg_left (hCf p.1 (zs p.1 p.2) N w)
            (pow_nonneg (div_nonneg (abs_nonneg _) (by positivity)) _)

end GlobalTheory.LatticeTranslateSum


open GlobalTheory.LatticeTranslateSum in
theorem GlobalTheory.LatticeTranslateSum.sum_translates_bounded : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T : HSp D) (c : WO S T → ℂ), (∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧ ∀ w : WO S T, c w ≠ 0 → ∀ u ∈ U, u.map (infPart D) = 0 → ψ (symplO S T w u) = 1) → (∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (k : ℕ), ∃ C : ℝ, ∀ w : WO S T, ‖deriv (fun t : ℝ => ψ (symplO S T (lineAt θ τ z t) w)) 0‖ ^ k * ‖c w‖ ≤ C) → ∃ C : ℝ, ∀ w : WO S T, Summable (fun γ : ratL T S => ‖c ((γ : WO S T) + w)‖) ∧ ∑' γ : ratL T S, ‖c ((γ : WO S T) + w)‖ ≤ C := by
  intro D ψ hψ θ hθ S T c ⟨U, hU, hUc⟩ hder
  obtain ⟨Q, hQ, hQc⟩ := GlobalTheory.T.exists_compact_finiteComponents_of_annihilator_openSubgroup D ψ hψ S T U hU
  have hbox : ∀ x, c x ≠ 0 → GlobalTheory.Unf.InBox Q x := fun x hx => hQc x (hUc x hx)
  obtain ⟨-, -, -, -, -, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  obtain ⟨N, hN⟩ := GlobalTheory.Unf.MajLoc.summable_bound D θ hθ T.rank S.rank
  obtain ⟨b, hb, hbb⟩ := hN Q K hQ hK
  obtain ⟨C, hC⟩ := decay D ψ hψ θ hθ S T c hder N
  have hmaj : ∀ x : WO S T, ‖c x‖ ≤ max C 0 * GlobalTheory.Unf.maj θ Q N x := by
    intro x
    by_cases hx : c x = 0
    · rw [hx, norm_zero]
      refine mul_nonneg (le_max_right _ _) ?_
      unfold GlobalTheory.Unf.maj
      split_ifs
      · have hrs : 0 ≤ GlobalTheory.Unf.realSize θ x := by
          unfold GlobalTheory.Unf.realSize
          exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
        positivity
      · exact le_rfl
    · have hrs : 0 ≤ GlobalTheory.Unf.realSize θ x := by
        unfold GlobalTheory.Unf.realSize
        exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
      have hp : 0 < (1 + GlobalTheory.Unf.realSize θ x) ^ N := by positivity
      unfold GlobalTheory.Unf.maj
      rw [if_pos (hbox x hx), ← div_eq_mul_inv, le_div_iff₀ hp, mul_comm]
      exact (hC x).trans (le_max_left _ _)
  have hinj : Function.Injective (incA D) := GlobalTheory.MixModel.incA_injective
  let e0 : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ratL T S := fun ξ => ⟨rat ξ, ⟨ξ, rfl⟩⟩
  have he0 : Function.Bijective e0 := by
    refine ⟨fun ξ ξ' h => ?_, fun γ => ?_⟩
    · have h' : rat ξ = rat ξ' := congrArg Subtype.val h
      exact Matrix.map_injective hinj h'
    · obtain ⟨x, ξ, hξ⟩ := γ
      exact ⟨ξ, Subtype.ext hξ⟩
  refine ⟨max C 0 * ∑' ξ, b ξ, fun w => ?_⟩
  obtain ⟨g0, hg0, hg0K⟩ := hcov w
  let e : Matrix (Fin T.rank) (Fin S.rank) D.host.E ≃ ratL T S :=
    (Equiv.ofBijective e0 he0).trans (Equiv.addRight ⟨g0, hg0⟩)
  have hterm : ∀ ξ, ‖c (((e ξ : ratL T S) : WO S T) + w)‖ ≤ max C 0 * b ξ := by
    intro ξ
    have he : ((e ξ : ratL T S) : WO S T) + w = (g0 + w) + rat ξ := by
      show rat ξ + g0 + w = (g0 + w) + rat ξ
      abel
    rw [he]
    exact (hmaj _).trans (mul_le_mul_of_nonneg_left (hbb _ hg0K ξ) (le_max_right _ _))
  have hs : Summable (fun ξ => ‖c (((e ξ : ratL T S) : WO S T) + w)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm (hb.mul_left _)
  refine ⟨e.summable_iff.mp hs, ?_⟩
  rw [← e.tsum_eq, ← tsum_mul_left]
  exact hs.tsum_le_tsum hterm (hb.mul_left _)
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin

section Gen

variable {D : D7} {A B : HSp D} {c σ : ℕ}

theorem isAuxiliaryVectorWittDec_evenFourierJacobiRescale (d : HermitianOrthogonalExtensionData A B c (-1)) (h : c = 2 * σ) :
    IsAuxiliaryVectorWittDec d (GlobalTheory.AscInh.rescale (GlobalTheory.RowUnf.jacDec d h) (fun p => (-D.host.xi0) ^ (p.1 + 1))
      fun _ => GlobalTheory.AscInh.xiPow_ne D _) := by
  refine ⟨by omega, ?_, fun p => (star ((-D.host.xi0) ^ (p.1 + 1)))⁻¹, ?_⟩
  · ext i p
    simp only [GlobalTheory.AscInh.rescale, GlobalTheory.RowUnf.jacDec, HermitianOrthogonalExtensionData.iso, colsOf, Matrix.mul_diagonal, Matrix.submatrix_apply, id]
    exact mul_comm _ _
  · ext i p
    simp only [GlobalTheory.AscInh.rescale, GlobalTheory.RowUnf.jacDec, colsOf, Matrix.mul_diagonal, Matrix.submatrix_apply, id]
    exact mul_comm _ _

theorem isAuxiliaryVectorWittDec_oddBesselRescale (d : HermitianOrthogonalExtensionData A B c (-1)) (h : c = 2 * σ + 1) :
    IsAuxiliaryVectorWittDec d (GlobalTheory.AscInh.rescale (GlobalTheory.RowUnf.besDec d h) (fun p => (-D.host.xi0) ^ (p.1 + 1))
      fun _ => GlobalTheory.AscInh.xiPow_ne D _) := by
  refine ⟨by omega, ?_, fun p => (star ((-D.host.xi0) ^ (p.1 + 1)))⁻¹, ?_⟩
  · ext i p
    simp only [GlobalTheory.AscInh.rescale, GlobalTheory.RowUnf.besDec, HermitianOrthogonalExtensionData.iso, colsOf, Matrix.mul_diagonal, Matrix.submatrix_apply, id]
    exact mul_comm _ _
  · ext i p
    simp only [GlobalTheory.AscInh.rescale, GlobalTheory.RowUnf.besDec, colsOf, Matrix.mul_diagonal, Matrix.submatrix_apply, id]
    exact mul_comm _ _

theorem coreMat_iA (d : HermitianOrthogonalExtensionData A B c (-1)) (h : c = 2 * σ + 1) :
    GlobalTheory.RowUnf.coreMat d h * (GlobalTheory.OrthSumExists.orthDecHsum D A (GlobalTheory.SeeSaw.Model.nLine D)).iA = frameMat B A d.ι := by
  change (Matrix.fromCols (frameMat B A d.ι) (GlobalTheory.RowUnf.midCol d h)).submatrix id (finSumFinEquiv (m := A.rank) (n := 1)).symm *
    (Matrix.fromRows (1 : Matrix (Fin A.rank) (Fin A.rank) D.host.E) (0 : Matrix (Fin 1) (Fin A.rank) D.host.E)).submatrix
      finSumFinEquiv.symm id = _
  rw [Matrix.submatrix_mul_equiv, Matrix.fromCols_mul_fromRows, Matrix.mul_one, Matrix.mul_zero, add_zero, Matrix.submatrix_id_id]

theorem coreMat_iB (d : HermitianOrthogonalExtensionData A B c (-1)) (h : c = 2 * σ + 1) :
    (GlobalTheory.RowUnf.coreMat d h * (GlobalTheory.OrthSumExists.orthDecHsum D A (GlobalTheory.SeeSaw.Model.nLine D)).iB) *ᵥ
      (fun _ => (-D.host.xi0) ^ 0) = fun i => d.a i ⟨σ, by omega⟩ := by
  have e : GlobalTheory.RowUnf.coreMat d h * (GlobalTheory.OrthSumExists.orthDecHsum D A (GlobalTheory.SeeSaw.Model.nLine D)).iB = GlobalTheory.RowUnf.midCol d h := by
    change (Matrix.fromCols (frameMat B A d.ι) (GlobalTheory.RowUnf.midCol d h)).submatrix id (finSumFinEquiv (m := A.rank) (n := 1)).symm *
      (Matrix.fromRows (0 : Matrix (Fin A.rank) (Fin 1) D.host.E) (1 : Matrix (Fin 1) (Fin 1) D.host.E)).submatrix
        finSumFinEquiv.symm id = _
    rw [Matrix.submatrix_mul_equiv, Matrix.fromCols_mul_fromRows, Matrix.mul_one, Matrix.mul_zero, zero_add,
      Matrix.submatrix_id_id]
  rw [e]
  funext i
  change ∑ j : Fin 1, GlobalTheory.RowUnf.midCol d h i j * (-D.host.xi0) ^ 0 = _
  rw [Fin.sum_univ_one, pow_zero, mul_one]
  rfl

end Gen

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)

theorem auxiliaryFrames_standard : Std (GlobalTheory.AscInh.auxiliaryFrames G) := by
  exact {
    zA := rfl
    zB := by
      funext i
      simp only [GlobalTheory.AscInh.auxiliaryFrames, GlobalTheory.AscInh.lineDec, Matrix.mulVec, dotProduct, pow_zero, mul_one]
      exact Fin.sum_univ_one _
    ζ ρ := by
      funext i
      show (-D.host.xi0) ^ ρ = (-D.host.xi0) ^ ρ * (-D.host.xi0) ^ 0
      rw [pow_zero, mul_one]
    hB ρ h := isAuxiliaryVectorWittDec_oddBesselRescale _ _
    aB ρ h := coreMat_iA _ _
    zB' ρ h := coreMat_iB _ _
    hJ ρ h := isAuxiliaryVectorWittDec_evenFourierJacobiRescale _ _
    aJ ρ h := rfl
  }

theorem exists_std_frames : All fun {_} _ _ _ {G} _ _ => ∃ F : GlobalTheory.Asc.Frames G, Std F :=
  fun _ _ _ _ _ _ _ G _ _ _ => ⟨_, auxiliaryFrames_standard G⟩

end GlobalTheory.AscFin

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.ProjCore

variable {D : D7}

theorem rat_entry' {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E) (i : Fin m) (j : Fin n) :
    (rat A : Mx D m n) i j = (1 : AF D.host.F) ⊗ₜ[D.host.F] A i j := rfl

theorem rat_mul_mem_hatMx {m n : ℕ} {ΛS : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} (M : Matrix (Fin m) (Fin m) D.host.E)
    (hM : ∀ y ∈ ΛT, M *ᵥ y ∈ ΛT) (I : Ideal (𝓞 D.host.E)) {z : Mx D m n} (hz : z ∈ hatMx (I • homLat ΛS ΛT)) :
    (rat M : Mx D m m) ⬝ z ∈ hatMx (I • homLat ΛS ΛT) := by
  have key : ∀ X ∈ I • homLat ΛS ΛT, M * X ∈ I • homLat ΛS ΛT := by
    intro X hX
    refine Submodule.smul_induction_on hX (fun r hr Y hY => ?_) (fun a b ha hb => ?_)
    · rw [Matrix.mul_smul]
      refine Submodule.smul_mem_smul hr ?_
      intro y hy
      rw [← Matrix.mulVec_mulVec]
      exact hM _ (hY _ hy)
    · rw [Matrix.mul_add]; exact add_mem ha hb
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, X, hX, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨α, hα, M * X, key X hX, ?_⟩
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, TensorProduct.tmul_sum, rat_entry',
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [Matrix.mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mul_neg]; exact neg_mem hx

theorem proj_mem_latCore : OnStd fun {D} _ _ _ {G} _ F => ∀ u ∈ latCore G 0, F.oz.jA ⬝ (F.oz.pA ⬝ u) ∈ latCore G 0 := by
  intro D hq T L μ0 hL sc G W M hM F hF u hu
  have hz := hF.zA
  have hqa : F.oz.qA * G.sp.dec0.a = 0 := by
    have hp := G.sp.dec0.perp
    rw [show Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat (G.sp.P 0).sp (Yc D 0) G.sp.dec0.ι) =
        (frameMat (G.sp.P 0).sp (Yc D 0) G.sp.dec0.ι)ᴴ from Matrix.ext fun _ _ => rfl, ← hz] at hp
    rw [OrthDec.qA, Matrix.mul_assoc, hp, Matrix.mul_zero]
  have hmap : ∀ x ∈ G.Λ (.core 0), (F.oz.iA * F.oz.qA) *ᵥ x ∈ G.Λ (.core 0) := by
    intro x hx
    have hx' : x ∈ G.sp.dec0.lat (L.ΛY 0) (fun _ => 1) := by rw [← G.sp.lat0]; exact hx
    obtain ⟨y, hy, c, hc, rfl⟩ := hx'
    show _ ∈ (G.sp.P 0).lat
    rw [G.sp.lat0]
    refine ⟨y, hy, 0, fun _ => Submodule.zero_mem _, ?_⟩
    rw [Matrix.mulVec_add, Matrix.mulVec_zero, add_zero, ← hz, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_assoc, F.oz.qA_iA, Matrix.mul_one, Matrix.mul_assoc, hqa, Matrix.mul_zero, Matrix.zero_mulVec, add_zero]
  have he : F.oz.jA ⬝ (F.oz.pA ⬝ u) = (rat (F.oz.iA * F.oz.qA) : Mx D _ _) ⬝ u := by
    rw [rat_mul, ← Matrix.mul_assoc]; rfl
  rw [he]
  refine ⟨?_, fun e he' => ?_⟩
  · exact GlobalTheory.OverTgt.mul_mem_latO (LT := G.Λ (.core 0)) (LT' := G.Λ (.core 0)) _
      (fun y hy => GlobalTheory.OrthSumLat.rat_mulVec_mem_latV _ hmap hy) hu.1
  · rw [← Matrix.mul_smul]
    exact rat_mul_mem_hatMx _ hmap _ (hu.2 e he')

end GlobalTheory.ProjCore
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.standardAuxiliaryFrames_fit_grid_ends : All fun {_} _ _ _ {G} W M => ∀ (v : CoreVol G) (F : GlobalTheory.Asc.Frames G), Std F → F.Ends v W M := by
  first | exact @GlobalTheory.AscFin.EndsPf.ends | exact GlobalTheory.AscFin.EndsPf.ends | (intros; apply GlobalTheory.AscFin.EndsPf.ends <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.doubledWeil_split_place_vacuum_eigenfunction : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)), (∀ w : HeightOneSpectrum (𝓞 E), ¬ Formalism.UG.IsInertAt F E v w) → v ∉ X.T → PsiUnr B.ψ v →
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a'))))
      (omd : GlobalTheory.DblVac.UD σ G.W →* Module.End ℂ (((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → AF F) → ℂ)),
    IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) G.M.co dd →
    IsUWeilSplit (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) B.ψ (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)) dd X.β (diagCols (Fin (a + a'))) omd →
    ∀ r : (Fin a × Fin (a + a') → AF F) → ℂ, Rest (evFin F v) (G.M.vac v) r →
    ∀ g ∈ GlobalTheory.DblVac.KD σ G.W v, ∃ μ : ℂ,
      omd g (boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x))) =
        μ • boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x)) := by
  first | exact @GlobalTheory.DblVacAny.split_eigen | exact GlobalTheory.DblVacAny.split_eigen | (intros; apply GlobalTheory.DblVacAny.split_eigen <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.BottomAct

open GlobalTheory.Grid (neg sgn ofSgn)

theorem conj_invT_of_unitary {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : Matrix.conjTranspose M * M = 1) :
    ((M⁻¹).transpose).map (starRingEnd ℂ) = M := by
  rw [Matrix.inv_eq_left_inv h]
  ext a b
  simp only [Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply, RCLike.star_def, Complex.conj_conj]

theorem conj_invT_compAt {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} (hV : V.gram = 1) (g : GA D V)
    (τ : D.what₂.Tau) :
    (((compAt θ τ (Formalism.L2.Theta.mt V g))⁻¹).transpose).map (starRingEnd ℂ) = compAt θ τ (Formalism.L2.Theta.mt V g) := by
  have h1 := GlobalTheory.StdUnn.CartanMove.compAt_isom hθ V g τ
  have hg : gramAt D V τ = 1 := by
    unfold gramAt
    rw [hV]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  rw [hg, Matrix.mul_one] at h1
  exact conj_invT_of_unitary h1

theorem om_pureTensorO_bottom : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X → ∀ (t : T) (g : GA D A) (P : MvPolynomial (FVar D WW.rank A.rank) ℂ), (X.ω t).toSgn true ((GlobalTheory.Grid.ofSgn true A).symm g, 1) (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) = pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B ((X.ω t).toSgn true ((GlobalTheory.Grid.ofSgn true A).symm g, 1) (X.f t)) (GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)) (fun τ => compAt W.θ τ (Formalism.L2.Theta.mt A g)) P) := by
  intro D T L sc G W i j A A' WW X hX t g P
  have hI := hX.is
  have hθ : IsInfFam W.θ := hI.isVac.2.inf
  have hψ : IsStdChar D W.ψ (-1) := hI.isVac.1
  have hom := hI.weil t
  have hsA : ∀ τ, X.rA.s τ = 1 := fun τ => (hX.std.2.2 τ).1
  have hsW : ∀ τ, X.rW.s τ = 1 := fun τ => (hX.stdW.2.2 τ).1
  have hBA : ∀ τ, X.rA.B τ = 1 := fun τ => (hX.std.2.2 τ).2
  have hf : IsThetaFunO W.ψ (neg A) WW (X.f t) := (GlobalTheory.ConstRatio.theta_f hI t).1
  have hmt : Formalism.L2.Theta.mt (neg A) ((ofSgn true A).symm g) = Formalism.L2.Theta.mt A g := by
    rw [← GlobalTheory.Grid.mt_ofSgn, MulEquiv.apply_symm_apply]
  set u : D.what₂.Tau → Matrix (Fin A.rank) (Fin A.rank) ℂ := fun τ => compAt W.θ τ (Formalism.L2.Theta.mt A g) with hu
  have one : ∀ τ, compAt W.θ τ (Formalism.L2.Theta.mt WW 1) = 1 := fun τ => GlobalTheory.StdUnn.CartanMove.compAt_mt_one W.θ τ WW
  have hop := GlobalTheory.OrientedHeis.om_pureTensorO D W.ψ W.θ (neg A) WW _ _ ((X.ω t).toSgn true) hom hθ
    (fun τ => -X.rA.s τ) (fun τ => -X.rA.s τ) X.rA.B (fun τ => X.rA.B τ * u τ) X.rW.s X.rW.s X.rW.B
    (fun τ => X.rW.B τ * 1) ((ofSgn true A).symm g) 1
    (fun τ => by rw [hmt, hsA, Matrix.neg_mul, Matrix.mul_neg, Matrix.one_mul, Matrix.mul_one])
    (fun τ => by rw [one, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [hmt, hBA, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [one, Matrix.one_mul, Matrix.mul_one]) (X.f t) hf P
  rw [hop.2]
  have hf' : IsThetaFunO W.ψ (neg A) WW ((X.ω t).toSgn true ((ofSgn true A).symm g, 1) (X.f t)) :=
    hom.om_pres _ _ hf
  have e1 : (fun τ => -X.rA.s τ) = fun _ => (-1 : Matrix (Fin A.rank) (Fin A.rank) ℂ) := funext fun τ => by rw [hsA]
  have e2 : X.rW.s = fun _ => (1 : Matrix (Fin WW.rank) (Fin WW.rank) ℂ) := funext hsW
  have key := GlobalTheory.FockNegSubst.pureTensorO_negSp_subst D W.ψ W.θ A WW hψ hθ X.rA.B u X.rW.B (fun _ => 1) _ hf' P
  have hunit : ∀ τ, (((u τ)⁻¹).transpose).map (starRingEnd ℂ) = u τ := fun τ => conj_invT_compAt hθ hX.std.1 g τ
  have hv : (fun _ : D.what₂.Tau => (1 : Matrix (Fin WW.rank) (Fin WW.rank) ℂ).map (starRingEnd ℂ)) = fun _ => 1 :=
    funext fun _ => Matrix.map_one _ (map_zero _) (map_one _)
  rw [funext hunit, hv] at key
  rw [e1, e2]
  exact key

end GlobalTheory.BottomAct

end
end
