module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle502
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsOrthogonalBasisDotProductApplyEq
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle504
import Formalism.LocalRingCardinality.DataHost
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepMetricSmooth
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle488
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle459
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle431
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle430
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.PcFc
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.PcFc

section Field
variable {E : Type} [Field E] {c : E →+* E}

theorem exists_congr_diag_rank (h2 : (2 : E) ≠ 0) (hc : ∀ t, c (c t) = t) {n ρ p : ℕ} (hn : ρ + p = n)
    {G : Matrix (Fin n) (Fin n) E} (hG : ∀ a b, c (G a b) = G b a) (hr : ρ ≤ G.rank) :
    ∃ (a : Matrix (Fin n) (Fin n) E) (d₁ : Fin ρ → E) (d₂ : Fin p → E), a.det ≠ 0 ∧
      (a.map c).transpose * G * a = bl hn (Matrix.diagonal d₁) 0 0 (Matrix.diagonal d₂) ∧
      (∀ i, c (d₁ i) = d₁ i) ∧ (∀ i, c (d₂ i) = d₂ i) ∧ ∀ i, d₁ i ≠ 0 := by
  classical
  obtain ⟨P, d, hP, hPG, hd, -⟩ := GlobalTheory.HermDiag.exists_congr_diagonal h2 hc hG
  have hQ : (P.map c).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero c).mpr hP
  have hrk : (Matrix.diagonal d).rank = G.rank := by
    rw [← hPG, Matrix.rank_mul_eq_left_of_isUnit_det _ _ (isUnit_iff_ne_zero.mpr hQ),
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ (by rw [Matrix.det_transpose]; exact isUnit_iff_ne_zero.mpr hP)]
  rw [Matrix.rank_diagonal, Fintype.card_subtype] at hrk
  obtain ⟨T, hTS, hTc⟩ := Finset.exists_subset_card_eq (hr.trans hrk.ge)
  let e : Fin ρ ⊕ Fin p ≃ Fin n := finSumFinEquiv.trans (finCongr hn)
  let A : Finset (Fin n) := Finset.univ.map ⟨fun i : Fin ρ => e (Sum.inl i), fun i j h => Sum.inl_injective (e.injective h)⟩
  have hAc : A.card = ρ := by simp [A]
  let e' : {x // x ∈ A} ≃ {x // x ∈ T} :=
    Fintype.equivOfCardEq (by rw [Fintype.card_coe, Fintype.card_coe, hAc, hTc])
  let σ : Equiv.Perm (Fin n) := e'.extendSubtype
  have hσ : ∀ i : Fin ρ, d (σ (e (Sum.inl i))) ≠ 0 := by
    intro i
    have hm : σ (e (Sum.inl i)) ∈ T := Equiv.extendSubtype_mem e' _ (Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    simpa using hTS hm
  refine ⟨(P.map c).submatrix id σ, fun i => d (σ (e (Sum.inl i))), fun j => d (σ (e (Sum.inr j))), ?_, ?_,
    fun i => hd _, fun j => hd _, hσ⟩
  · rw [Matrix.det_permute']
    refine mul_ne_zero ?_ hQ
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  · have hmc : (((P.map c).submatrix id σ).map c).transpose * G * (P.map c).submatrix id σ
        = (P.transpose * G * P.map c).submatrix σ σ := by
      ext i j
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply, id, hc]
    rw [hmc, hPG, Matrix.submatrix_diagonal_equiv]
    unfold PositivityTheory.Rg.Rsw.bl
    rw [Matrix.fromBlocks_diagonal, Matrix.submatrix_diagonal_equiv]
    congr 1
    funext x
    obtain ⟨y, rfl⟩ := e.surjective x
    cases y <;> simp [e]

end Field

theorem exists_cg_dsum {D : D7} {n ρ p : ℕ} (hn : ρ + p = n) (β : HermE D n) (hr : ρ ≤ β.1.rank) :
    ∃ (a : GL (Fin n) D.host.E) (b₀ : HermE D ρ) (β' : HermE D p), IsDiagInv b₀ ∧ cg a β = dsum hn b₀ β' := by
  obtain ⟨G, hG⟩ := β
  have hc : ∀ t : D.host.E, D.sp.cm.sig.toRingHom (D.sp.cm.sig.toRingHom t) = t := fun t => star_star t
  obtain ⟨a, d₁, d₂, ha, hEq, hd₁, hd₂, hne⟩ := exists_congr_diag_rank (c := D.sp.cm.sig.toRingHom) two_ne_zero hc hn
    (G := G) (fun i j => congrFun (congrFun hG j) i) hr
  have hdiag : ∀ {m : ℕ} (d : Fin m → D.host.E), (∀ i, D.sp.cm.sig.toRingHom (d i) = d i) →
      ((Matrix.diagonal d).map ⇑D.sp.cm.sig).transpose = Matrix.diagonal d := by
    intro m d hd
    rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose]
    congr 1
    funext i
    exact hd i
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero a ha, ⟨Matrix.diagonal d₁, hdiag d₁ hd₁⟩,
    ⟨Matrix.diagonal d₂, hdiag d₂ hd₂⟩, ⟨Matrix.isDiag_diagonal _, ?_⟩, ?_⟩
  · rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hne i
  · exact Subtype.ext hEq

end GlobalTheory.CompanionTheory.PcFc
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WhitFree.AvgInf

theorem exists_mem_boxK_two_pow {K W : Type} [CommRing K] [Fintype W] (κ : K ≃+* (W → ℂ)) {n M : ℕ}
    {R : ℝ} (hR : 0 < R) (X : Fin n → Fin M → K) :
    ∃ j : ℕ, X ∈ boxK κ (fun _ _ => (2 : ℝ) ^ j * R) := by
  set B : ℝ := ∑ a, ∑ i, ∑ w, ‖κ (X a i) w‖ with hB
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (B / R) (one_lt_two : (1 : ℝ) < 2)
  refine ⟨j, fun a i w => ?_⟩
  have h1 : ‖κ (X a i) w‖ ≤ ∑ w, ‖κ (X a i) w‖ :=
    Finset.single_le_sum (f := fun w => ‖κ (X a i) w‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ w)
  have h2 : ∑ w, ‖κ (X a i) w‖ ≤ ∑ i, ∑ w, ‖κ (X a i) w‖ :=
    Finset.single_le_sum (f := fun i => ∑ w, ‖κ (X a i) w‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)
  have h3 : ∑ i, ∑ w, ‖κ (X a i) w‖ ≤ B :=
    Finset.single_le_sum (f := fun a => ∑ i, ∑ w, ‖κ (X a i) w‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
      (Finset.mem_univ a)
  have h4 : B < (2 : ℝ) ^ j * R := (div_lt_iff₀ hR).1 hj
  linarith

theorem exists_large_ofReal_div_mul_le {A : ℝ} (hA : 0 ≤ A) {D ε : ℝ≥0∞} (hD : D ≠ ⊤) (hε : ε ≠ 0) :
    ∃ R : ℝ, 1 ≤ R ∧ ENNReal.ofReal (A / R) * D ≤ ε := by
  obtain ⟨δ, hδ0, hδ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (pos_iff_ne_zero.2 hε)
  have hδ0' : (0 : ℝ) < δ := by exact_mod_cast hδ0
  have hDr : 0 ≤ D.toReal := ENNReal.toReal_nonneg
  have hq : 0 ≤ A * D.toReal / δ := by positivity
  refine ⟨1 + A * D.toReal / δ, by linarith, ?_⟩
  have hRpos : 0 < 1 + A * D.toReal / δ := by linarith
  have hkey : A / (1 + A * D.toReal / δ) * D.toReal ≤ δ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hRpos]
    have : (δ : ℝ) * (1 + A * D.toReal / δ) = δ + A * D.toReal := by
      field_simp
    rw [this]
    have : (0 : ℝ) ≤ δ := hδ0'.le
    linarith
  calc ENNReal.ofReal (A / (1 + A * D.toReal / δ)) * D
      = ENNReal.ofReal (A / (1 + A * D.toReal / δ)) * ENNReal.ofReal D.toReal := by
        rw [ENNReal.ofReal_toReal hD]
    _ = ENNReal.ofReal (A / (1 + A * D.toReal / δ) * D.toReal) :=
        (ENNReal.ofReal_mul (by positivity)).symm
    _ ≤ ENNReal.ofReal (δ : ℝ) := ENNReal.ofReal_le_ofReal hkey
    _ = δ := ENNReal.ofReal_coe_nnreal
    _ ≤ ε := hδ.le

theorem tsum_geometric_half_mul (c d : ℝ≥0∞) :
    ∑' j : ℕ, c * (2⁻¹ : ℝ≥0∞) ^ j * d = c * 2 * d := by
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, ENNReal.tsum_geometric,
    ENNReal.one_sub_inv_two, inv_inv]

theorem shell_real_identity {c R : ℝ} (hR : 0 < R) (e j : ℕ) :
    c / ((2 : ℝ) ^ j * R) ^ (e + 1) * ((2 : ℝ) ^ (j + 1) * R) ^ e
      = c * 2 ^ e / R * (1 / 2) ^ j := by
  have h2 : (2 : ℝ) ^ (j + 1) * R = 2 * ((2 : ℝ) ^ j * R) := by ring
  have key : ∀ P : ℝ, P ≠ 0 → c / P ^ (e + 1) * (2 * P) ^ e = c * 2 ^ e / P := by
    intro P hP
    rw [mul_pow, pow_succ]
    field_simp
  rw [h2, key _ (by positivity), one_div, inv_pow]
  field_simp

theorem tail_small_of_density :
    ∀ (K W : Type) [CommRing K] [Fintype W] (κ : K ≃+* (W → ℂ)) (n M : ℕ) (H : Type) [MeasurableSpace H] [MeasurableSpace (Fin n → Fin M → K)] (μ : Measure (Fin n → Fin M → K)) (ν : Measure H) (q : (Fin n → Fin M → K) → H) (C₀ : ℝ≥0∞), C₀ ≠ ⊤ → (∀ r : Fin n → W → ℝ, (∀ a w, 0 < r a w) → GlobalTheory.CompanionTheory.WhitFree.AvgInf.DenLE μ ν q (GlobalTheory.CompanionTheory.WhitFree.AvgInf.boxK κ r) (C₀ * ∏ a, ∏ w, ENNReal.ofReal (r a w) ^ (2 * (M - n)))) → Measurable q → (∀ r : Fin n → W → ℝ, MeasurableSet (GlobalTheory.CompanionTheory.WhitFree.AvgInf.boxK (M := M) κ r)) → ∀ φ : (Fin n → Fin M → K) → ℂ, (∀ k : ℕ, ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R → ∀ X, X ∉ GlobalTheory.CompanionTheory.WhitFree.AvgInf.boxK κ (fun _ _ => R) → ‖φ X‖ ≤ C / R ^ k) → ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ R : ℝ, 1 ≤ R ∧ ∀ Y, MeasurableSet Y → ∫⁻ X in (GlobalTheory.CompanionTheory.WhitFree.AvgInf.boxK κ (fun _ _ => R))ᶜ ∩ q ⁻¹' Y, ‖φ X‖ₑ ∂μ ≤ ε * ν Y := by
  intro K W _ _ κ n M H _ _ μ ν q C₀ hC₀ hden hq hbox φ hφ ε hε
  obtain ⟨e, he⟩ : ∃ e : ℕ, e = 2 * (M - n) * Fintype.card W * n := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ := hφ (e + 1)
  have hA : 0 ≤ |C| * (2 : ℝ) ^ e := by positivity
  obtain ⟨R, hR1, hRε⟩ := exists_large_ofReal_div_mul_le hA
    (ENNReal.mul_ne_top (by simp) hC₀ : (2 : ℝ≥0∞) * C₀ ≠ ⊤) hε
  refine ⟨R, hR1, fun Y hY => ?_⟩
  have hR0 : 0 < R := by linarith
  let S : ℕ → Set (Fin n → Fin M → K) := fun j =>
    (boxK κ (fun _ _ => (2 : ℝ) ^ (j + 1) * R) \ boxK κ (fun _ _ => (2 : ℝ) ^ j * R)) ∩ q ⁻¹' Y
  have hcover : (boxK κ (fun _ _ => R))ᶜ ∩ q ⁻¹' Y ⊆ ⋃ j, S j := by
    rintro X ⟨hX, hXY⟩
    classical
    have hex := exists_mem_boxK_two_pow κ hR0 X
    have hne : Nat.find hex ≠ 0 := by
      intro h0
      have := Nat.find_spec hex
      rw [h0] at this
      simp only [pow_zero, one_mul] at this
      exact hX this
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hne
    refine Set.mem_iUnion.2 ⟨j, ⟨?_, ?_⟩, hXY⟩
    · have := Nat.find_spec hex
      rw [hj] at this
      exact this
    · exact Nat.find_min hex (by omega)
  have hshell : ∀ j, ∫⁻ X in S j, ‖φ X‖ₑ ∂μ
      ≤ ENNReal.ofReal (|C| * 2 ^ e / R) * (2⁻¹ : ℝ≥0∞) ^ j * (C₀ * ν Y) := by
    intro j
    have hRj : 1 ≤ (2 : ℝ) ^ j * R := by
      have : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ one_le_two
      nlinarith
    have hRj0 : 0 < (2 : ℝ) ^ j * R := by linarith
    have hSm : MeasurableSet (S j) := ((hbox _).diff (hbox _)).inter (hq hY)
    have hpt : ∀ X ∈ S j, ‖φ X‖ₑ ≤ ENNReal.ofReal (|C| / ((2 : ℝ) ^ j * R) ^ (e + 1)) := by
      rintro X ⟨⟨-, hX⟩, -⟩
      rw [← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ((hC _ hRj X hX).trans ?_)
      exact div_le_div_of_nonneg_right (le_abs_self C) (by positivity)
    have hmu : μ (S j) ≤ C₀ * ENNReal.ofReal (((2 : ℝ) ^ (j + 1) * R) ^ e) * ν Y := by
      have h1 := hden (fun _ _ => (2 : ℝ) ^ (j + 1) * R) (fun _ _ => by positivity) Y hY
      have h2 : μ (S j) ≤ μ (boxK κ (fun _ _ => (2 : ℝ) ^ (j + 1) * R) ∩ q ⁻¹' Y) :=
        measure_mono fun X hX => ⟨hX.1.1, hX.2⟩
      have h3 : (∏ a : Fin n, ∏ w : W, ENNReal.ofReal ((2 : ℝ) ^ (j + 1) * R) ^ (2 * (M - n)))
          = ENNReal.ofReal (((2 : ℝ) ^ (j + 1) * R) ^ e) := by
        rw [ENNReal.ofReal_pow (by positivity), he]
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
      rw [h3] at h1
      exact h2.trans h1
    calc ∫⁻ X in S j, ‖φ X‖ₑ ∂μ
        ≤ ∫⁻ _ in S j, ENNReal.ofReal (|C| / ((2 : ℝ) ^ j * R) ^ (e + 1)) ∂μ :=
          setLIntegral_mono' hSm hpt
      _ = ENNReal.ofReal (|C| / ((2 : ℝ) ^ j * R) ^ (e + 1)) * μ (S j) := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal (|C| / ((2 : ℝ) ^ j * R) ^ (e + 1)) *
            (C₀ * ENNReal.ofReal (((2 : ℝ) ^ (j + 1) * R) ^ e) * ν Y) := by gcongr
      _ = (ENNReal.ofReal (|C| / ((2 : ℝ) ^ j * R) ^ (e + 1)) *
            ENNReal.ofReal (((2 : ℝ) ^ (j + 1) * R) ^ e)) * (C₀ * ν Y) := by ring
      _ = ENNReal.ofReal (|C| * 2 ^ e / R) * (2⁻¹ : ℝ≥0∞) ^ j * (C₀ * ν Y) := by
          rw [← ENNReal.ofReal_mul (by positivity), shell_real_identity hR0,
            ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
          congr 3
          rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
          simp
  calc ∫⁻ X in (boxK κ (fun _ _ => R))ᶜ ∩ q ⁻¹' Y, ‖φ X‖ₑ ∂μ
      ≤ ∫⁻ X in ⋃ j, S j, ‖φ X‖ₑ ∂μ := lintegral_mono_set hcover
    _ ≤ ∑' j, ∫⁻ X in S j, ‖φ X‖ₑ ∂μ := lintegral_iUnion_le _ _
    _ ≤ ∑' j : ℕ, ENNReal.ofReal (|C| * 2 ^ e / R) * (2⁻¹ : ℝ≥0∞) ^ j * (C₀ * ν Y) :=
        ENNReal.tsum_le_tsum hshell
    _ = ENNReal.ofReal (|C| * 2 ^ e / R) * 2 * (C₀ * ν Y) := tsum_geometric_half_mul _ _
    _ = ENNReal.ofReal (|C| * 2 ^ e / R) * (2 * C₀) * ν Y := by ring
    _ ≤ ε * ν Y := by gcongr

end GlobalTheory.CompanionTheory.WhitFree.AvgInf
end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WhitFree.AvgInf.Topo

open GlobalTheory.CompanionTheory.WhitFree.AvgInf

variable {K W : Type} [CommRing K] [TopologicalSpace K] [Fintype W]

lemma cont_coord (κ : K ≃+* (W → ℂ)) (hκ : IsHomeomorph κ) {n M : ℕ} (b : Fin n) (i : Fin M) (w : W) :
    Continuous fun X : Fin n → Fin M → K => κ (X b i) w :=
  (continuous_apply w).comp (hκ.continuous.comp ((continuous_apply i).comp (continuous_apply b)))

lemma isOpen_nearK (κ : K ≃+* (W → ℂ)) (hκ : IsHomeomorph κ) {n M : ℕ} (w : W) (s : Fin n → ℂ) (ε : ℝ) :
    IsOpen (nearK (M := M) κ w s ε) := by
  have : nearK (M := M) κ w s ε = ⋂ i, {X | ‖∑ b, s b * κ (X b i) w‖ < ε} := by
    ext X; simp [nearK]
  rw [this]
  refine isOpen_iInter_of_finite fun i => ?_
  refine isOpen_lt ?_ continuous_const
  refine Continuous.norm ?_
  refine continuous_finsetSum _ fun b _ => ?_
  exact continuous_const.mul (cont_coord κ hκ b i w)

lemma isCompact_boxK (κ : K ≃+* (W → ℂ)) (hκ : IsHomeomorph κ) {n M : ℕ} (r : Fin n → W → ℝ) :
    IsCompact (boxK (M := M) κ r) := by
  let e : K ≃ₜ (W → ℂ) := hκ.homeomorph κ
  let Φ : (Fin n → Fin M → K) ≃ₜ (Fin n → Fin M → W → ℂ) :=
    Homeomorph.piCongrRight fun _ => Homeomorph.piCongrRight fun _ => e
  have hB : IsCompact (Set.univ.pi fun a : Fin n => Set.univ.pi fun _ : Fin M =>
      Set.univ.pi fun w : W => Metric.closedBall (0 : ℂ) (r a w)) :=
    isCompact_univ_pi fun a => isCompact_univ_pi fun _ => isCompact_univ_pi fun w =>
      isCompact_closedBall _ _
  have : boxK (M := M) κ r = Φ ⁻¹' (Set.univ.pi fun a : Fin n => Set.univ.pi fun _ : Fin M =>
      Set.univ.pi fun w : W => Metric.closedBall (0 : ℂ) (r a w)) := by
    ext X
    simp [boxK, Φ, e]
  rw [this]
  exact (Homeomorph.isCompact_preimage Φ).2 hB

lemma linIndep_iff (κ : K ≃+* (W → ℂ)) {n M : ℕ} (X : Fin n → Fin M → K) :
    LinearIndependent K X ↔ ∀ w, LinearIndependent ℂ (fun b i => κ (X b i) w) := by
  classical
  constructor
  · intro hX w
    rw [Fintype.linearIndependent_iff] at hX ⊢
    intro t ht b
    have key := hX (fun b => κ.symm (Pi.single w (t b))) (by
      funext i
      apply κ.injective
      funext w'
      have := congrFun ht i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this

      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul,
      RingEquiv.apply_symm_apply, Pi.zero_apply, map_zero, Finset.sum_apply, Pi.mul_apply]
      by_cases h : w' = w
      · subst h; simpa using this
      · simp [Pi.single_apply, h])
    have := congrFun (congrArg κ (key b)) w
    simpa using this
  · intro h
    rw [Fintype.linearIndependent_iff]
    intro c hc b
    apply κ.injective
    funext w
    have hw := h w
    rw [Fintype.linearIndependent_iff] at hw
    have := hw (fun b => κ (c b) w) (by
      funext i
      have := congrArg (fun y => κ y w) (congrFun hc i)

      simpa [Finset.sum_apply, map_sum, map_mul] using this) b
    simpa using this

lemma isOpen_linIndep (κ : K ≃+* (W → ℂ)) (hκ : IsHomeomorph κ) (n M : ℕ) :
    IsOpen {X : Fin n → Fin M → K | LinearIndependent K X} := by
  have : {X : Fin n → Fin M → K | LinearIndependent K X} =
      ⋂ w, (fun X : Fin n → Fin M → K => fun b i => κ (X b i) w) ⁻¹'
        {Y : Fin n → Fin M → ℂ | LinearIndependent ℂ Y} := by
    ext X; simp [linIndep_iff κ X]
  rw [this]
  refine isOpen_iInter_of_finite fun w => ?_
  refine isOpen_setOfPred_linearIndependent.preimage ?_
  exact continuous_pi fun b => continuous_pi fun i => cont_coord κ hκ b i w

end GlobalTheory.CompanionTheory.WhitFree.AvgInf.Topo

namespace GlobalTheory.CompanionTheory.WhitFree.AvgInf.Topo

open GlobalTheory.CompanionTheory.WhitFree.AvgInf

variable {K W : Type} [CommRing K] [TopologicalSpace K] [Fintype W]

lemma goodK_subset (κ : K ≃+* (W → ℂ)) {n M : ℕ} (R ε : ℝ) (hε : 0 < ε) :
    goodK (n := n) (M := M) κ R ε ⊆ {X : Fin n → Fin M → K | LinearIndependent K X} := by
  intro X hX
  rcases hX with ⟨-, hX⟩
  show LinearIndependent K X
  rw [Fintype.linearIndependent_iff]
  intro c hc b0
  by_contra h0
  have hk : κ (c b0) ≠ 0 := by
    intro h; exact h0 (κ.injective (by simpa using h))
  obtain ⟨w, hw⟩ := Function.ne_iff.1 hk
  haveI : Nonempty (Fin n) := ⟨b0⟩
  obtain ⟨a, ha⟩ := Finite.exists_max fun b => ‖κ (c b) w‖
  have hca : κ (c a) w ≠ 0 := by
    intro h
    have := ha b0
    rw [h, norm_zero] at this
    exact hw (norm_le_zero_iff.1 this)
  have hsum : ∀ i, ∑ b, κ (c b) w * κ (X b i) w = 0 := by
    intro i
    have := congrArg (fun y => κ y w) (congrFun hc i)

    simpa [Finset.sum_apply, map_sum, map_mul] using this
  apply hX
  simp only [Set.mem_iUnion]
  refine ⟨w, a, fun b => κ (c b) w / κ (c a) w, ⟨div_self hca, fun b => ?_⟩, ?_⟩
  · rw [norm_div]
    exact div_le_one_of_le₀ (ha b) (norm_nonneg _)
  · intro i
    have : ∑ b, κ (c b) w / κ (c a) w * κ (X b i) w = (κ (c a) w)⁻¹ * ∑ b, κ (c b) w * κ (X b i) w := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      ring
    rw [this, hsum i, mul_zero, norm_zero]
    exact hε

theorem boxK_goodK_topology : ∀ (K W : Type) [CommRing K] [TopologicalSpace K] [Fintype W] (κ : K ≃+* (W → ℂ)), IsHomeomorph κ → ∀ n M : ℕ, (∀ r : Fin n → W → ℝ, IsCompact (GlobalTheory.CompanionTheory.WhitFree.AvgInf.boxK (M := M) κ r)) ∧ IsOpen {X : Fin n → Fin M → K | LinearIndependent K X} ∧ ∀ R ε : ℝ, 0 < ε → IsCompact (GlobalTheory.CompanionTheory.WhitFree.AvgInf.goodK (n := n) (M := M) κ R ε) ∧ GlobalTheory.CompanionTheory.WhitFree.AvgInf.goodK (n := n) (M := M) κ R ε ⊆ {X : Fin n → Fin M → K | LinearIndependent K X} := by
  intro K W _ _ _ κ hκ n M
  refine ⟨fun r => isCompact_boxK κ hκ r, isOpen_linIndep κ hκ n M, fun R ε hε => ⟨?_, goodK_subset κ R ε hε⟩⟩
  refine (isCompact_boxK κ hκ _).diff ?_
  exact isOpen_iUnion fun w => isOpen_iUnion fun a => isOpen_iUnion fun s => isOpen_iUnion fun _ =>
    isOpen_nearK κ hκ w s ε

end GlobalTheory.CompanionTheory.WhitFree.AvgInf.Topo
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm)
open GlobalTheory.CompanionTheory.MPDict

namespace GlobalTheory.CompanionTheory.MixZ

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem exists_block_ne_zero_of_isUnder {y : CxPts (mpStr ℤ m n) σ₀} {z : (Σ k, Bk n k) → ℂ} (h : IsUnder y z) (k : Fin (m + 1)) :
    ∃ i, z ⟨k, i⟩ ≠ 0 :=
  ⟨ptChart _ k, (h k _).1.1 (CxPts.mem_ptsIn.2 (mem_ptChart _ k))⟩

theorem combLine_unit_a (A : HermLine (Bk n)) : (combLine (fun _ : Unit => A) 1).a = A.a := by
  simp [combLine]

theorem combLine_unit_h (A : HermLine (Bk n)) {z : (Σ k, Bk n k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    (combLine (fun _ : Unit => A) 1).h z = A.h z := by
  simp [combLine, if_pos hz]

theorem combLine_unit_h_off (A : HermLine (Bk n)) {z : (Σ k, Bk n k) → ℂ} (hz : ¬ ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    (combLine (fun _ : Unit => A) 1).h z = 0 :=
  if_neg hz

theorem isHermRep_combLine_unit {M : HermLB (mpStr ℤ m n)} {A : HermLine (Bk n)} (hA : IsHermRep M A) :
    IsHermRep M (combLine (fun _ : Unit => A) 1) := by
  obtain ⟨u, h₁, h₂, h₃⟩ := hA
  refine ⟨u, h₁, fun i c c' => ?_, fun i c y z hu hy => ?_⟩
  · rw [combLine_unit_a]
    exact h₂ i c c'
  · rw [combLine_unit_h A (exists_block_ne_zero_of_isUnder hu), combLine_unit_a]
    exact h₃ i c y z hu hy

theorem existsRead : ExistsRead := by
  rintro m n M ⟨c, t, e⟩
  obtain ⟨A, hA, -⟩ := GlobalTheory.T.hermRep_twisted_bundle_exists m n M c t e
  have hs : IsSmoothHerm A := GlobalTheory.CompanionTheory.MPDict.SmoothRep.isSmoothHerm_of_isHermRep m n M A hA
  exact ⟨combLine (fun _ : Unit => A) 1, isSmoothHerm_combLine (fun _ => hs) 1, isHermRep_combLine_unit hA,
    fun z hz => combLine_unit_h_off A hz⟩

end GlobalTheory.CompanionTheory.MixZ
end
end
