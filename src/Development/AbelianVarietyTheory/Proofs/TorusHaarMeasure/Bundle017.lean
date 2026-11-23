module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle005
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle015
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfE
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH

@[expose] public section

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.NormFactor

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma nfac_eq_prod_norm_dmin_ratio_rpow {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) :
    X.nfac la x = ∏ τ, ∏ i : Fin r,
      ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.succ / _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.castSucc‖ ^ (-(la τ i : ℝ) / 2) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.nfac _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin
  rfl

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma blockTriangular_id_of_mem_bor {r : ℕ} {Ψ : Finset (E →+* ℂ)} {b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r} (hb : b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor Ψ r)
    (τ : Ψ) : (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ).BlockTriangular id := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor at hb
  intro a c hca
  exact (hb τ).2 a c hca

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma mat_diag_ne_zero_of_mem_bor {r : ℕ} {Ψ : Finset (E →+* ℂ)} {b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r}
    (hb : b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor Ψ r) (τ : Ψ) (j : Fin r) : _root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ j j ≠ 0 := by
  have hdet := (show (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ).det ≠ 0 by unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor at hb; exact (hb τ).1)
  rw [Matrix.det_of_upperTriangular (blockTriangular_id_of_mem_bor hb τ)] at hdet
  exact Finset.prod_ne_zero_iff.1 hdet j (Finset.mem_univ j)

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma diag_prod_ne_zero_of_mem_bor {r : ℕ} {Ψ : Finset (E →+* ℂ)} {b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r}
    (hb : b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor Ψ r) (τ : Ψ) (i : Fin (r + 1)) :
    ∏ j : Fin i, _root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ (Fin.castLE (by omega) j) (Fin.castLE (by omega) j) ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun j _ => mat_diag_ne_zero_of_mem_bor hb τ _

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma gram_rmul_eq_transpose_mul_gram {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) (τ : X.Ψ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.gram (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) τ) =
      (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ).transpose * _root_.ReciprocityTheory.ChartRestriction.G.FD.gram (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) * (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ).map (starRingEnd ℂ) := by
  have hmul : _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) τ = _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul
    conv_lhs => unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.mat
    rfl
  rw [hmul, _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.gram_mul]

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma dmin_rmul_eq_diag_prod_mul_conj {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) (hb : b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r)
    (τ : X.Ψ) (i : Fin (r + 1)) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) τ i = (∏ j : Fin i, _root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ (Fin.castLE (by omega) j) (Fin.castLE (by omega) j)) *
      _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i * starRingEnd ℂ (∏ j : Fin i, _root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ (Fin.castLE (by omega) j) (Fin.castLE (by omega) j)) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin
  rw [gram_rmul_eq_transpose_mul_gram]
  exact _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.lminor_conj (blockTriangular_id_of_mem_bor hb τ) i

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma diag_prod_succ {r : ℕ} (M : Matrix (Fin r) (Fin r) ℂ) (i : Fin r) :
    ∏ j : Fin (i.succ : ℕ), M (Fin.castLE (by omega) j) (Fin.castLE (by omega) j) =
      (∏ j : Fin (i.castSucc : ℕ), M (Fin.castLE (by omega) j) (Fin.castLE (by omega) j)) * M i i := by
  show ∏ j : Fin ((i : ℕ) + 1), M (Fin.castLE (by omega) j) (Fin.castLE (by omega) j) = _
  rw [Fin.prod_univ_castSucc]
  rfl

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma norm_ratio_rmul_lemma_2 {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r)
    (hb : b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r) (τ : X.Ψ) (i : Fin r) :
    ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) τ i.succ / _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) τ i.castSucc‖ =
      ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ i i‖ ^ 2 * ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.succ / _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.castSucc‖ := by
  have hp := diag_prod_ne_zero_of_mem_bor hb τ i.castSucc
  rw [dmin_rmul_eq_diag_prod_mul_conj X x b hb τ i.succ, dmin_rmul_eq_diag_prod_mul_conj X x b hb τ i.castSucc, diag_prod_succ]
  simp only [norm_div, norm_mul, map_mul, RCLike.norm_conj]
  have hp' : ‖∏ j : Fin (i.castSucc : ℕ), _root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ (Fin.castLE (by omega) j) (Fin.castLE (by omega) j)‖ ≠ 0 :=
    norm_ne_zero_iff.2 hp
  by_cases hm : ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.castSucc‖ = 0
  · simp [hm]
  · field_simp

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma rpow_sq_mul_eq_inv_zpow_mul_rpow {d t : ℝ} (hd : 0 ≤ d) (ht : 0 ≤ t) (l : ℤ) :
    (d ^ 2 * t) ^ (-(l : ℝ) / 2) = (d ^ l)⁻¹ * t ^ (-(l : ℝ) / 2) := by
  rw [Real.mul_rpow (by positivity) ht, ← Real.rpow_natCast, ← Real.rpow_mul hd]
  congr 1
  rw [show ((2 : ℕ) : ℝ) * (-(l : ℝ) / 2) = -(l : ℝ) by push_cast; ring, Real.rpow_neg hd,
    Real.rpow_intCast]


open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.NormFactor.norm_bchar_mul_nfac_rmul {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r)
    {x b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx : x ∈ X.dom) (hb : b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r) :
    ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.bchar la b‖ * X.nfac la (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) = X.nfac la x := by
  rw [nfac_eq_prod_norm_dmin_ratio_rpow, nfac_eq_prod_norm_dmin_ratio_rpow]
  simp_rw [norm_ratio_rmul_lemma_2 X x b hb, rpow_sq_mul_eq_inv_zpow_mul_rpow (norm_nonneg _) (norm_nonneg _),
    Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  have hbc : ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.bchar la b‖ = ∏ τ, ∏ i : Fin r, ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ i i‖ ^ la τ i := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.bchar _root_.ReciprocityTheory.ChartRestriction.G.FD.mat
    simp [norm_prod, norm_zpow]
  have hne : ∏ τ, ∏ i : Fin r, ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ i i‖ ^ la τ i ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun τ _ => Finset.prod_ne_zero_iff.2 fun i _ =>
      zpow_ne_zero _ (norm_ne_zero_iff.2 (mat_diag_ne_zero_of_mem_bor hb τ i))
  rw [hbc, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]


open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.NormFactor.nfacRmul_holds : _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.NfacRmulStatement (E := E) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.NfacRmulStatement
  intro r X la x hx b hb
  have hne : ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.bchar la b‖ ≠ 0 := norm_ne_zero_iff.2 (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE.bchar_ne X la hb)
  rw [eq_inv_mul_iff_mul_eq₀ hne]
  exact _root_.GlobalTheory.NormFactor.norm_bchar_mul_nfac_rmul X la hx hb


open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.NormFactor.dmin_lact {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {γ : GL (Fin r) E}
    (hγ : γ ∈ X.Γ) (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) (τ : X.Ψ) (i : Fin (r + 1)) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ x) τ i = _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin
  rw [_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS.gram_lact X hγ x τ]


open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.NormFactor.nfacLact_holds : _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.NfacLactStatement (E := E) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.NfacLactStatement
  intro r X la γ hγ x _
  rw [nfac_eq_prod_norm_dmin_ratio_rpow, nfac_eq_prod_norm_dmin_ratio_rpow]
  simp only [_root_.GlobalTheory.NormFactor.dmin_lact X hγ]


open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.NormFactor.pnormInv_holds : _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.PnormInvStatement (E := E) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.PnormInvStatement
  intro r X la P hP γ hγ x hx b hb
  have hpn : ∀ y, X.pnorm la P y = ‖P y‖ * X.nfac la y := by
    intro y
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm
    rw [nfac_eq_prod_norm_dmin_ratio_rpow]
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.IsSec at hP
  obtain ⟨-, hPb, hPγ⟩ := hP
  have hxb := _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS.dom_rmul X hx hb
  have hlact := _root_.GlobalTheory.NormFactor.nfacLact_holds (E := E)
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.NfacLactStatement at hlact
  rw [hpn, hpn, hPγ γ hγ _ hxb, norm_mul, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE.chi_norm X la hγ, one_mul, hlact r X la γ hγ _ hxb,
    hPb x hx b hb, norm_mul, ← _root_.GlobalTheory.NormFactor.norm_bchar_mul_nfac_rmul X la hx hb]
  ring


open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.NormFactor.nfac_transform :
    _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.NfacRmulStatement (E := E) ∧ _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.NfacLactStatement (E := E) ∧ _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.PnormInvStatement (E := E) :=
  ⟨_root_.GlobalTheory.NormFactor.nfacRmul_holds, _root_.GlobalTheory.NormFactor.nfacLact_holds, _root_.GlobalTheory.NormFactor.pnormInv_holds⟩

end GlobalTheory.NormFactor
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix ComplexConjugate

namespace GlobalTheory.MajNear

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

omit [NumberField E] [IsCMField E] in
theorem hermC_mulVec {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (M : Matrix (Fin r) (Fin r) ℂ) (a b : Fin r → ℂ) :
    hermC τ G (M *ᵥ a) (M *ᵥ b) = ∑ i, ∑ j, a i * gram τ G M i j * conj (b j) := by

  simp only [hermC, gram, col, Matrix.of_apply, Matrix.mulVec, dotProduct, map_sum, map_mul,
  Finset.sum_mul, Finset.mul_sum]
  have h : ∀ (f : Fin r → Fin r → Fin r → Fin r → ℂ),
      ∑ k, ∑ l, ∑ j, ∑ i, f k l i j = ∑ i, ∑ j, ∑ k, ∑ l, f k l i j := by
    intro f
    calc ∑ k, ∑ l, ∑ j, ∑ i, f k l i j = ∑ k, ∑ l, ∑ i, ∑ j, f k l i j :=
          Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => Finset.sum_comm
      _ = ∑ k, ∑ i, ∑ l, ∑ j, f k l i j := Finset.sum_congr rfl fun k _ => Finset.sum_comm
      _ = ∑ i, ∑ k, ∑ l, ∑ j, f k l i j := Finset.sum_comm
      _ = ∑ i, ∑ k, ∑ j, ∑ l, f k l i j :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => Finset.sum_comm
      _ = ∑ i, ∑ j, ∑ k, ∑ l, f k l i j := Finset.sum_congr rfl fun i _ => Finset.sum_comm
  rw [h (fun k l i j => M k i * a i * τ (G k l) * (conj (M l j) * conj (b j)))]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring


omit [NumberField E] [IsCMField E] in
theorem isom_of_gram_eq {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    {M N : Matrix (Fin r) (Fin r) ℂ} (hN : N.det ≠ 0) (h : gram τ G M = gram τ G N)
    (u v : Fin r → ℂ) :
    hermC τ G ((M * N⁻¹) *ᵥ u) ((M * N⁻¹) *ᵥ v) = hermC τ G u v := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hermC_mulVec, h, ← hermC_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (Ne.isUnit hN),
    Matrix.one_mulVec, Matrix.one_mulVec]

theorem col_mul {r : ℕ} (g M : Matrix (Fin r) (Fin r) ℂ) (a : Fin r) :
    col (g * M) a = g *ᵥ col M a := by
  funext k
  simp [col, Matrix.mul_apply, Matrix.mulVec, dotProduct]

omit [NumberField E] [IsCMField E] in
theorem gram_isom {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    {g : Matrix (Fin r) (Fin r) ℂ} (hg : ∀ u v, hermC τ G (g *ᵥ u) (g *ᵥ v) = hermC τ G u v)
    (M : Matrix (Fin r) (Fin r) ℂ) : gram τ G (g * M) = gram τ G M := by
  ext a b
  simp only [gram, Matrix.of_apply, col_mul, hg]

theorem maj_isom {r : ℕ} (X : Data E r) (τ : X.Ψ) {x y : Frame X.Ψ r}
    {g : Matrix (Fin r) (Fin r) ℂ}
    (hg : ∀ u v, hermC τ.1 X.Gm (g *ᵥ u) (g *ᵥ v) = hermC τ.1 X.Gm u v)
    (hxy : mat y τ = g * mat x τ) (v : Fin r → ℂ) :
    X.maj y τ (g *ᵥ v) = X.maj x τ v := by
  simp only [Data.maj, Data.posPart, Data.gramPos, hxy, gram_isom τ.1 X.Gm hg, col_mul, hg]

theorem mat_cpt {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) (z : V (nd X)) (τ : X.Ψ) :
    mat (cpt X x z) τ = mat x τ * mat (nmat X z) τ := rfl

theorem continuous_cpt {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) : Continuous (cpt X x) :=
  continuous_pi fun τ => continuous_pi fun a => continuous_pi fun b =>
    (IW.cpt_entry_cd X x τ a b).continuous

theorem maj_near_orth :
    (∀ (r : ℕ) (X : Data E r), ∀ x ∈ X.dom, ∀ ε : ℝ, 0 < ε → ∀ᶠ y in 𝓝 x, y ∈ X.dom ∧ ∀ (τ : X.Ψ) (v : Fin r → ℂ), X.maj x τ v ≤ (1 + ε) * X.maj y τ v ∧ X.maj y τ v ≤ (1 + ε) * X.maj x τ v) → (∀ (r : ℕ) (X : Data E r) (ε : ℝ), 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → cpt X x z ∈ X.dom ∧ ∀ (τ : X.Ψ) (v : Fin r → ℂ), X.maj x τ v ≤ (1 + ε) * X.maj (cpt X x z) τ v ∧ X.maj (cpt X x z) τ v ≤ (1 + ε) * X.maj x τ v) := by
  intro H r X ε hε
  have ho : IsOrth X (x0F X) := fun τ => (X.signature τ).choose_spec.2
  have hd : x0F X ∈ X.dom := IW.orth_mem_dom X _ ho
  have ht : Filter.Tendsto (cpt X (x0F X)) (𝓝 0) (𝓝 (x0F X)) := by
    have := (continuous_cpt X (x0F X)).tendsto 0
    rwa [IW.cpt_zero] at this
  obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff.1 (ht.eventually (H r X _ hd ε hε))
  refine ⟨min δ 1, lt_min hδ one_pos, min_le_right _ _, fun x hx z hz => ?_⟩
  obtain ⟨hz0, hm⟩ := hb (y := z) (by rw [dist_zero_right]; exact hz.trans_le (min_le_left _ _))
  have hxd : x ∈ X.dom := IW.orth_mem_dom X _ hx
  have hiso : ∀ τ : X.Ψ, ∀ u v, hermC τ.1 X.Gm ((mat x τ * (mat (x0F X) τ)⁻¹) *ᵥ u)
      ((mat x τ * (mat (x0F X) τ)⁻¹) *ᵥ v) = hermC τ.1 X.Gm u v := fun τ =>
    isom_of_gram_eq τ.1 X.Gm (hd τ).1 ((hx τ).trans (ho τ).symm)
  have h1 : ∀ τ : X.Ψ, mat x τ = (mat x τ * (mat (x0F X) τ)⁻¹) * mat (x0F X) τ := fun τ => by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (Ne.isUnit (hd τ).1), Matrix.mul_one]
  have h2 : ∀ τ : X.Ψ, mat (cpt X x z) τ =
      (mat x τ * (mat (x0F X) τ)⁻¹) * mat (cpt X (x0F X) z) τ := fun τ => by
    rw [mat_cpt, mat_cpt, ← Matrix.mul_assoc, ← h1]
  have hdet : ∀ τ : X.Ψ, (mat x τ * (mat (x0F X) τ)⁻¹).det ≠ 0 := fun τ h0 => by
    have := (hxd τ).1
    rw [h1, Matrix.det_mul, h0, zero_mul] at this
    exact this rfl
  refine ⟨fun τ => ⟨?_, fun i => ?_⟩, fun τ v => ?_⟩
  · rw [h2, Matrix.det_mul]
    exact mul_ne_zero (hdet τ) (hz0 τ).1
  · have := (hz0 τ).2 i
    simp only [dmin] at this ⊢
    rwa [h2, gram_isom τ.1 X.Gm (hiso τ)]
  · obtain ⟨w, rfl⟩ : ∃ w, v = (mat x τ * (mat (x0F X) τ)⁻¹) *ᵥ w :=
      ⟨(mat x τ * (mat (x0F X) τ)⁻¹)⁻¹ *ᵥ v, by
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (Ne.isUnit (hdet τ)), Matrix.one_mulVec]⟩
    rw [maj_isom X τ (hiso τ) (h1 τ), maj_isom X τ (hiso τ) (h2 τ)]
    exact hm τ w

end GlobalTheory.MajNear
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
theorem _root_.GlobalTheory.T.firstMinimum_lower_of_lineHeights : (∀ (r : ℕ) (X : Data E r) (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → 0 < r → ∀ m : ℝ, 0 < m → ∃ ε : ℝ, 0 < ε ∧ ∀ x, IsOrth X x → (∀ W : Submodule E (Fin r → E), Module.finrank E W = 1 → m ≤ d x W) → ε ≤ X.la1 x) := by
  first | exact @GlobalTheory.LineHeight.exists_la1_lower_bound_of_line_heights | exact GlobalTheory.LineHeight.exists_la1_lower_bound_of_line_heights | (intros; apply GlobalTheory.LineHeight.exists_la1_lower_bound_of_line_heights <;> assumption)
end
