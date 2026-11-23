module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.QuotientIsHausdorff
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle009
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle003
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA
public import ReciprocityTheory.SemistableReduction.Bundle002
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle003
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle002
public import ReciprocityTheory.SemistableReduction.Bundle019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.NormOrderStatement

@[expose] public section

section

namespace GlobalTheory.PropDiscCompare

open NumberField Topology ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}


open NumberField Topology in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
theorem _root_.GlobalTheory.PropDiscCompare.compact_of_local (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (h : _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.PropDisc X) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.ProperlyDiscontinuousFlags.ProperlyDiscontinuousOnFlags X := by
  intro K hK hKdom
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.PropDisc at h
  choose! U hU U' hU' hfin using h
  obtain ⟨t, ht, hcover⟩ := (hK.prod hK).elim_nhds_subcover
    (fun q : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r × _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r => U q.1 q.2 ×ˢ U' q.1 q.2)
    (fun q hq => prod_mem_nhds (hU q.1 (hKdom hq.1) q.2 (hKdom hq.2))
      (hU' q.1 (hKdom hq.1) q.2 (hKdom hq.2)))
  refine (t.finite_toSet.biUnion fun q hq =>
    hfin q.1 (hKdom (ht q hq).1) q.2 (hKdom (ht q hq).2)).subset ?_
  rintro γ ⟨hγ, x, hx, y, hy, b, hb, hxy⟩
  obtain ⟨q, hq, hxq⟩ := Set.mem_iUnion₂.mp (hcover (Set.mk_mem_prod hx hy))
  exact Set.mem_iUnion₂.mpr ⟨q, hq, hγ, x, hxq.1, y, hxq.2, b, hb, hxy⟩

end GlobalTheory.PropDiscCompare
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.GrpSep

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

noncomputable def dev {Ψ : Finset (E →+* ℂ)} {r : ℕ} (x0 : Frame Ψ r) (γ : GL (Fin r) E) :
    Frame Ψ r :=
  fun τ => ((mat x0 τ)⁻¹ * (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x0 τ - 1 :
    Matrix (Fin r) (Fin r) ℂ)

noncomputable def shift {Ψ : Finset (E →+* ℂ)} {r : ℕ} (x0 M : Frame Ψ r) : Frame Ψ r :=
  fun τ => (mat x0 τ * (mat M τ + 1) : Matrix (Fin r) (Fin r) ℂ)

noncomputable def oneF (Ψ : Finset (E →+* ℂ)) (r : ℕ) : Frame Ψ r :=
  fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)

end GlobalTheory.GrpSep

namespace GlobalTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma sgn_ne_zero_torus_haar_measure (p a : ℕ) : _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn p a ≠ 0 := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn; split_ifs <;> norm_num

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma det_mat_ne_zero_of_isOrth' {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {x0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r}
    (h : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0) (τ : X.Ψ) : (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ).det ≠ 0 := by
  intro h0
  have := congrArg Matrix.det (h τ)
  rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.gram_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul,
    Matrix.det_diagonal] at this
  exact (Finset.prod_ne_zero_iff.mpr fun a _ => by exact_mod_cast sgn_ne_zero_torus_haar_measure X.p0 a) this.symm

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma mem_dom_of_isOrth {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {x0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r}
    (h : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0) : x0 ∈ X.dom := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.dom _root_.ReciprocityTheory.ChartRestriction.G.FD.GG
  refine fun τ => ⟨det_mat_ne_zero_of_isOrth' X h τ, fun i => ?_⟩
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin _root_.ReciprocityTheory.ChartRestriction.G.FD.lminor
  rw [h τ, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
  simp only [Function.comp_apply, Fin.coe_castLE]
  rw [← Complex.ofReal_prod, Complex.ofReal_re,
    Fin.prod_univ_eq_prod_range (fun j => _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 j) i]
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.psgn
  exact mul_self_pos.mpr (Finset.prod_ne_zero_iff.mpr fun a _ => sgn_ne_zero_torus_haar_measure X.p0 a)

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma continuous_shift' {Ψ : Finset (E →+* ℂ)} {r : ℕ} (x0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r) :
    Continuous (fun M : Ψ → Fin r → Fin r → ℂ =>
      (_root_.GlobalTheory.GrpSep.shift x0 M : Ψ → Fin r → Fin r → ℂ)) := by
  unfold _root_.GlobalTheory.GrpSep.shift _root_.ReciprocityTheory.ChartRestriction.G.FD.mat
  refine continuous_pi fun τ => ?_
  exact continuous_const.matrix_mul ((continuous_apply τ).add continuous_const)

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma shift_zero_torus_haar_measure {Ψ : Finset (E →+* ℂ)} {r : ℕ} (x0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r) :
    _root_.GlobalTheory.GrpSep.shift x0 0 = x0 := by
  funext τ
  change _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ * (0 + 1) = x0 τ
  rw [zero_add, Matrix.mul_one]; rfl

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma exists_pos_le_of_finite_pos {α : Type*} (S : Set α) (hS : S.Finite) (f : α → ℝ)
    (hf : ∀ a ∈ S, 0 < f a) : ∃ δ > 0, ∀ a ∈ S, δ ≤ f a := by
  rcases S.eq_empty_or_nonempty with h | h
  · exact ⟨1, one_pos, by simp [h]⟩
  · obtain ⟨a0, ha0, hmin⟩ := Set.exists_min_image S f hS h
    exact ⟨f a0, hf a0 ha0, hmin⟩

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma oneF_mem_bor {Ψ : Finset (E →+* ℂ)} {r : ℕ} :
    _root_.GlobalTheory.GrpSep.oneF Ψ r ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor Ψ r := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor
  refine fun τ => ⟨?_, fun a c h => ?_⟩
  · change (1 : Matrix (Fin r) (Fin r) ℂ).det ≠ 0
    simp
  · change (1 : Matrix (Fin r) (Fin r) ℂ) a c = 0
    exact Matrix.one_apply_ne h.ne'

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma shift_dev_eq_lact {Ψ : Finset (E →+* ℂ)} {r : ℕ} (x0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r)
    (hdet : ∀ τ, (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ).det ≠ 0) (γ : GL (Fin r) E) :
    _root_.GlobalTheory.GrpSep.shift x0 (_root_.GlobalTheory.GrpSep.dev x0 γ) = _root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ x0 := by
  funext τ
  change _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ * ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ)⁻¹ * (γ : Matrix (Fin r) (Fin r) E).map τ.1 *
    _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ - 1 + 1) = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ
  rw [sub_add_cancel, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (Ne.isUnit (hdet τ)), Matrix.one_mul]

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma rmul_oneF' {Ψ : Finset (E →+* ℂ)} {r : ℕ} (x0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x0 (_root_.GlobalTheory.GrpSep.oneF Ψ r) = x0 := by
  funext τ
  change (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ * 1 : Matrix (Fin r) (Fin r) ℂ) = _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ
  exact Matrix.mul_one _


open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.grpSep : ∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r),
    _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0 → _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.PropDisc X →
    ∃ c : ℝ, 0 < c ∧ ∀ γ ∈ X.Γ, γ ≠ 1 → ∃ (τ : X.Ψ) (a b : Fin r),
      c ≤ ‖((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ)⁻¹ * (γ : Matrix (Fin r) (Fin r) E).map τ.1 * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ - 1) a b‖ := by
  intro r X x0 hO hP
  have hdom := mem_dom_of_isOrth X hO
  have hdet := det_mat_ne_zero_of_isOrth' X hO
  obtain ⟨U, hU, U', hU', hfin⟩ := hP x0 hdom x0 hdom
  have hV : (fun M : X.Ψ → Fin r → Fin r → ℂ =>
      (_root_.GlobalTheory.GrpSep.shift x0 M : X.Ψ → Fin r → Fin r → ℂ)) ⁻¹' U' ∈
      nhds (0 : X.Ψ → Fin r → Fin r → ℂ) :=
    (continuous_shift' x0).continuousAt.preimage_mem_nhds (by erw [shift_zero_torus_haar_measure]; exact hU')
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hV
  let S : Set (GL (Fin r) E) :=
    {γ | γ ∈ {γ | γ ∈ X.Γ ∧ ∃ u ∈ U, ∃ u' ∈ U', ∃ b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r,
      _root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ u = _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul u' b} \ ({1} : Set (GL (Fin r) E))}
  obtain ⟨δ, hδ, hmin⟩ := exists_pos_le_of_finite_pos S (hfin.subset (fun _ h => Set.sdiff_subset h))
    (fun γ => ‖(_root_.GlobalTheory.GrpSep.dev x0 γ : X.Ψ → Fin r → Fin r → ℂ)‖) (by
      rintro γ ⟨hγ, h1⟩
      refine norm_pos_iff.mpr fun h0 => h1 (Set.mem_singleton_iff.mpr ?_)
      refine X.Γ_free γ hγ.1 x0 hdom (_root_.GlobalTheory.GrpSep.oneF X.Ψ r) oneF_mem_bor ?_
      rw [← shift_dev_eq_lact x0 hdet, rmul_oneF']
      exact (congrArg (_root_.GlobalTheory.GrpSep.shift x0) h0).trans (shift_zero_torus_haar_measure x0))
  refine ⟨min ε δ, lt_min hε hδ, fun γ hγ h1 => ?_⟩
  by_contra hcon
  push_neg at hcon
  have hlt : ‖(_root_.GlobalTheory.GrpSep.dev x0 γ : X.Ψ → Fin r → Fin r → ℂ)‖ < min ε δ := by
    refine (pi_norm_lt_iff (lt_min hε hδ)).mpr fun τ => (pi_norm_lt_iff (lt_min hε hδ)).mpr
      fun a => (pi_norm_lt_iff (lt_min hε hδ)).mpr fun b => hcon τ a b
  have hmem : _root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ x0 ∈ U' := by
    rw [← shift_dev_eq_lact x0 hdet]
    exact hball (mem_ball_zero_iff.mpr (hlt.trans_le (min_le_left _ _)))
  have hS := hmin γ ⟨⟨hγ, x0, mem_of_mem_nhds hU, _, hmem, _root_.GlobalTheory.GrpSep.oneF X.Ψ r,
    oneF_mem_bor, (rmul_oneF' _).symm⟩, h1⟩
  exact absurd hS (not_le.mpr (hlt.trans_le (min_le_right _ _)))

end GlobalTheory
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace GlobalTheory


open NumberField MeasureTheory Topology in
open scoped ComplexOrder ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.norm_entry_le_of_gram_eq_smul_one {r : ℕ} (G x : Matrix (Fin r) (Fin r) ℂ) (s : ℂ)
    (hs : s * s = 1) (h : xᵀ * G * x.map (starRingEnd ℂ) = s • (1 : Matrix (Fin r) (Fin r) ℂ))
    (a b : Fin r) : ‖x a b‖ ≤ 1 + ‖G⁻¹ a a‖ := by
  set y := x.map (starRingEnd ℂ) with hy
  have h1 : xᵀ * (s • (G * y)) = 1 := by
    rw [Matrix.mul_smul, ← Matrix.mul_assoc, h, smul_smul, hs, one_smul]
  have h2 : (s • (G * y)) * xᵀ = 1 := mul_eq_one_comm.1 h1
  have h3 : G * (s • (y * xᵀ)) = 1 := by
    rw [Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.smul_mul]; exact h2
  have hinv : G⁻¹ = s • (y * xᵀ) := Matrix.inv_eq_right_inv h3
  have hentry : G⁻¹ a a = s * ((∑ c, ‖x a c‖ ^ 2 : ℝ) : ℂ) := by
    rw [hinv, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul]
    congr 1
    push_cast
    refine Finset.sum_congr rfl fun c _ => ?_
    simp [hy, Matrix.transpose_apply, Complex.conj_mul']
  have hsn : ‖s‖ = 1 := by
    have h4 := congrArg norm hs
    rw [norm_mul, norm_one] at h4
    nlinarith [norm_nonneg s]
  have hsum : 0 ≤ ∑ c, ‖x a c‖ ^ 2 := Finset.sum_nonneg fun c _ => sq_nonneg _
  have hnorm : ‖G⁻¹ a a‖ = ∑ c, ‖x a c‖ ^ 2 := by
    rw [hentry, norm_mul, hsn, one_mul, Complex.norm_of_nonneg hsum]
  have hle : ‖x a b‖ ^ 2 ≤ ∑ c, ‖x a c‖ ^ 2 :=
    Finset.single_le_sum (f := fun c => ‖x a c‖ ^ 2) (fun c _ => sq_nonneg _) (Finset.mem_univ b)
  rw [hnorm]
  nlinarith [sq_nonneg (‖x a b‖ - 1), norm_nonneg (x a b)]


open NumberField MeasureTheory Topology in
open scoped ComplexOrder ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.orthonormal_frames_bounded_of_definite :
    (∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r), (X.p0 = 0 ∨ X.p0 = r) →
      ∃ R : ℝ, ∀ x, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → ∀ τ a b, ‖x τ a b‖ ≤ R) := by
  intro r X hp
  refine ⟨1 + ∑ τ : X.Ψ, ∑ a : Fin r, ‖((X.Gm.map (τ : E →+* ℂ))⁻¹) a a‖,
    fun x hx τ a b => ?_⟩
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth at hx
  have hτ := hx τ
  obtain ⟨s, hs, hdiag⟩ : ∃ s : ℂ, s * s = 1 ∧
      Matrix.diagonal (fun a : Fin r => ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 a : ℝ) : ℂ)) = s • 1 := by
    rcases hp with h | h
    · refine ⟨-1, by norm_num, ?_⟩
      ext i j
      simp [h, _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn, Matrix.diagonal_apply, Matrix.one_apply]
    · refine ⟨1, by norm_num, ?_⟩
      ext i j
      simp [h, _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn, Matrix.diagonal_apply, Matrix.one_apply]
  have key : (Matrix.of (x τ))ᵀ * X.Gm.map (τ : E →+* ℂ) * (Matrix.of (x τ)).map (starRingEnd ℂ)
      = s • 1 := by
    rw [← hdiag, ← hτ]
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.gram _root_.ReciprocityTheory.ChartRestriction.G.FD.mat
    ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
      _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC, _root_.ReciprocityTheory.ChartRestriction.G.FD.col, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hb := _root_.GlobalTheory.norm_entry_le_of_gram_eq_smul_one _ _ s hs key a b
  have h1 : ‖((X.Gm.map (τ : E →+* ℂ))⁻¹) a a‖ ≤ ∑ a' : Fin r, ‖((X.Gm.map (τ : E →+* ℂ))⁻¹) a' a'‖ :=
    Finset.single_le_sum (f := fun a' => ‖((X.Gm.map (τ : E →+* ℂ))⁻¹) a' a'‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ a)
  have h2 : ∑ a' : Fin r, ‖((X.Gm.map (τ : E →+* ℂ))⁻¹) a' a'‖ ≤
      ∑ τ' : X.Ψ, ∑ a' : Fin r, ‖((X.Gm.map (τ' : E →+* ℂ))⁻¹) a' a'‖ :=
    Finset.single_le_sum (f := fun τ' : X.Ψ => ∑ a' : Fin r, ‖((X.Gm.map (τ' : E →+* ℂ))⁻¹) a' a'‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ τ)
  have hx' : ‖x τ a b‖ = ‖Matrix.of (x τ) a b‖ := rfl
  linarith

end GlobalTheory
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.FinCovol

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isCompact_orth_bounded :
    (∀ (r : ℕ) (X : Data E r) (R : ℝ),
      IsCompact {x : Frame X.Ψ r | IsOrth X x ∧ ∀ τ a b, ‖x τ a b‖ ≤ R}) := by
  intro r X R
  have h1 : IsClosed {x : Frame X.Ψ r | IsOrth X x} := by
    simp only [IsOrth, Set.ofPred_forall]
    refine isClosed_iInter fun τ => isClosed_eq ?_ continuous_const
    refine continuous_matrix fun a b => ?_
    simp only [gram, hermC, col, mat, Matrix.of_apply]
    fun_prop
  have h2 : IsClosed {x : Frame X.Ψ r | ∀ τ a b, ‖x τ a b‖ ≤ R} := by
    simp only [Set.ofPred_forall]
    refine isClosed_iInter fun τ => isClosed_iInter fun a => isClosed_iInter fun b =>
      isClosed_le ?_ continuous_const
    fun_prop
  refine Metric.isCompact_of_isClosed_isBounded (h1.inter h2) ?_
  refine (Metric.isBounded_closedBall (x := (0 : Frame X.Ψ r)) (r := |R|)).subset ?_
  rintro x ⟨-, hx⟩
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (abs_nonneg R)]
  intro τ
  rw [pi_norm_le_iff_of_nonneg (abs_nonneg R)]
  intro a
  rw [pi_norm_le_iff_of_nonneg (abs_nonneg R)]
  intro b
  exact (hx τ a b).trans (le_abs_self R)

end GlobalTheory.FinCovol
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.SpanIndex

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem relIndex_mul_le_of_le {A : Type} [AddCommGroup A] (M₁ M₂ W₁ W₂ Λ : AddSubgroup A)
    (h₁ : M₁ ≤ Λ ⊓ W₁) (h₂ : M₂ ≤ Λ ⊓ W₂)
    (hne : (M₁ ⊔ M₂).relIndex (Λ ⊓ (W₁ ⊔ W₂)) ≠ 0) :
    M₁.relIndex (Λ ⊓ W₁) * M₂.relIndex (Λ ⊓ W₂) ≤
      (M₁ ⊓ M₂).relIndex (Λ ⊓ (W₁ ⊓ W₂)) * (M₁ ⊔ M₂).relIndex (Λ ⊓ (W₁ ⊔ W₂)) := by
  rw [← GlobalTheory.relIndex_sup_mul_relIndex_inf A M₁ _ M₂ _ h₁ h₂, mul_comm, ← inf_inf_distrib_left]
  refine Nat.mul_le_mul_left _ (AddSubgroup.relIndex_le_of_le_right ?_ hne)
  exact sup_le (inf_le_inf_left _ le_sup_left) (inf_le_inf_left _ le_sup_right)


omit [IsCMField E] in
theorem span_le_inf_span {r : ℕ} (Λ : Submodule (𝓞 E) (Fin r → E)) {ι : Type}
    (w : ι → Fin r → E) (hw : ∀ a, w a ∈ Λ) :
    (Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup ≤
      Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup := by
  refine le_inf ?_ ?_
  · have : Submodule.span (𝓞 E) (Set.range w) ≤ Λ :=
      Submodule.span_le.2 (by rintro _ ⟨a, rfl⟩; exact hw a)
    exact fun x hx => this hx
  · exact fun x hx => Submodule.span_le_restrictScalars (𝓞 E) E _ hx

theorem relIndex_span_mul_le : (∀ (r : ℕ) (X : Data E r) (α β γ : Type) [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β] [DecidableEq γ] (w : α ⊕ β ⊕ γ → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → ((Submodule.span (𝓞 E) (Set.range (w ∘ (Sum.map id Sum.inl : α ⊕ β → α ⊕ β ⊕ γ)))).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range (w ∘ (Sum.map id Sum.inl : α ⊕ β → α ⊕ β ⊕ γ)))).toAddSubgroup)) * ((Submodule.span (𝓞 E) (Set.range (w ∘ (Sum.map id Sum.inr : α ⊕ γ → α ⊕ β ⊕ γ)))).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range (w ∘ (Sum.map id Sum.inr : α ⊕ γ → α ⊕ β ⊕ γ)))).toAddSubgroup)) ≤ ((Submodule.span (𝓞 E) (Set.range (w ∘ (Sum.inl : α → α ⊕ β ⊕ γ)))).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range (w ∘ (Sum.inl : α → α ⊕ β ⊕ γ)))).toAddSubgroup)) * ((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup))) := by
  intro r X α β γ _ _ _ _ _ _ w hw hΛ
  have hw' : LinearIndependent (𝓞 E) w := hw.restrict_scalars' (𝓞 E)
  obtain ⟨i₁, s₁⟩ := GlobalTheory.span_inf_sup_overlapping_parts (𝓞 E) _ α β γ w hw'
  obtain ⟨i₂, s₂⟩ := GlobalTheory.span_inf_sup_overlapping_parts E _ α β γ w hw
  have hne := relIndex_span_ne_zero r X _ w hw hΛ
  rw [← s₁, ← s₂, Submodule.sup_toAddSubgroup, Submodule.sup_toAddSubgroup] at hne
  have key := relIndex_mul_le_of_le _ _ _ _ _
    (span_le_inf_span X.Λ (w ∘ (Sum.map id Sum.inl : α ⊕ β → α ⊕ β ⊕ γ)) fun a => hΛ _)
    (span_le_inf_span X.Λ (w ∘ (Sum.map id Sum.inr : α ⊕ γ → α ⊕ β ⊕ γ)) fun a => hΛ _) hne
  rw [← i₁, ← i₂, ← s₁, ← s₂, Submodule.sup_toAddSubgroup, Submodule.sup_toAddSubgroup]
  exact key

end GlobalTheory.SpanIndex
end

section

namespace GlobalTheory

open NumberField ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.AlgT

theorem genericSection_reindex {F : Type} [Field F] {D N : ℕ} (j₀ : Fin (N + 1)) (x : Fin N → F) :
    ReciprocityTheory.MultiplicativeHeights.sImage (D := D) x = sImg (D := D) j₀ x ∘
      (Equiv.prodCongr (Equiv.refl (Fin (D + 1))) (Fin.cycleRange j₀).symm) := by
  funext p
  obtain ⟨i, j⟩ := p
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [ReciprocityTheory.MultiplicativeHeights.sImage, sImg, Fin.cycleRange_symm_zero]
  · simp [ReciprocityTheory.MultiplicativeHeights.sImage, sImg, Fin.cycleRange_symm_succ]

theorem genericSection_field {k F : Type} [Field k] [CharZero k] [Field F] [Algebra k F] {D N : ℕ}
    (j₀ : Fin (N + 1)) (x : Fin N → F) (hfg : (⊤ : IntermediateField k F).FG)
    (htr : Algebra.trdeg k F = D)
    (hJ : ∃ J : Fin D → Fin N, LinearIndependent F fun a => KaehlerDifferential.D k F (x (J a))) :
    AlgebraicIndependent k (sImg (D := D) j₀ x) ∧
      FiniteDimensional (IntermediateField.adjoin k (Set.range (sImg (D := D) j₀ x))) (OmS F D N) ∧
      Algebra.IsSeparable (IntermediateField.adjoin k (Set.range (sImg (D := D) j₀ x)))
        (OmS F D N) := by
  obtain ⟨hind, hfin⟩ := ReciprocityTheory.MultiplicativeHeights.Closed.fieldOfS k F D N x hfg htr hJ
  rw [genericSection_reindex j₀ x] at hind hfin
  rw [(Equiv.surjective _).range_comp] at hfin
  refine ⟨(algebraicIndependent_equiv _).1 hind, hfin, ?_⟩
  have : FiniteDimensional (IntermediateField.adjoin k (Set.range (sImg (D := D) j₀ x)))
    (OmS F D N) := hfin
  have : CharZero (IntermediateField.adjoin k (Set.range (sImg (D := D) j₀ x))) :=
    charZero_of_injective_algebraMap (algebraMap k _).injective
  infer_instance

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

end GlobalTheory
end
