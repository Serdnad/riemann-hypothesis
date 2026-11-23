module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle002
public import Lemmata.PosDefOfRealQuadratic.QuadFormRealSmul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle005
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
public import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle005
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA

open Matrix
open scoped ComplexOrder Matrix

variable {p q : ℕ}

theorem cross_psd (Z W : Matrix (Fin p) (Fin q) ℂ) (hW : (1 - W * Wᴴ).PosDef) :
    ((1 - Z * Wᴴ) * (1 - W * Wᴴ)⁻¹ * (1 - Z * Wᴴ)ᴴ - (1 - Z * Zᴴ)).PosSemidef := by
  set B := 1 - W * Wᴴ with hBdef
  set C := 1 - Z * Wᴴ with hCdef
  set S := B⁻¹ with hSdef
  have hBu : IsUnit B.det := isUnit_iff_ne_zero.2 hW.det_pos.ne'
  have hSB : S * B = 1 := Matrix.nonsing_inv_mul B hBu
  have hBS : B * S = 1 := Matrix.mul_nonsing_inv B hBu
  have hBh : Bᴴ = B := hW.1
  have hS : Sᴴ = S := by rw [hSdef, Matrix.conjTranspose_nonsing_inv, hBh]
  have h1 : (C * S - 1) * B * (C * S - 1)ᴴ = C * S * Cᴴ - C - Cᴴ + B := by
    have e : (C * S - 1) * B = C - B := by
      rw [Matrix.sub_mul, Matrix.mul_assoc, hSB, Matrix.mul_one, Matrix.one_mul]
    rw [e, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hS, Matrix.conjTranspose_one,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_one,
      ← Matrix.mul_assoc B S, hBS, Matrix.one_mul, Matrix.mul_assoc C S]
    abel
  have h2 : C + Cᴴ - B = (1 - Z * Zᴴ) + (W - Z) * (W - Z)ᴴ := by
    rw [hCdef, hBdef]
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_one,
      Matrix.conjTranspose_conjTranspose, Matrix.sub_mul, Matrix.mul_sub]
    abel
  have e : C * S * Cᴴ - (1 - Z * Zᴴ) = (C * S - 1) * B * (C * S - 1)ᴴ + (W - Z) * (W - Z)ᴴ := by
    have hA : (1 - Z * Zᴴ) = C + Cᴴ - B - (W - Z) * (W - Z)ᴴ := by rw [h2]; abel
    rw [h1, hA]; abel
  rw [e]
  exact (hW.posSemidef.mul_mul_conjTranspose_same _).add (posSemidef_self_mul_conjTranspose _)

theorem det_re_pos_im {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosDef) :
    0 < A.det.re ∧ A.det.im = 0 := by
  have h := hA.det_pos
  rw [Complex.lt_def] at h
  exact ⟨by simpa using h.1, by simpa using h.2.symm⟩

theorem det_eq_ofReal {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosDef) :
    A.det = ((A.det.re : ℝ) : ℂ) :=
  Complex.ext (by simp) (by simp [(det_re_pos_im hA).2])

theorem det_mul_det_le_normSq_det (Z W : Matrix (Fin p) (Fin q) ℂ) (hZ : (1 - Z * Zᴴ).PosDef)
    (hW : (1 - W * Wᴴ).PosDef) :
    (1 - Z * Zᴴ).det.re * (1 - W * Wᴴ).det.re ≤ Complex.normSq (1 - Z * Wᴴ).det := by
  have hm := ReciprocityTheory.L2DbarEstimates.I.maDet p ((1 - Z * Wᴴ) * (1 - W * Wᴴ)⁻¹ * (1 - Z * Wᴴ)ᴴ)
    (1 - Z * Zᴴ) hZ.posSemidef (cross_psd Z W hW)
  obtain ⟨hb, hbi⟩ := det_re_pos_im hW
  set b := (1 - W * Wᴴ).det.re
  have hdet : ((1 - Z * Wᴴ) * (1 - W * Wᴴ)⁻¹ * (1 - Z * Wᴴ)ᴴ).det =
      ((Complex.normSq (1 - Z * Wᴴ).det / b : ℝ) : ℂ) := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv, Matrix.det_conjTranspose,
      Ring.inverse_eq_inv', det_eq_ofReal hW, mul_right_comm, Complex.star_def, Complex.mul_conj]
    push_cast; ring
  rw [hdet, Complex.ofReal_re] at hm
  rwa [le_div_iff₀ hb] at hm

theorem det_re_le_one {Z : Matrix (Fin p) (Fin q) ℂ} (hZ : (1 - Z * Zᴴ).PosDef) :
    (1 - Z * Zᴴ).det.re ≤ 1 := by
  have hm := ReciprocityTheory.L2DbarEstimates.I.maDet p 1 (1 - Z * Zᴴ) hZ.posSemidef
    (by rw [sub_sub_cancel]; exact posSemidef_self_mul_conjTranspose Z)
  simpa using hm

end ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB

open Matrix Topology Filter
open scoped ComplexOrder Matrix
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up

theorem quad_im {m : ℕ} {A : Matrix (Fin m) (Fin m) ℂ} (hA : A.IsHermitian) (x : Fin m → ℂ) :
    (star x ⬝ᵥ (A *ᵥ x)).im = 0 := by
  rw [← Complex.conj_eq_iff_im]

  simp only [dotProduct, mulVec, map_sum, map_mul, Pi.star_apply, Complex.star_def,
  Complex.conj_conj, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h := hA.apply i j
  rw [Complex.star_def] at h
  rw [h]; ring

theorem posDef_eventually {X : Type*} [TopologicalSpace X] {m : ℕ}
    (A : X → Matrix (Fin m) (Fin m) ℂ) (hc : ∀ i j, Continuous fun x => A x i j)
    (hH : ∀ x, (A x).IsHermitian) (x0 : X) (h0 : (A x0).PosDef) :
    ∀ᶠ x in 𝓝 x0, (A x).PosDef := by
  first | exact Bl.PosDefOfRealQuadratic.goal1 .. | (apply Bl.PosDefOfRealQuadratic.goal1 <;> assumption) | (intros; apply Bl.PosDefOfRealQuadratic.goal1 <;> assumption)

theorem cont_coord {n : ℕ} (i : Fin n) : Continuous fun v : V n => v i := by
  have h : (fun v : V n => v i) = ⇑(EuclideanSpace.proj i : V n →L[ℂ] ℂ) := by
    funext v; simp
  rw [h]; exact ContinuousLinearMap.continuous _

theorem herm_one_sub {p q : ℕ} (Z : Matrix (Fin p) (Fin q) ℂ) : (1 - Z * Zᴴ).IsHermitian :=
  isHermitian_one.sub (isHermitian_mul_conjTranspose_self Z)

theorem cont_entry {X : Type*} [TopologicalSpace X] {f p q : ℕ} (g : X → V (nD f p q))
    (hg : ∀ i, Continuous fun x => g x i) (k : Fin f) (a b : Fin p) :
    Continuous fun x => (1 - Zof (g x) k * (Zof (g x) k)ᴴ : Matrix (Fin p) (Fin p) ℂ) a b := by
  simp only [Matrix.sub_apply, Matrix.mul_apply, conjTranspose_apply, Zof, Matrix.of_apply]
  exact continuous_const.sub (continuous_finsetSum _ fun c _ =>
    (hg _).mul (continuous_star.comp (hg _)))

theorem isOpen_of {X : Type*} [TopologicalSpace X] {f p q : ℕ} (g : X → V (nD f p q))
    (hg : ∀ i, Continuous fun x => g x i) :
    IsOpen {x | ∀ k, (1 - Zof (g x) k * (Zof (g x) k)ᴴ).PosDef} := by
  refine isOpen_iff_mem_nhds.2 fun x0 hx0 => ?_
  exact Filter.eventually_all.2 fun k => posDef_eventually _ (cont_entry g hg k)
    (fun x => herm_one_sub _) x0 (hx0 k)

theorem isOpen_Dset (f p q : ℕ) : IsOpen (Dset f p q) :=
  isOpen_of (fun v : V (nD f p q) => v) cont_coord

end ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
end

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

namespace ModeHalfA

open Matrix NumberField Complex ReciprocityTheory.ChartRestriction.G.FD Topology Filter
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

noncomputable def sf (p0 : ℕ) (α β : Fin r → ℂ) : ℂ :=
  ∑ k : Fin r, ((sgn p0 (k : ℕ) : ℝ) : ℂ) * α k * conj (β k)

def cl (N : Fin r → Fin r → ℂ) (a : Fin r) : Fin r → ℂ := fun k => N k a

noncomputable def Ag (p0 : ℕ) (hp : p0 ≤ r) (N : Fin r → Fin r → ℂ) : Matrix (Fin p0) (Fin p0) ℂ :=
  Matrix.of fun a b => sf p0 (cl N (Fin.castLE hp a)) (cl N (Fin.castLE hp b))

noncomputable def Ms (p0 : ℕ) (hp : p0 ≤ r) (N : Fin r → Fin r → ℂ) (v : Fin r → ℂ) : ℝ :=
  2 * (∑ a : Fin p0, ∑ b : Fin p0, sf p0 v (cl N (Fin.castLE hp a)) * (Ag p0 hp N)⁻¹ a b *
    conj (sf p0 v (cl N (Fin.castLE hp b)))).re - (sf p0 v v).re

private lemma hermC_eq_dotProduct_upper_bounds (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u v : Fin r → ℂ) :
    hermC τ G u v = u ⬝ᵥ (G.map τ *ᵥ fun b => conj (v b)) := by
  simp only [ReciprocityTheory.ChartRestriction.G.FD.hermC, dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum, mul_assoc]

private lemma gram_eq_upper_bounds (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (Y : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G Y = Yᵀ * G.map τ * Y.map conj := by
  ext i j
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, Matrix.of_apply, ReciprocityTheory.ChartRestriction.G.FD.hermC, ReciprocityTheory.ChartRestriction.G.FD.col,
    Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

private lemma hermC_mulVec_eq_dotProduct_gram (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (Y : Matrix (Fin r) (Fin r) ℂ) (w n : Fin r → ℂ) :
    hermC τ G (Y *ᵥ w) (Y *ᵥ n) = w ⬝ᵥ (gram τ G Y *ᵥ fun b => conj (n b)) := by
  have hc : (fun b => conj ((Y *ᵥ n) b)) = Y.map conj *ᵥ fun b => conj (n b) := by
    funext b

    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
  rw [hermC_eq_dotProduct_upper_bounds, hc, gram_eq_upper_bounds, dotProduct_comm, Matrix.dotProduct_mulVec,
    ← Matrix.mulVec_transpose, dotProduct_comm, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

private lemma det_ne_zero_of_gram_eq_diagonal_sgn (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (p0 : ℕ)
    (Y : Matrix (Fin r) (Fin r) ℂ)
    (hY : gram τ G Y = diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) : Y.det ≠ 0 := by
  intro h0
  have h1 := congrArg Matrix.det hY
  rw [gram_eq_upper_bounds, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul,
    Matrix.det_diagonal] at h1
  exact (Finset.prod_ne_zero_iff.mpr fun a _ => by unfold sgn; split_ifs <;> norm_num) h1.symm

theorem maj_chart (X : Data E r) {w : Frame X.Ψ r} {τ : X.Ψ} {Y : Matrix (Fin r) (Fin r) ℂ}
    (hY : FD.gram τ.1 X.Gm Y = diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ))
    (N : Fin r → Fin r → ℂ) (hw : mat w τ = Y * Matrix.of N) (v : Fin r → ℂ) :
    X.maj w τ v = Ms X.p0 X.p0_le N (Y⁻¹ *ᵥ v) := by
  have hS : ∀ u' n : Fin r → ℂ, hermC τ.1 X.Gm (Y *ᵥ u') (Y *ᵥ n) = sf X.p0 u' n := by
    intro u' n
    rw [hermC_mulVec_eq_dotProduct_gram, hY]
    simp only [sf, dotProduct, Matrix.mulVec_diagonal]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hdetY := det_ne_zero_of_gram_eq_diagonal_sgn τ.1 X.Gm X.p0 Y hY
  have hv : v = Y *ᵥ (Y⁻¹ *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdetY), Matrix.one_mulVec]
  have hcol : ∀ a, FD.col (mat w τ) a = Y *ᵥ cl N a := by
    intro a
    rw [hw]
    funext k
    simp [ReciprocityTheory.ChartRestriction.G.FD.col, cl, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have hgp : X.gramPos w τ = Ag X.p0 X.p0_le N := by
    ext a b
    simp only [Data.gramPos, Matrix.submatrix_apply, ReciprocityTheory.ChartRestriction.G.FD.gram, Matrix.of_apply, Ag]
    rw [hcol, hcol, hS]
  unfold Data.maj Data.posPart Ms
  rw [hgp]
  conv_lhs => rw [hv]
  simp only [hcol, hS]

theorem dom_of_orth (X : Data E r) {u : Frame X.Ψ r} (hu : IsOrth X u) : u ∈ X.dom := by
  intro τ
  have hY := hu τ
  refine ⟨det_ne_zero_of_gram_eq_diagonal_sgn τ.1 X.Gm X.p0 _ hY, fun i => ?_⟩
  have hd : dmin X.Gm u τ i = ((psgn X.p0 i : ℝ) : ℂ) := by
    unfold dmin lminor
    rw [hY, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
    simp only [Function.comp_apply, Fin.coe_castLE, psgn, Complex.ofReal_prod]
    exact Fin.prod_univ_eq_prod_range (fun a => ((sgn X.p0 a : ℝ) : ℂ)) i
  rw [hd, Complex.ofReal_re]
  have hne : psgn X.p0 i ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun a _ => by unfold sgn; split_ifs <;> norm_num
  exact mul_self_pos.mpr hne

theorem maj_orth (X : Data E r) {u : Frame X.Ψ r} (hu : IsOrth X u) (τ : X.Ψ) (v : Fin r → ℂ) :
    X.maj u τ v = ∑ a, ‖((mat u τ)⁻¹ *ᵥ v) a‖ ^ 2 := by
  have hY := hu τ
  set N : Fin r → Fin r → ℂ := fun i j => (1 : Matrix (Fin r) (Fin r) ℂ) i j with hN
  have hw : mat u τ = mat u τ * Matrix.of N := by
    rw [show Matrix.of N = 1 from rfl, Matrix.mul_one]
  rw [maj_chart X hY N hw v]
  set w := (mat u τ)⁻¹ *ᵥ v
  have hsf : ∀ (α : Fin r → ℂ) (b : Fin r), sf X.p0 α (cl N b) = ((sgn X.p0 (b : ℕ) : ℝ) : ℂ) * α b := by
    intro α b
    unfold sf cl
    rw [Finset.sum_eq_single b]
    · simp [hN]
    · intro k _ hk
      simp [hN, Matrix.one_apply_ne hk]
    · intro h
      exact absurd (Finset.mem_univ b) h
  have hAg : Ag X.p0 X.p0_le N = 1 := by
    ext a b
    simp only [Ag, Matrix.of_apply, hsf]
    by_cases hab : a = b
    · subst hab
      simp [cl, hN, sgn]
    · have hne : (Fin.castLE X.p0_le b : Fin r) ≠ Fin.castLE X.p0_le a :=
        fun h => hab (Fin.castLE_injective _ h).symm
      simp [cl, hN, Matrix.one_apply_ne hne, Matrix.one_apply_ne hab]
  have hcast : ∀ g : Fin r → ℝ, ∑ a : Fin X.p0, g (Fin.castLE X.p0_le a) =
      ∑ k : Fin r, if (k : ℕ) < X.p0 then g k else 0 := by
    intro g
    rw [← Finset.sum_filter]
    have hset : Finset.univ.filter (fun k : Fin r => (k : ℕ) < X.p0) =
        Finset.univ.map (Fin.castLEEmb X.p0_le) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
      constructor
      · intro hk
        exact ⟨⟨k, hk⟩, Fin.ext rfl⟩
      · rintro ⟨a, rfl⟩
        exact a.isLt
    rw [hset, Finset.sum_map]
    rfl
  have hinner : ∀ a : Fin X.p0, ∑ b : Fin X.p0, sf X.p0 w (cl N (Fin.castLE X.p0_le a)) *
      (1 : Matrix (Fin X.p0) (Fin X.p0) ℂ) a b * conj (sf X.p0 w (cl N (Fin.castLE X.p0_le b))) =
      ((‖w (Fin.castLE X.p0_le a)‖ ^ 2 : ℝ) : ℂ) := by
    intro a
    rw [Finset.sum_eq_single a (fun b _ hb => by rw [Matrix.one_apply_ne' hb, mul_zero, zero_mul])
      (fun h => absurd (Finset.mem_univ a) h)]
    rw [Matrix.one_apply_eq, mul_one, hsf]
    have ha : ((Fin.castLE X.p0_le a : Fin r) : ℕ) < X.p0 := by simp
    simp only [sgn, ha, if_true, Complex.ofReal_one, one_mul]
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hww : (sf X.p0 w w).re = ∑ k : Fin r, sgn X.p0 (k : ℕ) * ‖w k‖ ^ 2 := by
    unfold sf
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_mul, Complex.ofReal_re]
  unfold Ms
  rw [hAg, inv_one]
  simp only [hinner]
  rw [← Complex.ofReal_sum, Complex.ofReal_re, hww]
  have hc := hcast (fun k => ‖w k‖ ^ 2)
  beta_reduce at hc
  rw [hc, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold sgn
  split_ifs <;> ring

end ModeHalfA

end ReciprocityTheory.ChartRestriction.G.AR.Up
end
