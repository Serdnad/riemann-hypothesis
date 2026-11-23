module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle008
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle020
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajorantNormalForms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

namespace ModeHalfC

open Matrix NumberField Complex ReciprocityTheory.ChartRestriction.G.FD Topology Filter ModeHalfA ReciprocityTheory.ChartRestriction.G.AR.Inst
  ReciprocityTheory.L2DbarEstimates Module

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem posDef_int_lower {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.PosDef) :
    ∃ m0 : ℝ, 0 < m0 ∧ ∀ x : Fin N → ℤ, x ≠ 0 →
      m0 ≤ (fun i => (x i : ℝ)) ⬝ᵥ (A *ᵥ fun i => (x i : ℝ)) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    exact ⟨1, one_pos, fun x hx => absurd (Subsingleton.elim x 0) hx⟩
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  let q : (Fin N → ℝ) → ℝ := fun y => y ⬝ᵥ (A *ᵥ y)
  have hqc : Continuous q :=
    continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)
  have hpos : ∀ y : Fin N → ℝ, y ≠ 0 → 0 < q y := by
    intro y hy
    have h0 := hA.dotProduct_mulVec_pos hy
    simpa [q] using h0

  obtain ⟨y0, hy0, hmin⟩ := (isCompact_sphere (0 : Fin N → ℝ) 1).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr zero_le_one) hqc.continuousOn
  have hy0ne : y0 ≠ 0 := by
    intro h
    rw [h, mem_sphere_zero_iff_norm, norm_zero] at hy0
    exact zero_ne_one hy0
  refine ⟨q y0, hpos y0 hy0ne, fun x hx => ?_⟩
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hx (funext hc)
  have hs1 : 1 ≤ ‖(fun i => (x i : ℝ))‖ := by
    have h1 : (1 : ℝ) ≤ |(x i : ℝ)| := by exact_mod_cast Int.one_le_abs hi
    calc (1 : ℝ) ≤ ‖(x i : ℝ)‖ := by rw [Real.norm_eq_abs]; exact h1
      _ ≤ ‖(fun i => (x i : ℝ))‖ := norm_le_pi_norm (fun i => (x i : ℝ)) i
  set xr : Fin N → ℝ := fun i => (x i : ℝ) with hxr
  have hs0 : ‖xr‖ ≠ 0 := (lt_of_lt_of_le one_pos hs1).ne'
  have hy : ‖xr‖⁻¹ • xr ∈ Metric.sphere (0 : Fin N → ℝ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hs0]
  have hq : q xr = ‖xr‖ ^ 2 * q (‖xr‖⁻¹ • xr) := by
    simp only [q, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
    field_simp
  have h3 : q y0 ≤ q (‖xr‖⁻¹ • xr) := hmin hy
  have h4 : 0 < q y0 := hpos y0 hy0ne
  have hs2 : 1 ≤ ‖xr‖ ^ 2 := by nlinarith
  show q y0 ≤ q xr
  rw [hq]
  nlinarith

theorem first_minimum_pos (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (hne : ∃ v ∈ X.Λ, v ≠ 0) :
    0 < X.la1 x := by
  obtain ⟨b, hb, h⟩ := ReciprocityTheory.ChartRestriction.G.FD.MajorantNormalForms.exists_normal_frame (X := X) hx
  have horth : IsOrth X (rmul x b) := fun τ => (h τ).1
  have hdet : ∀ τ, (mat (rmul x b) τ).det ≠ 0 := fun τ => (dom_of_orth X horth τ).1
  have hm : ∀ τ v, X.maj x τ v = ∑ a, ‖((mat (rmul x b) τ)⁻¹ *ᵥ v) a‖ ^ 2 :=
    fun τ v => (h τ).2 v
  obtain ⟨m0, hm0, hlow⟩ := posDef_int_lower
    (ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.Am_posDef (X := X) (mat (rmul x b)) hdet
      (ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings.zb (X := X)))

  have hQ : ∀ v ∈ X.Λ, v ≠ 0 → m0 ≤ ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 v) := by
    intro v hv hv0
    have e1 : ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 v) =
        ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.Qy X (mat (rmul x b)) v := by
      simp only [ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.Qy, hm]
    have hc : (ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings.zb (X := X)).repr ⟨v, hv⟩ ≠ 0 := by
      intro h0
      have h1 := (LinearEquiv.map_eq_zero_iff _).mp h0
      exact hv0 (by simpa using congrArg Subtype.val h1)
    have hx0 : (fun i => (ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings.zb (X := X)).repr ⟨v, hv⟩ i) ≠ 0 := by
      intro h0
      apply hc
      ext i
      exact congrFun h0 i
    have e2 := ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.quad_int (X := X) (mat (rmul x b))
      (ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings.zb (X := X))
      (fun i => (ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings.zb (X := X)).repr ⟨v, hv⟩ i)
    have e3 := ReciprocityTheory.ChartRestriction.G.FD.HermitianLatticeMaps.coe_expand (X := X)
      (ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings.zb (X := X)) ⟨v, hv⟩
    rw [e1]
    calc m0 ≤ _ := hlow _ hx0
      _ = _ := e2
      _ = ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.Qy X (mat (rmul x b)) v := by rw [← e3]
  have hS : m0 ≤ X.firstMinimumSq x := by
    unfold ReciprocityTheory.ChartRestriction.G.FD.Data.firstMinimumSq
    obtain ⟨v, hv, hv0⟩ := hne
    refine le_csInf ⟨_, v, hv, hv0, rfl⟩ ?_
    rintro t ⟨w, hw, hw0, rfl⟩
    exact hQ w hw hw0
  unfold ReciprocityTheory.ChartRestriction.G.FD.Data.la1
  exact Real.sqrt_pos.mpr (lt_of_lt_of_le hm0 hS)

theorem orthonormalize (X : Data E r) {p : Frame X.Ψ r} (hp : p ∈ X.dom) :
    ∃ b ∈ Bor X.Ψ r, IsOrth X (rmul p b) ∧ ∀ τ v, X.maj (rmul p b) τ v = X.maj p τ v := by
  obtain ⟨b, hb, h⟩ := ReciprocityTheory.ChartRestriction.G.FD.MajorantNormalForms.exists_normal_frame (X := X) hp
  have horth : IsOrth X (rmul p b) := fun τ => (h τ).1
  refine ⟨b, hb, horth, fun τ v => ?_⟩
  rw [maj_orth X horth, (h τ).2 v]

theorem maj_nonneg_orth (X : Data E r) {u : Frame X.Ψ r} (hu : IsOrth X u) (τ : X.Ψ) (v : Fin r → ℂ) :
    0 ≤ X.maj u τ v := by
  rw [maj_orth X hu]
  positivity

end ModeHalfC

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

namespace BigB

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem S_pos (X : Data E r) (Xa : ArchInM X) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    0 < ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 := by
  obtain ⟨k, hk⟩ := Xa.w_nz x hx
  have hd' : ∀ τ : X.Ψ, (mat x τ).det ≠ 0 ∧
      ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re := hx
  have hne : ∀ (τ : X.Ψ) (i : Fin (r + 1)), dmin X.Gm x τ i ≠ 0 := by
    intro τ i h0
    have h1 := (hd' τ).2 i
    rw [h0] at h1
    simp at h1
  have hp : 0 < X.pnorm Xa.L (Xa.w k) x := by
    unfold Data.pnorm
    apply mul_pos (norm_pos_iff.mpr hk)
    apply Finset.prod_pos
    intro τ _
    apply Finset.prod_pos
    intro i _
    apply Real.rpow_pos_of_pos
    exact norm_pos_iff.mpr (div_ne_zero (hne τ i.succ) (hne τ i.castSucc))
  calc (0 : ℝ) < X.pnorm Xa.L (Xa.w k) x ^ 2 := by positivity
    _ ≤ ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 :=
      Finset.single_le_sum (f := fun k => X.pnorm Xa.L (Xa.w k) x ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ k)

theorem pnorm_contOn (X : Data E r) (la : Wt X.Ψ r) {P : Frame X.Ψ r → ℂ} (hP : X.IsSec la P) :
    ContinuousOn (X.pnorm la P) X.dom := by
  have hd : ∀ (τ : X.Ψ) (i : Fin (r + 1)), Continuous fun x : Frame X.Ψ r => dmin X.Gm x τ i := by
    intro τ i
    unfold dmin lminor
    apply Continuous.matrix_det
    apply continuous_pi
    intro a
    apply continuous_pi
    intro b
    simp only [Matrix.submatrix_apply, gram, hermC, Matrix.of_apply, mat, col]
    fun_prop
  have hne : ∀ x ∈ X.dom, ∀ (τ : X.Ψ) (i : Fin (r + 1)), dmin X.Gm x τ i ≠ 0 := by
    intro x hx τ i h0
    have hd' : ∀ τ : X.Ψ, (mat x τ).det ≠ 0 ∧
        ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re := hx
    have h1 := (hd' τ).2 i
    rw [h0] at h1
    simp at h1
  unfold Data.pnorm
  apply ContinuousOn.mul
  · exact continuous_norm.comp_continuousOn hP.1.continuousOn
  · apply continuousOn_finsetProd
    intro τ _
    apply continuousOn_finsetProd
    intro i _
    apply ContinuousOn.rpow_const
    · exact (((hd τ i.succ).continuousOn).div (hd τ i.castSucc).continuousOn
        (fun x hx => hne x hx τ i.castSucc)).norm
    · intro x hx
      left
      exact norm_ne_zero_iff.mpr (div_ne_zero (hne x hx τ i.succ) (hne x hx τ i.castSucc))

theorem r_pos (X : Data E r) (Xa : ArchInM X) : 0 < r := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · exfalso
    subst hr
    have h := Xa.n_ge
    have h0 : nd X = 0 := by
      unfold nd
      rw [Fintype.card_eq_zero_iff]
      constructor
      rintro ⟨_, ⟨⟨a, _⟩, _⟩⟩
      exact a.elim0
    omega
  · exact hr

theorem lam_ne (X : Data E r) (Xa : ArchInM X) : ∃ v ∈ X.Λ, v ≠ 0 := by
  have hr := r_pos X Xa
  by_contra h
  push_neg at h
  have h1 : Submodule.span E (X.Λ : Set (Fin r → E)) ≤ ⊥ := by
    rw [Submodule.span_le]
    intro v hv
    simp [h v hv]
  rw [X.Λ_span, top_le_iff] at h1
  have hm : (fun _ => (1 : E) : Fin r → E) ∈ (⊤ : Submodule E (Fin r → E)) := Submodule.mem_top
  rw [← h1, Submodule.mem_bot] at hm
  exact one_ne_zero (congrFun hm ⟨0, hr⟩)

end BigB

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.IW

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
  Metric
open scoped ContDiff ENNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

def bmul (a b : Frame X.Ψ r) : Frame X.Ψ r := fun τ => (mat a τ * mat b τ : Matrix (Fin r) (Fin r) ℂ)

def binv (b : Frame X.Ψ r) : Frame X.Ψ r := fun τ => ((mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ)

theorem rmul_rmul (x a b : Frame X.Ψ r) : rmul (rmul x a) b = rmul x (bmul X a b) := by
  funext τ
  first
    | exact Matrix.mul_assoc (mat x τ) (mat a τ) (mat b τ)
    | (ext i j; simp [rmul, bmul, mat, Matrix.mul_assoc])

theorem bmul_mem {a b : Frame X.Ψ r} (ha : a ∈ Bor X.Ψ r) (hb : b ∈ Bor X.Ψ r) :
    bmul X a b ∈ Bor X.Ψ r := by
  simp only [Bor, Set.mem_setOf_eq] at ha hb ⊢
  intro τ
  obtain ⟨ha1, ha2⟩ := ha τ
  obtain ⟨hb1, hb2⟩ := hb τ
  have hA : Matrix.BlockTriangular (mat a τ) id := by
    intro i j h
    exact ha2 i j h
  have hB : Matrix.BlockTriangular (mat b τ) id := by
    intro i j h
    exact hb2 i j h
  refine ⟨?_, fun i j h => hA.mul hB h⟩
  show (mat a τ * mat b τ).det ≠ 0
  rw [Matrix.det_mul]
  exact mul_ne_zero ha1 hb1

theorem binv_mem {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) : binv X b ∈ Bor X.Ψ r := by
  simp only [Bor, Set.mem_setOf_eq] at hb ⊢
  intro τ
  obtain ⟨hb1, hb2⟩ := hb τ
  have hB : Matrix.BlockTriangular (mat b τ) id := by
    intro i j h
    exact hb2 i j h
  haveI : Invertible (mat b τ) := Matrix.invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr hb1)
  have hI : Matrix.BlockTriangular (mat b τ)⁻¹ id := Matrix.blockTriangular_inv_of_blockTriangular hB
  refine ⟨?_, fun i j h => hI h⟩
  show ((mat b τ)⁻¹).det ≠ 0
  exact (Matrix.isUnit_nonsing_inv_det _ (isUnit_iff_ne_zero.mpr hb1)).ne_zero

theorem rmul_binv (x : Frame X.Ψ r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) :
    rmul (rmul x b) (binv X b) = x := by
  simp only [Bor, Set.mem_setOf_eq] at hb
  funext τ
  have h := isUnit_iff_ne_zero.mpr (hb τ).1
  show mat x τ * mat b τ * (mat b τ)⁻¹ = x τ
  rw [Matrix.mul_nonsing_inv_cancel_right _ _ h]
  rfl

theorem lact_rmul (γ : GL (Fin r) E) (x b : Frame X.Ψ r) :
    lact γ (rmul x b) = rmul (lact γ x) b := by
  funext τ
  exact (Matrix.mul_assoc ((γ : Matrix (Fin r) (Fin r) E).map τ.1) (mat x τ) (mat b τ)).symm

theorem lact_lact (γ δ : GL (Fin r) E) (x : Frame X.Ψ r) : lact γ (lact δ x) = lact (γ * δ) x := by
  funext τ
  show (γ : Matrix (Fin r) (Fin r) E).map τ.1 * ((δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) =
    ((γ * δ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ
  rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]

theorem lact_inv (γ : GL (Fin r) E) (x : Frame X.Ψ r) : lact γ⁻¹ (lact γ x) = x := by
  rw [lact_lact, inv_mul_cancel]
  funext τ
  show ((1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ = x τ
  rw [Units.val_one, Matrix.map_one _ (map_zero τ.1) (map_one τ.1), Matrix.one_mul]
  try rfl

theorem avoid_base (Xa : ArchInM X) (Fl : FlatM X Xa) (j j' : Fin Fl.δ) {γ : GL (Fin r) E}
    (hγ : γ ∈ X.Γ) (hne : γ ≠ 1 ∨ j' ≠ j) (x0 b0 : Frame X.Ψ r) (hb0 : b0 ∈ Bor X.Ψ r)
    (hx : Fl.xs j = rmul x0 b0) (x1 b1 : Frame X.Ψ r) (hb1 : b1 ∈ Bor X.Ψ r)
    (hy : lact γ (Fl.xs j') = rmul x1 b1) (ε : ℝ)
    (hball : closedBall (0 : V (nd X)) (2 * ε) ⊆ OmF X x0)
    (hiso : ∀ y ∈ closedBall (0 : V (nd X)) (2 * ε), (∀ k, Fl.s k (cpt X x0 y) = 0) → y = 0)
    (hs1 : ∀ k, Fl.s k x1 = 0) :
    ∀ z ∈ closedBall (0 : V (nd X)) (2 * ε), ∀ b ∈ Bor X.Ψ r, x1 ≠ rmul (cpt X x0 z) b := by
  intro z hz b hb h1
  have hbc : ∀ c ∈ Bor X.Ψ r, bchar Xa.L c ≠ 0 := by
    intro c hc
    simp only [Bor, Set.mem_setOf_eq] at hc
    unfold bchar
    refine Finset.prod_ne_zero_iff.mpr fun τ _ =>
      Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ ?_
    obtain ⟨hd, ht⟩ := hc τ
    have hT : Matrix.BlockTriangular (mat c τ) id := by
      intro a e h
      exact ht a e h
    rw [Matrix.det_of_upperTriangular hT] at hd
    exact (Finset.prod_ne_zero_iff.mp hd) i (Finset.mem_univ _)
  have hzdom : cpt X x0 z ∈ X.dom := hball hz
  have hsz : ∀ k, Fl.s k (cpt X x0 z) = 0 := by
    intro k
    have hv := Fl.s_van k
    simp only [Data.SSgt, Data.SS, Data.IsBddSec, Data.IsSec, Set.mem_setOf_eq] at hv
    have hsec := hv.1.1.1.2.1 (cpt X x0 z) hzdom b hb
    have h0 := hs1 k
    rw [h1, hsec] at h0
    exact (mul_eq_zero.mp h0).resolve_left (hbc b hb)
  have hz0 : z = 0 := hiso z hz hsz
  have hc0 : cpt X x0 0 = x0 := by
    funext τ
    have hm : mat (nmat X 0) τ = 1 := by
      ext a e
      by_cases h : e < a
      · have hne : a ≠ e := ne_of_gt h
        simp only [mat, nmat, Matrix.of_apply, dif_pos h, Matrix.one_apply_ne hne]
        all_goals first | rfl | simp
      · simp only [mat, nmat, Matrix.of_apply, dif_neg h, Matrix.one_apply]
    show mat x0 τ * mat (nmat X 0) τ = x0 τ
    rw [hm, Matrix.mul_one]
    rfl
  have hx0 : rmul (Fl.xs j) (binv X b0) = x0 := by
    rw [hx]
    exact rmul_binv X x0 hb0
  have hcB : bmul X (binv X b0) (bmul X b b1) ∈ Bor X.Ψ r :=
    bmul_mem X (binv_mem X hb0) (bmul_mem X hb hb1)
  have hy' : lact γ (Fl.xs j') = rmul (Fl.xs j) (bmul X (binv X b0) (bmul X b b1)) := by
    rw [hy, h1, hz0, hc0, ← hx0, rmul_rmul X, rmul_rmul X]
  have hj := congrArg (lact γ⁻¹) hy'
  rw [lact_inv] at hj
  have hjj : j = j' := Fl.xs_inj j j' γ⁻¹ (X.Γ.inv_mem hγ) _ hcB hj
  subst hjj
  have hγ1 : γ = 1 := X.Γ_free γ hγ (Fl.xs j) (Fl.xs_mem j) _ hcB hy'
  rcases hne with h | h
  · exact h hγ1
  · exact h rfl

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.IW
end

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates
open scoped ContDiff ENNReal

noncomputable section

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
  {E : Type} [Field E] [NumberField E] [IsCMField E]

def BasePotentialExistence {r : ℕ} (X : FD.Data E r) (de : Wt X.Ψ r) (rr a1 : ℝ) : Prop :=
  ∃ ps0 : Frame X.Ψ r → ℝ, IsInvFn X ps0 ∧
    (∀ x0 ∈ X.dom, ContDiffOn ℝ ∞ (fun z => ps0 (cpt X x0 z)) {z | cpt X x0 z ∈ X.dom}) ∧
    (∀ x0 ∈ X.dom, ∀ z, cpt X x0 z ∈ X.dom → ∀ ξ : Fin (nd X) → ℂ,
      -(rr / 2 * leviM X (phla X de) x0 z ξ) ≤ leviM X ps0 x0 z ξ) ∧
    cfwM X ps0 a1

def InterpolationModelInequalities {r : ℕ} (X : FD.Data E r) {N : ℕ} (L eW : Wt X.Ψ r) (w : Fin N → Frame X.Ψ r → ℂ)
    (et : Frame X.Ψ r → ℂ) (c i : ℝ) (ph : Frame X.Ψ r → ℝ) : Prop :=
  (∃ K : ℝ, ∀ x ∈ X.dom, Real.exp (-(2 * c * ph x)) ≤ K * ∑ k, X.pnorm L (w k) x ^ 2) ∧
  ∃ K : ℝ, ∀ x ∈ X.dom, X.pnorm eW et x ^ 2 ≤ K * Real.exp (-(2 * i * ph x))

def IsDominantR {r : ℕ} (X : FD.Data E r) (v : X.Ψ → Fin r → ℝ) : Prop :=
  ∀ τ : X.Ψ, (∀ i j : Fin r, i ≤ j → (j : ℕ) < X.p0 → v τ j ≤ v τ i) ∧
    (∀ i j : Fin r, X.p0 ≤ (i : ℕ) → i ≤ j → v τ j ≤ v τ i) ∧
    (∀ i j : Fin r, (i : ℕ) < X.p0 → X.p0 ≤ (j : ℕ) → v τ i ≤ v τ j)

def CurvNumStatement : Prop :=
  ∀ (r : ℕ) (X : FD.Data E r) (L de Fp : Wt X.Ψ r) (T rr η : ℝ), 0 < η → 0 < rr → 0 ≤ T →
    IsStrictDom X L → IsStrictDom X (2 • L - de) →
    (∀ t ∈ ({0, 2 * T / rr} : Set ℝ), IsDominantR X fun τ a =>
      ((Fp - kapW X - nd X • L) τ a : ℝ) - t * (rr / 2) * (de τ a : ℝ) - 2 * η * (L τ a : ℝ)) →
    (∀ x0 ∈ X.dom, ∀ z, cpt X x0 z ∈ X.dom → ∀ ξ : Fin (nd X) → ℂ, ξ ≠ 0 →
      0 < leviM X (phla X L) x0 z ξ) ∧
    (∀ x0 ∈ X.dom, ∀ z, cpt X x0 z ∈ X.dom → ∀ ξ : Fin (nd X) → ℂ, ξ ≠ 0 →
      0 < leviM X (phla X (2 • L - de)) x0 z ξ) ∧
    ∀ t : ℝ, 0 ≤ t → t * rr ≤ 2 * T → ∀ x0 ∈ X.dom, ∀ z, cpt X x0 z ∈ X.dom → ∀ ξ : Fin (nd X) → ℂ,
      2 * η * leviM X (phla X L) x0 z ξ ≤
        leviM X (phla X (Fp - kapW X - nd X • L)) x0 z ξ - t * (rr / 2) * leviM X (phla X de) x0 z ξ

def de2W {r : ℕ} (X : FD.Data E r) : Wt X.Ψ r := fun _ j => if X.p0 ≤ (j : ℕ) then 1 else -1

end

end ReciprocityTheory.ChartRestriction.G.AR.Up
end
