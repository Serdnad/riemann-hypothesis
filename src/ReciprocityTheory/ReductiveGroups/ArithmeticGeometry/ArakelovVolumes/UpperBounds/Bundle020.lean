module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfD
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle009
import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.MeasurableEmbeddingRotAbout
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle014

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.LUB

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal ContDiff

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
  {x1' : Frame X.Ψ r} (b1 : Frame X.Ψ r) (D : ExtFPf.LUData X x1')

def uL (x1' b1 x : Frame X.Ψ r) : Frame X.Ψ r := fun τ =>
  (mat x1' τ * (mat b1 τ)⁻¹ * (mat x1' τ)⁻¹ * mat x τ : Matrix (Fin r) (Fin r) ℂ)

def vL (x1' b1 x : Frame X.Ψ r) : Frame X.Ψ r := fun τ =>
  (mat x1' τ * mat b1 τ * (mat x1' τ)⁻¹ * mat x τ : Matrix (Fin r) (Fin r) ℂ)

theorem cont_uL : Continuous (uL X x1' b1) := by
  unfold uL
  exact continuous_pi fun τ => Continuous.matrix_mul continuous_const (continuous_apply τ)

variable {X b1}

theorem mat_uL (x : Frame X.Ψ r) (τ : X.Ψ) :
    mat (uL X x1' b1 x) τ = mat x1' τ * (mat b1 τ)⁻¹ * (mat x1' τ)⁻¹ * mat x τ := rfl

private lemma det_mat_ne_zero_of_isOrth {x : Frame X.Ψ r} (ho : IsOrth X x) (τ : X.Ψ) : (mat x τ).det ≠ 0 := by
  intro h0
  have hg := ho τ
  have e : gram τ.1 X.Gm (mat x τ) =
      (mat x τ).transpose * X.Gm.map τ.1 * (mat x τ).map (starRingEnd ℂ) := by
    ext a b
    simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hd := congrArg Matrix.det hg
  rw [e, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul,
    Matrix.det_diagonal] at hd
  refine (Finset.prod_ne_zero_iff.mpr fun a _ => ?_) hd.symm
  unfold sgn
  split_ifs <;> norm_num

theorem uL_cpt (ho' : IsOrth X x1') (hb1 : b1 ∈ Bor X.Ψ r) (z : V (nd X)) (b : Frame X.Ψ r) :
    uL X x1' b1 (rmul (cpt X (rmul x1' b1) z) b) = rmul (cpt X x1' z) b := by
  funext τ
  have hA := isUnit_iff_ne_zero.mpr (det_mat_ne_zero_of_isOrth ho' τ)
  have hB := isUnit_iff_ne_zero.mpr (hb1 τ).1
  have e : ∀ x b : Frame X.Ψ r, mat (rmul x b) τ = mat x τ * mat b τ := fun _ _ => rfl
  show mat (uL X x1' b1 (rmul (cpt X (rmul x1' b1) z) b)) τ = mat (rmul (cpt X x1' z) b) τ
  rw [mat_uL]
  simp only [cpt, e, Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul_cancel_left _ _ hA, Matrix.nonsing_inv_mul_cancel_left _ _ hB]

theorem vL_uL (ho' : IsOrth X x1') (hb1 : b1 ∈ Bor X.Ψ r) (x : Frame X.Ψ r) :
    vL X x1' b1 (uL X x1' b1 x) = x := by
  funext τ
  have hA := isUnit_iff_ne_zero.mpr (det_mat_ne_zero_of_isOrth ho' τ)
  have hB := isUnit_iff_ne_zero.mpr (hb1 τ).1
  have e : ∀ y : Frame X.Ψ r,
      mat (vL X x1' b1 y) τ = mat x1' τ * mat b1 τ * (mat x1' τ)⁻¹ * mat y τ := fun _ => rfl
  show mat (vL X x1' b1 (uL X x1' b1 x)) τ = mat x τ
  rw [e, mat_uL]
  simp only [Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul_cancel_left _ _ hA, Matrix.mul_nonsing_inv_cancel_left _ _ hB,
    Matrix.mul_nonsing_inv_cancel_left _ _ hA]

theorem vL_cpt (ho' : IsOrth X x1') (z : V (nd X)) (b : Frame X.Ψ r) :
    vL X x1' b1 (rmul (cpt X x1' z) b) = rmul (cpt X (rmul x1' b1) z) b := by
  funext τ
  have hA := isUnit_iff_ne_zero.mpr (det_mat_ne_zero_of_isOrth ho' τ)
  have e : ∀ x b : Frame X.Ψ r, mat (rmul x b) τ = mat x τ * mat b τ := fun _ _ => rfl
  have e2 : ∀ y : Frame X.Ψ r,
      mat (vL X x1' b1 y) τ = mat x1' τ * mat b1 τ * (mat x1' τ)⁻¹ * mat y τ := fun _ => rfl
  show mat (vL X x1' b1 (rmul (cpt X x1' z) b)) τ = mat (rmul (cpt X (rmul x1' b1) z) b) τ
  rw [e2]
  simp only [cpt, e, Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul_cancel_left _ _ hA]

theorem Tset_eq_pre (ho' : IsOrth X x1') (hb1 : b1 ∈ Bor X.Ψ r) {ρ : ℝ}
    (hO : Metric.ball (0 : V (nd X)) ρ ⊆ OmF X x1') :
    Tset X (rmul x1' b1) ρ = uL X x1' b1 ⁻¹' (ExtFPf.cell D ∩ D.zOf ⁻¹' Metric.ball 0 ρ) := by
  ext x
  constructor
  · rintro ⟨⟨z, b⟩, ⟨hz, hb⟩, rfl⟩
    simp only [Set.mem_preimage, Set.mem_inter_iff]
    rw [uL_cpt ho' hb1]
    obtain ⟨hΔ, hzz, -⟩ := D.uniq z (hO hz) b hb
    exact ⟨⟨OntoS.dom_rmul X (hO hz) hb, hΔ⟩, by rw [hzz]; exact hz⟩
  · rintro ⟨hcell, hzb⟩
    obtain ⟨-, hbm, e⟩ := D.split _ hcell.1 hcell.2
    refine ⟨⟨D.zOf (uL X x1' b1 x), D.bOf (uL X x1' b1 x)⟩, ⟨hzb, hbm⟩, ?_⟩
    simp only
    rw [← vL_cpt (b1 := b1) ho', ← e, vL_uL ho' hb1]

include D in
theorem isOpen_Tset (ho' : IsOrth X x1') (hb1 : b1 ∈ Bor X.Ψ r) {ρ : ℝ}
    (hO : Metric.ball (0 : V (nd X)) ρ ⊆ OmF X x1') : IsOpen (Tset X (rmul x1' b1) ρ) := by
  rw [Tset_eq_pre D ho' hb1 hO]
  exact (D.hz.continuousOn.isOpen_inter_preimage (ExtFPf.isOpen_cell D) Metric.isOpen_ball).preimage
    (cont_uL X b1)

private lemma lact_lact_eq_lact_mul (γ δ : GL (Fin r) E) (x : Frame X.Ψ r) :
    lact γ (lact δ x) = lact (γ * δ) x := by
  funext τ
  show (γ : Matrix (Fin r) (Fin r) E).map τ.1 * ((δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) =
    ((γ * δ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ
  rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]

private lemma lact_one_upper_bounds (x : Frame X.Ψ r) : lact (1 : GL (Fin r) E) x = x := by
  funext τ
  show ((1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ = mat x τ
  rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]

theorem sat_eq (x1 : Frame X.Ψ r) (ρ : ℝ) :
    {x | ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z' ∈ Metric.ball (0 : V (nd X)) ρ, x = lact γ (rmul (cpt X x1 z') b)} =
      ⋃ γ : X.Γ, lact γ.1⁻¹ ⁻¹' Tset X x1 ρ := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_preimage, Tset, Set.mem_image, Set.mem_prod,
    Prod.exists]
  constructor
  · rintro ⟨γ, hγ, b, hb, z', hz', rfl⟩
    refine ⟨⟨γ, hγ⟩, z', b, ⟨hz', hb⟩, ?_⟩
    show _ = lact γ⁻¹ (lact γ _)
    rw [lact_lact_eq_lact_mul, inv_mul_cancel, lact_one_upper_bounds]
  · rintro ⟨⟨γ, hγ⟩, z', b, ⟨hz', hb⟩, h⟩
    refine ⟨γ, hγ, b, hb, z', hz', ?_⟩
    have h' : lact γ (lact γ⁻¹ x) = lact γ (rmul (cpt X x1 z') b) := by
      rw [← h]
    rw [lact_lact_eq_lact_mul, mul_inv_cancel, lact_one_upper_bounds] at h'
    exact h'

include D in
theorem isOpen_sat (ho' : IsOrth X x1') (hb1 : b1 ∈ Bor X.Ψ r) {ρ : ℝ}
    (hO : Metric.ball (0 : V (nd X)) ρ ⊆ OmF X x1') :
    IsOpen {x | ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z' ∈ Metric.ball (0 : V (nd X)) ρ,
      x = lact γ (rmul (cpt X (rmul x1' b1) z') b)} := by
  rw [sat_eq]
  refine isOpen_iUnion fun γ => ?_
  have hc : Continuous (fun x : Frame X.Ψ r => lact γ.1⁻¹ x) :=
    continuous_pi fun τ => Continuous.matrix_mul continuous_const (continuous_apply τ)
  exact (isOpen_Tset D ho' hb1 hO).preimage hc

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.LUB
end

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ENNReal Matrix ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def idF (X : Data E r) : Frame X.Ψ r := fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)

theorem idF_mem (X : Data E r) : idF X ∈ Bor X.Ψ r := by
  simp only [Bor, Set.mem_setOf_eq]
  intro τ
  refine ⟨?_, fun a c h => ?_⟩
  · have h1 : mat (idF X) τ = 1 := by
      ext i j
      rfl
    rw [h1, Matrix.det_one]
    exact one_ne_zero
  · simp [idF, Matrix.one_apply, ne_of_gt h]

theorem rmul_idF (X : Data E r) (y : Frame X.Ψ r) : rmul y (idF X) = y := by
  funext τ
  show (mat y τ * mat (idF X) τ : Matrix (Fin r) (Fin r) ℂ) = y τ
  have h1 : mat (idF X) τ = 1 := by
    ext i j
    rfl
  rw [h1, mul_one]
  rfl

theorem bchar_idF (X : Data E r) (la : Wt X.Ψ r) : bchar la (idF X) = 1 := by
  simp [bchar, idF]

theorem bchar_contAt (X : Data E r) (la : Wt X.Ψ r) : ContinuousAt (bchar la) (idF X) := by
  unfold bchar
  refine tendsto_finsetProd _ fun τ _ => tendsto_finsetProd _ fun i _ => ?_
  have hc : Continuous fun b : Frame X.Ψ r => b τ i i := by fun_prop
  exact hc.continuousAt.zpow₀ _ (Or.inl (by simp [idF]))

theorem ball_int_bound (X : Data E r) (la : Wt X.Ψ r) {R0 ρ : ℝ}
    (hgood : ∀ w ∈ Metric.ball (0 : V (nd X)) R0, (∀ τ, (mat (nmat X w) τ).det ≠ 0) ∧
      (∀ τ, ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (lminor (Gw X w τ) i).re) ∧ 1 / 2 < nfw X la w)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) (hxo : IsOrth X x) (P : Frame X.Ψ r → ℂ) :
    Metric.ball (0 : V (nd X)) (min R0 ρ) ⊆ Bset X x ρ ∧
      ∫⁻ z in Metric.ball (0 : V (nd X)) (min R0 ρ), ‖P (cpt X x z)‖ₑ ^ 2 ≤ ENNReal.ofReal 4 *
        ∫⁻ w in Bset X x ρ, ‖P (cpt X x w)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-phla X la (cpt X x w))) := by
  have hgoodR := fun w (hw : w ∈ Metric.ball (0 : V (nd X)) (min R0 ρ)) =>
    hgood w (Metric.ball_subset_ball (min_le_left _ _) hw)
  have hmem : Metric.ball (0 : V (nd X)) (min R0 ρ) ⊆ Bset X x ρ := fun w hw => by
    obtain ⟨h1, h2, -⟩ := hgoodR w hw
    exact ⟨lt_of_lt_of_le (mem_ball_zero_iff.1 hw) (min_le_right _ _), cpt_mem_dom X hx hxo h1 h2⟩
  refine ⟨hmem, ?_⟩
  have hpt : ∀ w ∈ Metric.ball (0 : V (nd X)) (min R0 ρ), ‖P (cpt X x w)‖ₑ ^ 2 ≤ ENNReal.ofReal 4 *
      (‖P (cpt X x w)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-phla X la (cpt X x w)))) := by
    intro w hw
    obtain ⟨-, -, h3⟩ := hgoodR w hw
    have hn : X.nfac la (cpt X x w) = nfw X la w := nfac_cpt_orth X la hxo w
    have he : 1 ≤ ENNReal.ofReal 4 * ENNReal.ofReal (Real.exp (-phla X la (cpt X x w))) := by
      rw [exp_neg_phla X la (by rw [hn]; linarith), hn, ← ENNReal.ofReal_mul (by norm_num),
        ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (by nlinarith)
    calc ‖P (cpt X x w)‖ₑ ^ 2 = ‖P (cpt X x w)‖ₑ ^ 2 * 1 := (mul_one _).symm
      _ ≤ ‖P (cpt X x w)‖ₑ ^ 2 *
          (ENNReal.ofReal 4 * ENNReal.ofReal (Real.exp (-phla X la (cpt X x w)))) := by gcongr
      _ = _ := by ring
  calc ∫⁻ z in Metric.ball (0 : V (nd X)) (min R0 ρ), ‖P (cpt X x z)‖ₑ ^ 2
      ≤ ∫⁻ z in Metric.ball (0 : V (nd X)) (min R0 ρ), ENNReal.ofReal 4 *
          (‖P (cpt X x z)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-phla X la (cpt X x z)))) :=
        setLIntegral_mono' Metric.isOpen_ball.measurableSet hpt
    _ = ENNReal.ofReal 4 * ∫⁻ z in Metric.ball (0 : V (nd X)) (min R0 ρ),
          ‖P (cpt X x z)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-phla X la (cpt X x z))) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := mul_le_mul_of_nonneg_left (lintegral_mono_set hmem) zero_le

theorem subMeanLoc_of (hLU : LUStatement (E := E)) : SubMeanLocStatement (E := E) := by
  intro r X la ρ hρ hρ1 x hx hxo
  obtain ⟨R0, hR0, hgood⟩ := good_ball X la
  have hR : 0 < min R0 ρ := lt_min hR0 hρ
  obtain ⟨Δ, zOf, bOf, hΔ, -, hz, hb, hdec, hinv⟩ := hLU r X x hxo
  have hx0 : (0 : V (nd X)) ∈ OmF X x := by
    show cpt X x 0 ∈ X.dom
    rw [cpt_zero]; exact hx
  obtain ⟨hΔx, hzx, hbx⟩ := hinv 0 hx0 (idF X) (idF_mem X)
  rw [rmul_idF, cpt_zero] at hΔx hzx hbx
  have hOo : IsOpen {y | y ∈ X.dom ∧ Δ y ≠ 0} :=
    (isOpenDom X).inter (isOpen_ne_fun hΔ.continuous continuous_const)
  have hxO : x ∈ {y | y ∈ X.dom ∧ Δ y ≠ 0} := ⟨hx, hΔx⟩
  have hzc : ContinuousAt zOf x := hz.continuousOn.continuousAt (hOo.mem_nhds hxO)
  have hbc : ContinuousAt (fun y => bchar la (bOf y)) x := by
    have h := bchar_contAt X la
    rw [← hbx] at h
    exact h.comp (hb.continuousOn.continuousAt (hOo.mem_nhds hxO))
  have e1 : ∀ᶠ y in 𝓝 x, y ∈ {y | y ∈ X.dom ∧ Δ y ≠ 0} := hOo.mem_nhds hxO
  have e2 : ∀ᶠ y in 𝓝 x, ‖zOf y‖ < min R0 ρ / 2 :=
    hzc.norm.eventually_lt continuousAt_const (by rw [hzx, norm_zero]; positivity)
  have e3 : ∀ᶠ y in 𝓝 x, ‖bchar la (bOf y)‖ < 2 :=
    hbc.norm.eventually_lt continuousAt_const (by rw [hbx, bchar_idF, norm_one]; norm_num)
  obtain ⟨ε, hε, hall⟩ := Metric.eventually_nhds_iff_ball.1 (e1.and (e2.and e3))
  set v := volume (Metric.ball (0 : V (nd X)) (min R0 ρ / 2)) with hv
  have hvpos : v ≠ 0 := (Metric.measure_ball_pos volume _ (by positivity)).ne'
  have hvtop : v ≠ ⊤ := measure_ball_lt_top.ne
  refine ⟨ε, hε, ENNReal.ofReal 4 * v⁻¹ * ENNReal.ofReal 4,
    ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.inv_lt_top.2 (pos_iff_ne_zero.2 hvpos))) ENNReal.ofReal_lt_top, fun P hP y hy => ?_⟩
  obtain ⟨⟨hyd, hΔy⟩, hzy, hby⟩ := hall y hy
  obtain ⟨hzO, hbB, hyeq⟩ := hdec y hyd hΔy
  have hPy : P y = bchar la (bOf y) * P (cpt X x (zOf y)) := by
    conv_lhs => rw [hyeq]
    exact hP.2 _ hzO _ hbB
  have hsub : Metric.ball (zOf y) (min R0 ρ / 2) ⊆ Metric.ball (0 : V (nd X)) (min R0 ρ) := by
    intro w hw
    rw [mem_ball_zero_iff]
    rw [Metric.mem_ball, dist_eq_norm] at hw
    calc ‖w‖ = ‖(w - zOf y) + zOf y‖ := by rw [sub_add_cancel]
      _ ≤ ‖w - zOf y‖ + ‖zOf y‖ := norm_add_le _ _
      _ < min R0 ρ / 2 + min R0 ρ / 2 := add_lt_add hw hzy
      _ = min R0 ρ := by ring
  obtain ⟨hmemB, hint⟩ := ball_int_bound X la hgood hx hxo P
  have hu : DifferentiableOn ℂ (fun w => P (cpt X x w)) (Metric.ball (zOf y) (min R0 ρ / 2)) :=
    hP.1.comp (diff_cpt X x).differentiableOn fun w hw => (hmemB (hsub hw)).2
  have hmv := ReciprocityTheory.L2DbarEstimates.C.mv (nd X) (zOf y) (min R0 ρ / 2) (fun w => P (cpt X x w)) (fun _ => 1)
    hu measurable_const
  simp only [mul_one, one_mul, lintegral_const, Measure.restrict_apply_univ] at hmv
  rw [Measure.addHaar_ball_center] at hmv
  have hle : ‖P (cpt X x (zOf y))‖ₑ ^ 2 ≤
      v⁻¹ * ∫⁻ w in Metric.ball (zOf y) (min R0 ρ / 2), ‖P (cpt X x w)‖ₑ ^ 2 := by
    rw [← ENNReal.div_eq_inv_mul, ENNReal.le_div_iff_mul_le (Or.inl hvpos) (Or.inl hvtop)]
    exact hmv
  have hbb : ‖bchar la (bOf y)‖ₑ ^ 2 ≤ ENNReal.ofReal 4 := by
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [norm_nonneg (bchar la (bOf y))])
  calc ‖P y‖ₑ ^ 2 = ‖bchar la (bOf y)‖ₑ ^ 2 * ‖P (cpt X x (zOf y))‖ₑ ^ 2 := by
        rw [hPy, enorm_mul, mul_pow]
    _ ≤ ENNReal.ofReal 4 * (v⁻¹ * (ENNReal.ofReal 4 * ∫⁻ w in Bset X x ρ,
          ‖P (cpt X x w)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-phla X la (cpt X x w))))) := by
        refine mul_le_mul' hbb (hle.trans (mul_le_mul_of_nonneg_left ?_ zero_le))
        exact (lintegral_mono_set hsub).trans hint
    _ = _ := by ring

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
end
