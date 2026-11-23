module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPfA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle023
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfK
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoWeightStatementPfC
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoWeightStatementPfA

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OW

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter Metric
open scoped ContDiff ENNReal

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

def SatB (X : Data E r) (x1 : Frame X.Ψ r) (ρ : ℝ) : Set (Frame X.Ψ r) :=
  {x | ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z' ∈ ball (0 : V (nd X)) ρ, x = lact γ (rmul (cpt X x1 z') b)}

theorem satB_sat (x1 : Frame X.Ψ r) (ρ : ℝ) {x : Frame X.Ψ r} (hx : x ∈ SatB X x1 ρ) {γ : GL (Fin r) E}
    (hγ : γ ∈ X.Γ) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) : lact γ (rmul x b) ∈ SatB X x1 ρ := by
  obtain ⟨γ', hγ', b', hb', z', hz', rfl⟩ := hx
  refine ⟨γ * γ', X.Γ.mul_mem hγ hγ', rmul b' b,
    ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.mul_mem (X := X) hb' hb, z', hz', ?_⟩
  rw [← ReciprocityTheory.ChartRestriction.G.AR.Up.IW.lact_rmul, ReciprocityTheory.ChartRestriction.G.AR.Up.IW.lact_lact,
    ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.rmul_assoc]

theorem mem_satB_self (x1 : Frame X.Ψ r) {ρ : ℝ} (hρ : 0 < ρ) : x1 ∈ SatB X x1 ρ := by
  have hn : nmat X 0 = fun _ => (1 : Matrix (Fin r) (Fin r) ℂ) := by
    funext τ a c
    simp only [nmat]
    split_ifs with h1 h2
    · rw [Matrix.one_apply_ne (ne_of_lt h1).symm]
      first | rfl | simp | exact PiLp.zero_apply _ _
    · subst h2; exact (Matrix.one_apply_eq a).symm
    · exact (Matrix.one_apply_ne h2).symm
  refine ⟨1, X.Γ.one_mem, fun _ => (1 : Matrix (Fin r) (Fin r) ℂ), ?_, 0, Metric.mem_ball_self hρ, ?_⟩
  · intro τ
    refine ⟨?_, fun a c hca => ?_⟩
    · show Matrix.det (1 : Matrix (Fin r) (Fin r) ℂ) ≠ 0
      simp
    · show (1 : Matrix (Fin r) (Fin r) ℂ) a c = 0
      exact Matrix.one_apply_ne (ne_of_lt hca).symm
  · funext τ a c
    simp [lact, rmul, mat, cpt, hn]
    change x1 τ a c = ((Matrix.of (x1 τ) * (1 : Matrix (Fin r) (Fin r) ℂ)) *
      (1 : Matrix (Fin r) (Fin r) ℂ)) a c
    rw [Matrix.mul_one, Matrix.mul_one]
    rfl

theorem rpow_ofReal_ne_top {a : ℝ} (ha : 0 < a) (y : ℝ) : ENNReal.ofReal a ^ y ≠ ⊤ := by
  rw [ENNReal.ofReal_rpow_of_pos ha]
  exact ENNReal.ofReal_ne_top

theorem inFF_of (hLU : LocalUnfoldBStatement (E := E)) {Xa : ArchInM X} (Fl : FlatM X Xa) (hPD : PropDisc X)
    (x0 : Frame X.Ψ r) (hx0 : IsOrth X x0) (FF : Set (V (nd X))) (hFF : IsFundSet X x0 FF)
    (g : Frame X.Ψ r → ℂ) (hg : g ∈ X.SS (Xa.Fp + Xa.T • Xa.L))
    (hint : ∫⁻ z in FF, ENNReal.ofReal (X.pnorm (Xa.Fp + Xa.T • Xa.L) g (cpt X x0 z) ^ 2 *
          (∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2) ^ (-(Xa.T : ℝ))) ∂muF X x0 < ⊤)
    (hv : VanS X Fl.xs Fl.s (Xa.T - nd X) g) : InFF X x0 (WSk X Xa Fl) FF g := by
  have hsec : X.IsSec (Xa.Fp + Xa.T • Xa.L) g := hg.1.1
  have hGm := Gf_meas Xa Fl hsec.1.continuousOn
  have key : ∀ j, ∃ ρ : ℝ, 0 < ρ ∧ IsOpen (SatB X (Fl.xs j) ρ) ∧
      ∫⁻ z in FF ∩ {z | ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z' ∈ ball (0 : V (nd X)) ρ,
        cpt X x0 z = lact γ (rmul (cpt X (Fl.xs j) z') b)}, Gf Xa Fl g (cpt X x0 z) ∂muF X x0 < ⊤ := by
    intro j
    obtain ⟨ρV, hρV, hV⟩ := hv j
    obtain ⟨ρ0, hρ0, hL⟩ := hLU r X x0 hx0 hPD FF hFF (Fl.xs j) (Fl.xs_mem j)
    have h0 : (0 : V (nd X)) ∈ OmF X (Fl.xs j) := by
      show cpt X (Fl.xs j) 0 ∈ X.dom
      rw [IW.cpt_zero]
      exact Fl.xs_mem j
    obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.1 (ExF.isOpen_OmF X (Fl.xs j)) 0 h0
    set ρ := min (min ρV ρ0) (ε / 2) with hρdef
    have hρ : 0 < ρ := lt_min (lt_min hρV hρ0) (by linarith)
    have hρV' : ρ ≤ ρV := (min_le_left _ _).trans (min_le_left _ _)
    have hρ0' : ρ ≤ ρ0 := (min_le_left _ _).trans (min_le_right _ _)
    have hcl : closedBall (0 : V (nd X)) ρ ⊆ OmF X (Fl.xs j) :=
      (closedBall_subset_ball (lt_of_le_of_lt (min_le_right _ _) (by linarith))).trans hεsub
    obtain ⟨hop, K, hK, hb⟩ := hL ρ hρ hρ0'
    refine ⟨ρ, hρ, hop, ?_⟩
    calc _ ≤ K * ∫⁻ z in ball (0 : V (nd X)) ρ, Gf Xa Fl g (cpt X (Fl.xs j) z) :=
          hb _ hGm (fun x hx b hb => Gf_rmul Xa Fl hsec hx hb) (fun γ hγ x hx => Gf_lact Xa Fl hsec hγ hx)
      _ < ⊤ := ENNReal.mul_lt_top hK (ball_finite Fl g j hρ hρV' hV hcl)
  choose ρ hρ hop hfin using key
  set U := ⋃ j, SatB X (Fl.xs j) (ρ j) with hUdef
  have hU : IsOpen U := isOpen_iUnion hop
  have hxs : ∀ j, Fl.xs j ∈ U := fun j => Set.mem_iUnion.2 ⟨j, mem_satB_self _ (hρ j)⟩
  have hsat : ∀ x ∈ U, ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, lact γ (rmul x b) ∈ U := by
    intro x hx γ hγ b hb
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hx
    exact Set.mem_iUnion.2 ⟨j, satB_sat _ _ hj hγ hb⟩
  obtain ⟨K, hK⟩ := Fl.family_le_coords U hU hxs hsat
  set P := {z : V (nd X) | cpt X x0 z ∈ U} with hPdef
  have hPm : MeasurableSet P := ((IW.cpt_diff X x0).continuous.isOpen_preimage _ hU).measurableSet
  set C := ENNReal.ofReal (1 / (max K 0 + 1)) ^ (-((Xa.T : ℝ) - 1 / 2)) with hCdef
  have hC : C ≠ ⊤ := rpow_ofReal_ne_top (by positivity) _
  have hoff : ∫⁻ z in FF \ P, Gf Xa Fl g (cpt X x0 z) ∂muF X x0 < ⊤ := by
    calc ∫⁻ z in FF \ P, Gf Xa Fl g (cpt X x0 z) ∂muF X x0
        ≤ ∫⁻ z in FF \ P, C * ENNReal.ofReal (X.pnorm (Xa.Fp + Xa.T • Xa.L) g (cpt X x0 z) ^ 2 *
          (∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2) ^ (-(Xa.T : ℝ))) ∂muF X x0 := by
          refine setLIntegral_mono' (hFF.1.diff hPm) fun z hz => ?_
          have hzd : cpt X x0 z ∈ X.dom := hFF.2.1 hz.1
          exact Gf_le_off Xa Fl g K hzd (hK _ hzd hz.2)
      _ ≤ ∫⁻ z in FF, C * ENNReal.ofReal (X.pnorm (Xa.Fp + Xa.T • Xa.L) g (cpt X x0 z) ^ 2 *
          (∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2) ^ (-(Xa.T : ℝ))) ∂muF X x0 :=
          lintegral_mono_set Set.diff_subset
      _ = C * ∫⁻ z in FF, ENNReal.ofReal (X.pnorm (Xa.Fp + Xa.T • Xa.L) g (cpt X x0 z) ^ 2 *
          (∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2) ^ (-(Xa.T : ℝ))) ∂muF X x0 :=
          lintegral_const_mul' _ _ hC
      _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hC) hint
  have hcover : FF ⊆ (FF \ P) ∪ ⋃ j, FF ∩ {z | ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r,
      ∃ z' ∈ ball (0 : V (nd X)) (ρ j), cpt X x0 z = lact γ (rmul (cpt X (Fl.xs j) z') b)} := by
    intro z hz
    by_cases hzP : z ∈ P
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hzP
      exact Or.inr (Set.mem_iUnion.2 ⟨j, hz, hj⟩)
    · exact Or.inl ⟨hz, hzP⟩
  show ∫⁻ z in FF, Gf Xa Fl g (cpt X x0 z) ∂muF X x0 < ⊤
  calc ∫⁻ z in FF, Gf Xa Fl g (cpt X x0 z) ∂muF X x0
      ≤ ∫⁻ z in (FF \ P) ∪ ⋃ j, FF ∩ {z | ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r,
          ∃ z' ∈ ball (0 : V (nd X)) (ρ j), cpt X x0 z = lact γ (rmul (cpt X (Fl.xs j) z') b)},
          Gf Xa Fl g (cpt X x0 z) ∂muF X x0 := lintegral_mono_set hcover
    _ ≤ ∫⁻ z in FF \ P, Gf Xa Fl g (cpt X x0 z) ∂muF X x0 + ∫⁻ z in ⋃ j, FF ∩ {z | ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r,
          ∃ z' ∈ ball (0 : V (nd X)) (ρ j), cpt X x0 z = lact γ (rmul (cpt X (Fl.xs j) z') b)},
          Gf Xa Fl g (cpt X x0 z) ∂muF X x0 := lintegral_union_le _ _ _
    _ ≤ ∫⁻ z in FF \ P, Gf Xa Fl g (cpt X x0 z) ∂muF X x0 + ∑' j, ∫⁻ z in FF ∩ {z | ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r,
          ∃ z' ∈ ball (0 : V (nd X)) (ρ j), cpt X x0 z = lact γ (rmul (cpt X (Fl.xs j) z') b)},
          Gf Xa Fl g (cpt X x0 z) ∂muF X x0 := add_le_add le_rfl (lintegral_iUnion_le _ _)
    _ < ⊤ := by
      rw [tsum_fintype]
      exact ENNReal.add_lt_top.2 ⟨hoff, ENNReal.sum_lt_top.2 fun j _ => hfin j⟩

theorem ontoWeight_of (hLU : LocalUnfoldBStatement (E := E)) : OntoWeightStatement (E := E) := by
  intro r X Xa Fl hPD _ bb m _ _ hlevi _ x0 hx0 FF hFF
  obtain ⟨k0, z0, hz0, hs0⟩ := exists_s_ne Fl x0 hx0
  refine ⟨PsK Xa Fl, fun z => Fl.s k0 (cpt X x0 z), WSk_metric Xa Fl, WSk_lower Xa Fl,
    IW.comp_cpt_diffOn X (s_diffOn Fl k0) x0, ⟨z0, hz0, hs0⟩, fun z hz => ?_, fun z hz hg1 => ?_,
    fun z hz hg1 ξ => ?_, fun g hg hint hv => ?_⟩
  · exact (PsK_cpt_cdAt Fl x0 k0 hz).contDiffWithinAt
  · exact WSk_eq_exp Xa Fl hz (sums_pos Fl hg1)
  · exact PsK_levi Fl x0 k0 m (hlevi x0 hx0) ⟨hz, hg1⟩ ξ
  · exact inFF_of hLU Fl hPD x0 hx0 FF hFF g hg hint hv

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.OW
end

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def KronHolStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa), PropDisc X →
    (∃ bb m : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb ∧ bb < m ∧
      ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
        m * leviRh X x0 z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ -
          (nd X : ℝ) * leviO X x0 (phla X Xa.L) z ξ) →
    (∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, 0 ≤ leviO X x0 (phla X Xa.L) z ξ) →
    ∀ j, ∃ (x0 : Frame X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ) (F : V (nd X) → ℂ)
      (P : Frame X.Ψ r → ℂ) (γ0 : GL (Fin r) E),
      IsOrth X x0 ∧ IsMetricW X Xa.Fp W ∧ WLower X Xa.Fp W ∧ 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb ∧
      DifferentiableOn ℂ F (OmF X x0) ∧ InAt X x0 W bb F ∧ IsBEq X Xa.Fp P ∧
      (∀ z ∈ OmF X x0, P (cpt X x0 z) = F z) ∧ γ0 ∈ X.Γ ∧ P (lact γ0 (Fl.xs j)) ≠ 0 ∧
      ∀ γ ∈ X.Γ, ∀ j', (γ ≠ γ0 ∨ j' ≠ j) → P (lact γ (Fl.xs j')) = 0

theorem chi_ne_zero {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) :
    X.χ la γ ≠ 0 := by
  obtain ⟨n, hn, h⟩ := X.χ_fin la
  intro h0
  have h1 := h γ hγ
  rw [h0, zero_pow hn.ne'] at h1
  exact zero_ne_one h1

theorem poin_single {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r)
    {γ0 : GL (Fin r) E} (h0 : γ0 ∈ X.Γ) (hz : ∀ γ ∈ X.Γ, γ ≠ γ0 → P (lact γ x) = 0) :
    poin X la P x = (X.χ la γ0)⁻¹ * P (lact γ0 x) := by
  unfold poin
  rw [tsum_eq_single ⟨γ0, h0⟩ fun γ hγ => by
    rw [hz γ.1 γ.2 fun h => hγ (Subtype.ext h), mul_zero]]

theorem poin_zero {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r)
    (hz : ∀ γ ∈ X.Γ, P (lact γ x) = 0) : poin X la P x = 0 := by
  unfold poin
  exact (tsum_congr fun γ => by rw [hz γ.1 γ.2, mul_zero]).trans tsum_zero

theorem leviO_zero {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) (z : V (nd X)) (ξ : Fin (nd X) → ℂ) :
    leviO X x0 (fun _ => (0 : ℝ)) z ξ = 0 := by
  have h0 : ∀ k, wdb (nd X) k (fun _ : V (nd X) => (0 : ℂ)) = fun _ => 0 := fun k => by
    funext y
    simp [wdb]
  simp [leviO, leviM, leviV, wd, h0]

theorem kronHol_of_psi (hK : KronHolPsiStatement (E := E)) : KronHolStatement (E := E) := by
  intro r X Xa Fl hPD hm hL j
  obtain ⟨bb, m, hb1, hb2, hb3⟩ := hm

  obtain ⟨η, hη, hpos⟩ := Xa.posF
  have hmarg : ∃ bb m : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb ∧ bb < m ∧
      ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
        m * leviRh X x0 z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ -
          (nd X : ℝ) * leviO X x0 (phla X Xa.L) z ξ + leviO X x0 (fun _ => (0 : ℝ)) z ξ :=
    ⟨bb, m, hb1, hb2, fun x0 hx z hz ξ => by
      rw [ReciprocityTheory.ChartRestriction.G.AR.Up.leviO_zero, add_zero]
      exact hb3 x0 hx z hz ξ⟩
  have heta : ∃ η : ℝ, 0 < η ∧ ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
      2 * η * leviO X x0 (phla X Xa.L) z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ -
        (nd X : ℝ) * leviO X x0 (phla X Xa.L) z ξ + leviO X x0 (fun _ => (0 : ℝ)) z ξ :=
    ⟨η, hη, fun x0 hx z hz ξ => by
      rw [ReciprocityTheory.ChartRestriction.G.AR.Up.leviO_zero, add_zero]
      have h1 := hpos 0 le_rfl (by rw [zero_mul]; positivity) x0
        (ReciprocityTheory.ChartRestriction.G.AR.Up.IW.orth_mem_dom X x0 hx) z hz ξ
      rw [zero_mul, zero_mul, sub_zero, ReciprocityTheory.ChartRestriction.G.AR.Up.IW.leviM_comb X x0 hx hz] at h1
      exact h1⟩
  obtain ⟨x0, W, bb', F, P, γ0, h1, h2, h3, -, h5, h6, h7, h8, h9, h10, h11, h12⟩ :=
    hK r X Xa Fl hPD (fun _ => 0) (fun _ _ _ _ _ _ => rfl) (fun _ _ => contDiffOn_const)
      ⟨0, fun _ _ => le_rfl⟩ hmarg heta hL j
  exact ⟨x0, W, bb', F, P, γ0, h1, h2, h3, h5, h6, h7, h8, h9, h10, h11, h12⟩

theorem interp_of (hP : PoinStatement (E := E)) (hK' : KronHolPsiStatement (E := E)) :
    InterpStatement (E := E) := by
  intro r X Xa Fl hPD hm hL hSS
  have hK := ReciprocityTheory.ChartRestriction.G.AR.Up.kronHol_of_psi hK'
  refine ReciprocityTheory.ChartRestriction.G.AR.Up.interp_of_kron X Xa.Fp Fl.xs fun j => ?_
  obtain ⟨x0, W, bb, F, P, γ0, hO, hW, hWL, hbb, hF, hIn, hBE, hPF, hγ0, hne, hzero⟩ :=
    hK r X Xa Fl hPD hm hL j

  have hIn' : InAt X x0 W bb (fun z => X.χ Xa.Fp γ0 / P (lact γ0 (Fl.xs j)) * F z) := by
    unfold InAt at hIn ⊢
    have h1 : ∀ z, ENNReal.ofReal (‖X.χ Xa.Fp γ0 / P (lact γ0 (Fl.xs j)) * F z‖ ^ 2 / kaF X x0 bb z) *
        W (cpt X x0 z) = ENNReal.ofReal (‖X.χ Xa.Fp γ0 / P (lact γ0 (Fl.xs j))‖ ^ 2) *
          (ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x0 bb z) * W (cpt X x0 z)) := fun z => by
      rw [norm_mul, mul_pow, mul_div_assoc, ENNReal.ofReal_mul (by positivity), mul_assoc]
    simp_rw [h1]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hIn
  have hBE' : IsBEq X Xa.Fp (fun x => X.χ Xa.Fp γ0 / P (lact γ0 (Fl.xs j)) * P x) :=
    ⟨(differentiableOn_const _).mul hBE.1, fun x hx b hb => by dsimp only; rw [hBE.2 x hx b hb]; ring⟩
  obtain ⟨-, hbdd, -⟩ := hP r X x0 hO hPD Xa.Fp W bb hW hWL hbb
    (fun z => X.χ Xa.Fp γ0 / P (lact γ0 (Fl.xs j)) * F z)
    (fun x => X.χ Xa.Fp γ0 / P (lact γ0 (Fl.xs j)) * P x)
    ((differentiableOn_const _).mul hF) hIn' hBE' fun z hz => by simp only [hPF z hz]
  refine ⟨_, ReciprocityTheory.ChartRestriction.G.AR.Up.ss_sub_ssgt0 X Xa.Fp (hSS _ hbdd), fun j' => ?_⟩
  split_ifs with hj
  · subst hj
    rw [ReciprocityTheory.ChartRestriction.G.AR.Up.poin_single X Xa.Fp _ (Fl.xs j') hγ0 fun γ hγ hγ' => by
      simp only [hzero γ hγ j' (Or.inl hγ'), mul_zero]]
    rw [div_mul_cancel₀ _ hne, inv_mul_cancel₀ (ReciprocityTheory.ChartRestriction.G.AR.Up.chi_ne_zero X Xa.Fp hγ0)]
  · exact ReciprocityTheory.ChartRestriction.G.AR.Up.poin_zero X Xa.Fp _ (Fl.xs j') fun γ hγ => by
      simp only [hzero γ hγ j' (Or.inr hj), mul_zero]

end

end ReciprocityTheory.ChartRestriction.G.AR.Up
end
