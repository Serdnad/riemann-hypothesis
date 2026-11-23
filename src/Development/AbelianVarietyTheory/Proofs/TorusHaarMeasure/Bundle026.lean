module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle025
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle008
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle020
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.FDeriv.WithLp
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth
import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle003
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.DerivDerivNonposOfIsLocalMax
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.Bundle004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle015
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfE
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfK
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle012
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle006
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourIndep
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowMeanContinuity
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FractionalSliceDomains
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajPos
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.TwoSidedBoostBounds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MinimumGrowthBounds

@[expose] public section

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
theorem _root_.GlobalTheory.T.compact_mod_latticeStabiliser_of_le_firstMinimum : (∀ (r : ℕ) (X : Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∀ x0, IsOrth X x0 → ∀ ε : ℝ, 0 < ε → ∃ K : Set H, IsCompact K ∧ ∀ g : H, ε ≤ X.la1 (X.lmulC (fun τ => (((g : H) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) → ∃ u : H, (∃ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ ∧ ∀ τ : X.Ψ, ((((u : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1) ∧ ∃ k ∈ K, g = u * k) := by
  first | exact @GlobalTheory.FiniteCovolume.exists_unitaryStab_mul_compact_of_le_firstMinimum | exact GlobalTheory.FiniteCovolume.exists_unitaryStab_mul_compact_of_le_firstMinimum | (intros; apply GlobalTheory.FiniteCovolume.exists_unitaryStab_mul_compact_of_le_firstMinimum <;> assumption)
end

section

namespace GlobalTheory.InterpCompare

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open MeasureTheory Topology
open scoped ContDiff ENNReal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem differentiable_chart (X : Data E r) (x0 : Frame X.Ψ r) : Differentiable ℂ (cpt X x0) :=
  IW.cpt_diff X x0

theorem levi_transport (X : Data E r) {x0 x1 : Frame X.Ψ r} (ho : IsOrth X x1) {z z1 : V (nd X)}
    (hz : z ∈ OmF X x0) (hz1 : z1 ∈ OmF X x1) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r)
    (hxb : cpt X x0 z = rmul (cpt X x1 z1) b) (ξ : Fin (nd X) → ℂ) :
    ∃ ξ' : Fin (nd X) → ℂ, (∀ la, leviM X (phla X la) x0 z ξ = leviM X (phla X la) x1 z1 ξ') ∧
      ∀ ψ : Frame X.Ψ r → ℝ, IsInvFn X ψ → ContDiffAt ℝ 2 (fun w => ψ (cpt X x1 w)) z1 →
        leviM X ψ x0 z ξ = leviM X ψ x1 z1 ξ' := by
  obtain ⟨Δ, zOf, bOf, hΔ, -, hzd, hbd, hsplit, hinv⟩ := lu_holds r X x1 ho
  have h0 := hinv z1 hz1 b hb
  rw [← hxb] at h0
  have hcd := differentiable_chart X x0
  set U : Set (V (nd X)) := {w | cpt X x0 w ∈ X.dom ∧ Δ (cpt X x0 w) ≠ 0} with hUdef
  have hU : IsOpen U :=
    (ExF.isOpen_OmF X x0).inter (isOpen_compl_singleton.preimage (hΔ.comp hcd).continuous)
  have hzU : z ∈ U := ⟨hz, h0.1⟩
  set Φ : V (nd X) → V (nd X) := fun w => zOf (cpt X x0 w) with hΦdef
  set bf : V (nd X) → Frame X.Ψ r := fun w => bOf (cpt X x0 w) with hbfdef
  have hΦ : DifferentiableOn ℂ Φ U := hzd.comp hcd.differentiableOn fun w hw => hw
  have hbf : DifferentiableOn ℂ bf U := hbd.comp hcd.differentiableOn fun w hw => hw
  have hΦz : Φ z = z1 := h0.2.1
  have hΦ2 : ContDiffOn ℂ 2 Φ U := by
    rw [contDiffOn_piLp]
    intro i
    exact (ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn _ _ U hU
      ((differentiableOn_piLp 2).1 hΦ i)).of_le HE.two_le_inf
  refine ⟨fun k => (fderiv ℂ Φ z (WithLp.toLp 2 ξ)).ofLp k, fun la => ?_, fun ψ hψ hψs => ?_⟩
  · have hch : DifferentiableOn ℂ (fun w => bchar la (bf w)) U := by
      classical
      intro w hw
      unfold bchar
      refine DifferentiableAt.differentiableWithinAt ?_
      refine (HasFDerivAt.finsetProd (g' := fun τ => fderiv ℂ (fun w => ∏ i, bf w τ i i ^ la τ i) w)
        fun τ _ => DifferentiableAt.hasFDerivAt ?_).differentiableAt
      refine (HasFDerivAt.finsetProd (g' := fun i => fderiv ℂ (fun w => bf w τ i i ^ la τ i) w)
        fun i _ => DifferentiableAt.hasFDerivAt ?_).differentiableAt
      have hw' : DifferentiableAt ℂ bf w := hbf.differentiableAt (hU.mem_nhds hw)
      have hi : DifferentiableAt ℂ (fun w => bf w τ i i) w :=
        differentiableAt_pi.1 (differentiableAt_pi.1 (differentiableAt_pi.1 hw' τ) i) i
      have hzp : DifferentiableAt ℂ (fun t : ℂ => t ^ la τ i) (bf w τ i i) :=
        differentiableAt_zpow.2
          (Or.inl (GlobalTheory.LeviTransfer.borel_diag_ne_zero (hsplit _ hw.1 hw.2).2.1 τ i))
      exact DifferentiableAt.comp (g := fun t : ℂ => t ^ la τ i) w hzp hi
    have hchz : ContDiffAt ℂ 2 (fun w => bchar la (bf w)) z :=
      (HE.contDiffAt_of_punct hU hch hzU).of_le HE.two_le_inf
    have hne : bchar la (bf z) ≠ 0 := IW.bchar_ne_zero X (hsplit _ hz h0.1).2.1 _
    have hev : (fun w => ((phla X la (cpt X x0 w) : ℝ) : ℂ)) =ᶠ[𝓝 z]
        fun w => ((phla X la (cpt X x1 (Φ w)) + Real.log (Complex.normSq (bchar la (bf w))) : ℝ) : ℂ) := by
      filter_upwards [hU.mem_nhds hzU] with w hw
      obtain ⟨h1, h2, h3⟩ := hsplit _ hw.1 hw.2
      rw [← GlobalTheory.LeviTransfer.metric_rmul normFactor_rightBorel_holds X la h1 h2, ← h3]
    have hg : ContDiffAt ℝ 2 (fun w => phla X la (cpt X x1 w)) (Φ z) := by
      rw [hΦz]
      exact (IW.phla_cpt_cdAt X x1 hz1 la).of_le HE.two_le_inf
    have h1 : ContDiffAt ℝ 2 (fun w => phla X la (cpt X x1 (Φ w))) z :=
      hg.comp z ((hΦ2.contDiffAt (hU.mem_nhds hzU)).restrict_scalars ℝ)
    have h2 : ContDiffAt ℝ 2 (fun w => Real.log (Complex.normSq (bchar la (bf w)))) z :=
      (HE.normSq_contDiffAt hchz).log (Complex.normSq_pos.2 hne).ne'
    have hgC : ContDiffAt ℝ 2 (fun w => ((phla X la (cpt X x1 w) : ℝ) : ℂ)) (Φ z) :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp _ hg
    have hc := RGF.gc_leviV_comp _ _ _ Φ U hU z hzU hΦ2 hgC ξ
    rw [hΦz] at hc
    unfold leviM
    rw [leviV_congr hev, Y.LocalMaximumSecondDerivative.leviV_ofReal_add h1 h2,
      HE.levi_logNormSq_zero_at _ z hchz hne ξ, add_zero]
    exact congrArg Complex.re hc
  · have hev : (fun w => ((ψ (cpt X x0 w) : ℝ) : ℂ)) =ᶠ[𝓝 z]
        fun w => ((ψ (cpt X x1 (Φ w)) : ℝ) : ℂ) := by
      filter_upwards [hU.mem_nhds hzU] with w hw
      obtain ⟨h1, h2, h3⟩ := hsplit _ hw.1 hw.2
      have := hψ 1 X.Γ.one_mem _ h1 _ h2
      rw [IW.lact_one, ← h3] at this
      rw [this]
    have hgC : ContDiffAt ℝ 2 (fun w => ((ψ (cpt X x1 w) : ℝ) : ℂ)) (Φ z) := by
      rw [hΦz]
      exact Complex.ofRealCLM.contDiff.contDiffAt.comp _ hψs
    have hc := RGF.gc_leviV_comp _ _ _ Φ U hU z hzU hΦ2 hgC ξ
    rw [hΦz] at hc
    unfold leviM
    rw [leviV_congr hev]
    exact congrArg Complex.re hc

end GlobalTheory.InterpCompare
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


open MajorantConjugateTransfer TwoSidedBoostBounds MinimumGrowthBounds FractionalSliceDomains in
theorem fj_norm_mul_exp_le_sup_flow :
    (∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (F : Frame X.Ψ r → ℂ), X.IsSec la F → ∀ ξ, X.IsIso ξ → ∀ (ν : X.Ψ → ℝ), ∀ x ∈ X.dom, ∃ B : ℝ, 0 ≤ B ∧ ∀ (y : X.Ψ → ℝ) (M : ℝ), (∀ τ, 0 ≤ y τ) → (∀ u : X.Ψ → ℝ, (∀ τ, |u τ| ≤ B) → ‖F (X.flow ξ (fun τ => (u τ : ℂ) + (y τ : ℂ) * Complex.I) x)‖ ≤ M) → ‖X.fj la ξ ν F x‖ * Real.exp (-4 * Real.pi * ∑ τ, ν τ * y τ) ≤ M) := open ReciprocityTheory.ChartRestriction.G.FD.FractionalSliceDomains ReciprocityTheory.ChartRestriction.G.FD.MinimumGrowthBounds ReciprocityTheory.ChartRestriction.G.FD.TwoSidedBoostBounds in by
  intro r X la P hP ξ hξ ν x hx
  classical
  obtain ⟨bs, hω⟩ := FlowMeanContinuity.exists_basis X la
  have hωp : ∀ j, bs j ∈ X.periods la := by
    intro j
    have : bs j ∈ Submodule.span ℤ (Set.range bs) := Submodule.subset_span ⟨j, rfl⟩
    rw [hω] at this
    exact this
  have hrepr : ∀ (v : X.Ψ → ℝ) τ, ∑ j, bs.repr v j * bs j τ = v τ := by
    intro v τ
    conv_rhs => rw [← bs.sum_repr v]
    simp [Finset.sum_apply, mul_comm]
  have hB := Bω_nonneg X bs
  refine ⟨Bω X bs, hB, ?_⟩
  intro y M hy hM
  by_cases hf : ∀ j, ∃ k : ℤ, 2 * ∑ τ, ν τ * bs j τ = k
  swap
  · have h0 : X.fj la ξ ν P x = 0 := by
      unfold Data.fj
      rw [if_neg]
      intro hall
      exact hf fun j => hall _ (hωp j)
    rw [h0, norm_zero, zero_mul]
    exact (norm_nonneg _).trans (hM 0 fun τ => by simpa using hB)
  choose k hk using hf
  rw [FlowMeanContinuity.fj_eq_fourCoeff X la P hP hξ hx bs hω ν k hk]
  change ‖ReciprocityTheory.L2DbarEstimates.Y.fourCoeff (hfun X P ξ x bs) 0 k‖ * _ ≤ _
  have hm : ∀ τ, 0 < X.maj x τ (Data.emb τ.1 ξ) :=
    fun τ => X.maj_pos hx τ (emb_ne_zero τ.1 hξ.2.2)
  have hc := c_pos X
  set b' : Fin (Fintype.card X.Ψ) → ℝ := fun j => bs.repr y j with hb'
  have hb'ω : ∀ τ, ∑ j, b' j * bs j τ = y τ := hrepr y
  have hb'Ω : b' ∈ FractionalSliceDomains.Om X ξ x bs := by
    show (fun τ => ∑ j, b' j * bs j τ) ∈ AdmissibleHermitianColumns.admissibleImaginary X ξ x
    rw [mem_admissibleImaginary_iff X hx hξ]
    intro τ
    rw [hb'ω]
    have := hc τ; have := hm τ; have := hy τ
    positivity
  have hind := ReciprocityTheory.L2DbarEstimates.Y.four_indep (Fintype.card X.Ψ) (FractionalSliceDomains.Om X ξ x bs) (hfun X P ξ x bs)
    (Om_open_conn X bs hx).1 (Om_open_conn X bs hx).2 (hfun_diff X bs P la hP hx hξ)
    (hfun_periodic X bs P la hP hx hξ hω) 0 (zero_mem_Om X bs hx hξ) b' hb'Ω k
  rw [hind]
  have hslice : ∀ t : Fin (Fintype.card X.Ψ) → ℝ,
      ‖hfun X P ξ x bs (fun k => (t k : ℂ) + (b' k : ℂ) * Complex.I)‖ ≤ M := by
    intro t
    rw [slice_fract X bs P la hP hx hξ hω hb'Ω t]
    have h := hM (fun τ => ∑ j, Int.fract (t j) * bs j τ) (fun τ =>
      re_bound X bs _ (fun j => ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩) τ)
    unfold hfun
    convert h using 4
    funext τ
    rw [← hb'ω τ]
    push_cast
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hbd := ReciprocityTheory.L2DbarEstimates.Y.four_bound (Fintype.card X.Ψ) (hfun X P ξ x bs) b' k _ hslice
  have hsum : ∑ j, (k j : ℝ) * b' j = 2 * ∑ τ, ν τ * ∑ j, b' j * bs j τ := by
    simp only [← hk, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hsum] at hbd
  simp only [hb'ω] at hbd
  convert hbd using 3
  ring

end GlobalTheory
end
