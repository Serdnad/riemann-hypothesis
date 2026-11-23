module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPfA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfE
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle010

@[expose] public section

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.OrbitCoord

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


omit [NumberField E] [IsCMField E] in
theorem rmul_left_cancel {r : ℕ} {Ψ : Finset (E →+* ℂ)} {o a c : Frame Ψ r}
    (ho : ∀ τ, (mat o τ).det ≠ 0) (h : rmul o a = rmul o c) : a = c := by
  funext τ
  have h1 : mat o τ * mat a τ = mat o τ * mat c τ := congrFun h τ
  have hu : IsUnit (mat o τ) := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (ho τ))
  exact hu.mul_left_cancel h1

theorem exists_swap {r : ℕ} (X : Data E r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) :
    ∃ (U : Set (V (nd X))) (Φ : V (nd X) → V (nd X)) (bf : V (nd X) → Frame X.Ψ r),
      IsOpen U ∧ 0 ∈ U ∧ DifferentiableOn ℂ Φ U ∧ Φ 0 = 0 ∧
      ∀ z ∈ U, bf z ∈ Bor X.Ψ r ∧ rmul b (nmat X z) = rmul (nmat X (Φ z)) (bf z) := by
  have ho : IsOrth X (x0F X) := fun τ => (X.signature τ).choose_spec.2
  have hod : x0F X ∈ X.dom := IW.orth_mem_dom X _ ho
  obtain ⟨Δ, zOf, bOf, hΔ, -, hz, -, hsplit, huniq⟩ := lu_holds r X (x0F X) ho
  have hcd := OntoB.cd_cpt X (rmul (x0F X) b)
  have h0 := huniq 0 (IW.zero_mem_OmF X _ ho) b hb
  rw [IW.cpt_zero] at h0
  refine ⟨cpt X (rmul (x0F X) b) ⁻¹' {x | x ∈ X.dom ∧ Δ x ≠ 0},
    fun z => zOf (cpt X (rmul (x0F X) b) z), fun z => bOf (cpt X (rmul (x0F X) b) z), ?_, ?_, ?_, ?_, ?_⟩
  · exact ((FourierCoefficientDomain.isOpen_dom X).inter
      (isOpen_ne_fun hΔ.continuous continuous_const)).preimage hcd.continuous
  · show cpt X _ 0 ∈ X.dom ∧ Δ (cpt X _ 0) ≠ 0
    rw [IW.cpt_zero]
    exact ⟨OntoS.dom_rmul X hod hb, h0.1⟩
  · exact hz.comp (hcd.differentiable (by simp)).differentiableOn fun _ h => h
  · show zOf (cpt X _ 0) = 0
    rw [IW.cpt_zero]
    exact h0.2.1
  · intro z hzU
    obtain ⟨-, h2, h3⟩ := hsplit _ hzU.1 hzU.2
    refine ⟨h2, rmul_left_cancel (fun τ => (hod τ).1) ?_⟩
    rw [← ExtFPf.rmul_assoc, ← ExtFPf.rmul_assoc]
    exact h3

theorem det_fderiv_ne_zero_orbit : (KapGGStatement (E := E)) → (∀ (r : ℕ) (X : Data E r) (L : Wt X.Ψ r) (w0 : Frame X.Ψ r → ℂ) (s : Fin (nd X) → Frame X.Ψ r → ℂ), X.IsSec L w0 → (∀ k, X.IsSec L (s k)) → ∀ x ∈ X.dom, w0 x ≠ 0 → (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k => s k (cpt X (x) z) / w0 (cpt X (x) z) : V (nd X))) 0).det ≠ 0 → ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k => s k (cpt X (lact γ (rmul x b)) z) / w0 (cpt X (lact γ (rmul x b)) z) : V (nd X))) 0).det ≠ 0) := by
  intro hK r X L w0 s hw0 hs x hx hwx hdet γ hγ b hb
  obtain ⟨U, Φ, bf, hU, h0U, hΦ, hΦ0, hsw⟩ := exists_swap X hb
  set y := lact γ (rmul x b) with hy
  have hyd : y ∈ X.dom := OntoS.dom_lact X hγ (OntoS.dom_rmul X hx hb)
  have hcpt : ∀ z ∈ U, cpt X y z = lact γ (rmul (cpt X x (Φ z)) (bf z)) := by
    intro z hz
    unfold cpt
    rw [hy, ← FundSetPf.lact_rmul, ExtFPf.rmul_assoc, (hsw z hz).2, ExtFPf.rmul_assoc]
  have h0y : (0 : V (nd X)) ∈ OmF X y := by
    show cpt X y 0 ∈ X.dom
    rwa [IW.cpt_zero]
  have h0x : (0 : V (nd X)) ∈ OmF X x := by
    show cpt X x 0 ∈ X.dom
    rwa [IW.cpt_zero]
  have hJ : (fderiv ℂ Φ 0).det = bchar (kapW X) (bf 0) :=
    hK r X y x γ (U ∩ OmF X y) Φ bf (hU.inter (OntoB.isOpen_OmF X y)) (hΦ.mono Set.inter_subset_left)
      (fun z hz => ⟨hz.2, (hsw z hz.1).1, hcpt z hz.1⟩) 0 ⟨h0U, h0y⟩
  have hJ0 : (fderiv ℂ Φ 0).det ≠ 0 := hJ ▸ OntoE.bchar_ne X _ (hsw 0 h0U).1
  have hΦd : DifferentiableAt ℂ Φ 0 := hΦ.differentiableAt (hU.mem_nhds h0U)
  have hnx : OmF X x ∈ 𝓝 (0 : V (nd X)) := (OntoB.isOpen_OmF X x).mem_nhds h0x
  set F : V (nd X) → V (nd X) := fun z : V (nd X) =>
    (WithLp.toLp 2 fun k => s k (cpt X (x) z) / w0 (cpt X (x) z) : V (nd X)) with hF
  have hFd : DifferentiableAt ℂ F 0 := by
    have hw : DifferentiableAt ℂ (fun z => w0 (cpt X x z)) 0 :=
      (OntoB.hol_comp X x hw0.1).differentiableAt hnx
    have hsk : ∀ k, DifferentiableAt ℂ (fun z => s k (cpt X x z)) 0 := fun k =>
      (OntoB.hol_comp X x (hs k).1).differentiableAt hnx
    rw [hF]
    refine (differentiableAt_piLp 2).2 fun k => ?_
    have hne : w0 (cpt X x 0) ≠ 0 := by rwa [IW.cpt_zero]
    have := (hsk k).mul (hw.inv hne)
    simp only [div_eq_mul_inv]
    exact this
  have hev : (fun z : V (nd X) => (WithLp.toLp 2 fun k =>
      s k (cpt X y z) / w0 (cpt X y z) : V (nd X))) =ᶠ[𝓝 0] F ∘ Φ := by
    have h1 : ∀ᶠ z in 𝓝 (0 : V (nd X)), Φ z ∈ OmF X x :=
      hΦd.continuousAt.preimage_mem_nhds (by rwa [hΦ0])
    filter_upwards [hU.mem_nhds h0U, h1] with z hz hzx
    have hzx' : cpt X x (Φ z) ∈ X.dom := hzx
    have hbz := (hsw z hz).1
    have hd := OntoS.dom_rmul X hzx' hbz
    have hχ : X.χ L γ ≠ 0 := by
      intro h
      have := OntoE.chi_norm X L hγ
      rw [h, norm_zero] at this
      exact zero_ne_one this
    show _ = F (Φ z)
    rw [hF]
    show (WithLp.toLp 2 _ : V (nd X)) = WithLp.toLp 2 _
    congr 1
    funext k
    rw [hcpt z hz, (hs k).2.2 γ hγ _ hd, hw0.2.2 γ hγ _ hd, mul_div_mul_left _ _ hχ,
      (hs k).2.1 _ hzx' _ hbz, hw0.2.1 _ hzx' _ hbz, mul_div_mul_left _ _ (OntoE.bchar_ne X L hbz)]
  rw [hev.fderiv_eq, fderiv_comp 0 (by rwa [hΦ0]) hΦd, hΦ0]
  have : ((fderiv ℂ F 0).comp (fderiv ℂ Φ 0)).det = (fderiv ℂ F 0).det * (fderiv ℂ Φ 0).det := by
    unfold ContinuousLinearMap.det
    rw [← LinearMap.det_comp]
    rfl
  rw [this]
  exact mul_ne_zero hdet hJ0

end GlobalTheory.OrbitCoord
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.KronAssembly

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem chi_ne_zero {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) :
    X.χ la γ ≠ 0 := by
  obtain ⟨n, hn, h⟩ := X.χ_fin la
  intro h0
  have := h γ hγ
  rw [h0, zero_pow hn.ne'] at this
  exact zero_ne_one this

theorem exists_orth {r : ℕ} (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {γ : GL (Fin r) E}
    (hγ : γ ∈ X.Γ) : ∃ x1, IsOrth X x1 ∧ ∃ b ∈ Bor X.Ψ r, ∃ b' ∈ Bor X.Ψ r,
      lact γ x = rmul x1 b ∧ x1 = lact γ (rmul x b') := by
  obtain ⟨x1, ho, b, hb, h⟩ := ortho_holds r X (lact γ x) (OntoS.dom_lact X hγ hx)
  refine ⟨x1, ho, b, hb, ExtFPf.invF X b, ExtFPf.invF_mem X hb, h, ?_⟩
  rw [FundSetPf.lact_rmul, h, ExtFPf.rmul_assoc, ExtFPf.rmul_invF X hb, ExtFPf.rmul_oneF]

theorem sec_ne_zero {r : ℕ} (X : Data E r) {L : Wt X.Ψ r} {w : Frame X.Ψ r → ℂ} (hw : X.IsSec L w)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) (h : w x ≠ 0) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ)
    {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) : w (lact γ (rmul x b)) ≠ 0 := by
  rw [hw.2.2 γ hγ _ (OntoS.dom_rmul X hx hb), hw.2.1 x hx b hb]
  exact mul_ne_zero (chi_ne_zero X L hγ) (mul_ne_zero (OntoE.bchar_ne X L hb) h)

end GlobalTheory.KronAssembly
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.PairUnfold

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


open Classical in
def pairDens {r : ℕ} (X : Data E r) (P f0 : Frame X.Ψ r → ℂ) (W : Frame X.Ψ r → ℝ≥0∞) :
    Frame X.Ψ r → ℂ :=
  fun y => X.dom.piecewise (fun y => P y * (starRingEnd ℂ) (f0 y)) 0 y * ((W y).toReal : ℂ)

theorem pairDens_dom {r : ℕ} (X : Data E r) (P f0 : Frame X.Ψ r → ℂ) (W : Frame X.Ψ r → ℝ≥0∞)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    pairDens X P f0 W x = P x * (starRingEnd ℂ) (f0 x) * ((W x).toReal : ℂ) := by
  simp [pairDens, Set.piecewise, hx]

theorem pairDens_meas {r : ℕ} (X : Data E r) {P f0 : Frame X.Ψ r → ℂ} {W : Frame X.Ψ r → ℝ≥0∞}
    (hP : ContinuousOn P X.dom) (hf : ContinuousOn f0 X.dom) (hW : Measurable W) :
    Measurable (pairDens X P f0 W) := by
  classical
  unfold pairDens
  exact (ContinuousOn.measurable_piecewise
    (hP.mul (Complex.continuous_conj.comp_continuousOn hf)) continuousOn_const
    (FourierCoefficientDomain.isOpen_dom X).measurableSet).mul
    (Complex.measurable_ofReal.comp hW.ennreal_toReal)

theorem pairDens_rmul {r : ℕ} (X : Data E r) {la : Wt X.Ψ r} {P f0 : Frame X.Ψ r → ℂ}
    {W : Frame X.Ψ r → ℝ≥0∞}
    (hP : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, P (rmul x b) = bchar la b * P x)
    (hf : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, f0 (rmul x b) = bchar la b * f0 x)
    (hW : IsMetricW X la W) :
    ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, pairDens X P f0 W (rmul x b) = pairDens X P f0 W x := by
  intro x hx b hb
  have h0 := OntoE.bchar_ne X la hb
  have h1 : (starRingEnd ℂ) (bchar la b) ≠ 0 := by simpa using h0
  rw [pairDens_dom X P f0 W (OntoS.dom_rmul X hx hb), pairDens_dom X P f0 W hx, hP x hx b hb,
    hf x hx b hb, hW.2.1 x hx b hb, ENNReal.toReal_div, ENNReal.toReal_ofReal (sq_nonneg _), map_mul]
  push_cast
  rw [← Complex.mul_conj']
  field_simp

theorem pairDens_lact {r : ℕ} (X : Data E r) {la : Wt X.Ψ r} {P f0 : Frame X.Ψ r → ℂ}
    {W : Frame X.Ψ r → ℝ≥0∞}
    (hf : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, f0 (lact γ x) = X.χ la γ * f0 x)
    (hW : IsMetricW X la W) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    pairDens X P f0 W (lact γ x) =
      (X.χ la γ)⁻¹ * P (lact γ x) * ((starRingEnd ℂ) (f0 x) * ((W x).toReal : ℂ)) := by
  rw [pairDens_dom X P f0 W (OntoS.dom_lact X hγ hx), hf γ hγ x hx, hW.2.2 γ hγ x hx, map_mul,
    Complex.inv_eq_conj (OntoE.chi_norm X la hγ)]
  ring

theorem kaF_meas {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) (bb : ℝ) : Measurable (kaF X x0 bb) := by
  unfold kaF rhF
  refine Real.measurable_exp.comp (measurable_const.mul (Measurable.neg ?_))
  refine Finset.measurable_fun_sum _ fun τ _ => Real.measurable_log.comp ?_
  exact (OntoB.cd_dmin X x0 τ _).continuous.norm.measurable

theorem enorm_le {k : ℝ} (hk : 0 < k) (u g : ℂ) (w : ℝ≥0∞) :
    ‖u * (starRingEnd ℂ) g * (w.toReal : ℂ)‖ₑ ≤
      ENNReal.ofReal (‖u‖ ^ 2 / k) * w + ENNReal.ofReal k * (ENNReal.ofReal (‖g‖ ^ 2) * w) := by
  have h1 := OntoG.amgm (x := ‖u‖) (y := ‖g‖) hk
  have h2 : ‖u‖ * ‖g‖ ≤ ‖u‖ ^ 2 / k + k * ‖g‖ ^ 2 := by
    have : 0 ≤ ‖u‖ * ‖g‖ := by positivity
    linarith
  rw [← ofReal_norm_eq_enorm, norm_mul, norm_mul, RCLike.norm_conj, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_mul (by positivity),
    ← mul_assoc, ← ENNReal.ofReal_mul hk.le, ← add_mul,
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal h2) ENNReal.ofReal_toReal_le

theorem pairUnfold_of_unfold :
    (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ FF, IsFundSet X x0 FF → ∀ h : Frame X.Ψ r → ℂ, Measurable h → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, h (rmul x b) = h x) → Integrable (fun z => h (cpt X x0 z)) (muF X x0) → ∫ z, h (cpt X x0 z) ∂muF X x0 = ∫ z in FF, ∑' γ : X.Γ, h (lact γ.1 (cpt X x0 z)) ∂muF X x0) → (KaUnfoldStatement (E := E)) → (PairUnfoldStatement (E := E)) := by
  intro hU hKa r X x0 hx0 hPD la W bb hW _ hbb F P _ hIn hP hPF FF hFF f0 hf0 hfF
  have hsec := hf0.1.1
  obtain ⟨C, hCt, hC⟩ := hKa r X x0 hx0 hPD FF hFF bb hbb
  have hφm := OntoE.phiF_meas X hsec.1.continuousOn hW.1
  have hφ := hC (OntoE.phiF X f0 W) hφm (OntoE.phiF_B X hsec.2.1 hW) (OntoE.phiF_G X hsec.2.2 hW)
  have hFFeq : ∫⁻ z in FF, OntoE.phiF X f0 W (cpt X x0 z) ∂muF X x0 =
      ∫⁻ z in FF, ENNReal.ofReal (‖f0 (cpt X x0 z)‖ ^ 2) * W (cpt X x0 z) ∂muF X x0 :=
    setLIntegral_congr_fun hFF.1 (fun z hz => OntoE.phiF_dom X f0 W (hFF.2.1 hz))
  have hI : ∫⁻ z, ENNReal.ofReal (kaF X x0 bb z) * OntoE.phiF X f0 W (cpt X x0 z) ∂muF X x0 < ⊤ := by
    refine hφ.trans_lt (ENNReal.mul_lt_top hCt ?_)
    rw [hFFeq]; exact hfF
  have hcm : Measurable (cpt X x0) := (FundSetPf.cont_cpt X x0).measurable
  have hae := FundSetPf.ae_OmF' X x0
  have hm := pairDens_meas X hP.1.continuousOn hsec.1.continuousOn hW.1
  have hint : Integrable (fun z => pairDens X P f0 W (cpt X x0 z)) (muF X x0) := by
    refine ⟨(hm.comp hcm).aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    calc ∫⁻ z, ‖pairDens X P f0 W (cpt X x0 z)‖ₑ ∂muF X x0
        ≤ ∫⁻ z, (ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x0 bb z) * W (cpt X x0 z) +
            ENNReal.ofReal (kaF X x0 bb z) * OntoE.phiF X f0 W (cpt X x0 z)) ∂muF X x0 := by
          refine lintegral_mono_ae (hae.mono fun z hz => ?_)
          rw [pairDens_dom X P f0 W hz, OntoE.phiF_dom X f0 W hz, hPF z hz]
          exact enorm_le (Real.exp_pos _) _ _ _
      _ < ⊤ := by
          have hB : Measurable fun z => ENNReal.ofReal (kaF X x0 bb z) *
              OntoE.phiF X f0 W (cpt X x0 z) :=
            (ENNReal.measurable_ofReal.comp (kaF_meas X x0 bb)).mul (hφm.comp hcm)
          rw [lintegral_add_right _ hB]
          exact ENNReal.add_lt_top.2 ⟨hIn, hI⟩
  have key := hU r X x0 hx0 FF hFF _ hm (pairDens_rmul X hP.2 hsec.2.1 hW) hint
  calc _ = ∫ z in FF, ∑' γ : X.Γ, pairDens X P f0 W (lact γ.1 (cpt X x0 z)) ∂muF X x0 := by
        refine setIntegral_congr_fun hFF.1 fun z hz => ?_
        have hz' : cpt X x0 z ∈ X.dom := hFF.2.1 hz
        simp only [poin]
        rw [mul_assoc, ← tsum_mul_right]
        exact tsum_congr fun γ => (pairDens_lact X hsec.2.2 hW γ.2 hz').symm
    _ = _ := by
        rw [← key]
        refine integral_congr_ae (hae.mono fun z hz => ?_)
        simp only
        rw [pairDens_dom X P f0 W hz, hPF z hz]

end

end GlobalTheory.PairUnfold
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.FrameMeas

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def borSat {r : ℕ} (X : Data E r) (C : Set (Frame X.Ψ r)) : Set (Frame X.Ψ r) :=
  {y | ∃ x ∈ C, ∃ b ∈ Bor X.Ψ r, y = rmul x b}

theorem borSat_subset_dom {r : ℕ} (X : Data E r) {C : Set (Frame X.Ψ r)} (hC : C ⊆ X.dom) :
    borSat X C ⊆ X.dom := by
  rintro y ⟨x, hx, b, hb, rfl⟩
  exact OrthogonalFrameDomain.rmul_mem_dom X (hC hx) hb

theorem subset_borSat {r : ℕ} (X : Data E r) (C : Set (Frame X.Ψ r)) : C ⊆ borSat X C :=
  fun x hx => ⟨x, hx, ExtFPf.oneF X, ExtFPf.oneF_mem X, (ExtFPf.rmul_oneF X x).symm⟩

theorem rmul_mem_borSat_iff {r : ℕ} (X : Data E r) (C : Set (Frame X.Ψ r)) {y b : Frame X.Ψ r}
    (hb : b ∈ Bor X.Ψ r) : rmul y b ∈ borSat X C ↔ y ∈ borSat X C := by
  constructor
  · rintro ⟨x, hx, b', hb', h⟩
    refine ⟨x, hx, rmul b' (ExtFPf.invF X b), ExtFPf.mul_mem X hb' (ExtFPf.invF_mem X hb), ?_⟩
    rw [← ExtFPf.rmul_assoc, ← h, ExtFPf.rmul_assoc, ExtFPf.rmul_invF X hb, ExtFPf.rmul_oneF]
  · rintro ⟨x, hx, b', hb', rfl⟩
    exact ⟨x, hx, rmul b' b, ExtFPf.mul_mem X hb' hb, ExtFPf.rmul_assoc X _ _ _⟩

theorem measurableSet_borSat {r : ℕ} (X : Data E r) {C : Set (Frame X.Ψ r)} (hK : IsCompact C)
    (hC : C ⊆ X.dom) : MeasurableSet (borSat X C) := by
  have : CompactSpace C := isCompact_iff_compactSpace.mp hK
  let T : Set (Frame X.Ψ r × C) := {p | ∀ τ : X.Ψ, ∀ a c : Fin r, c < a →
    ((mat p.2.1 τ).adjugate * ((1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 *
      mat p.1 τ) a c = 0}
  have hm : ∀ τ : X.Ψ, Continuous fun y : Frame X.Ψ r => mat y τ := fun τ => continuous_apply τ
  have hT : IsClosed T := by
    simp only [T, Set.setOf_forall]
    refine isClosed_iInter fun τ => isClosed_iInter fun a => isClosed_iInter fun c =>
      isClosed_iInter fun _ => isClosed_eq ?_ continuous_const
    exact (((((hm τ).comp (continuous_subtype_val.comp continuous_snd)).matrix_adjugate).matrix_mul
      continuous_const).matrix_mul ((hm τ).comp continuous_fst)).matrix_elem a c
  have hT' : IsClosed (Prod.fst '' T) := isClosedMap_fst_of_compactSpace T hT
  have hU : IsOpen {y : Frame X.Ψ r | ∀ τ, (mat y τ).det ≠ 0} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun τ => isOpen_ne_fun (hm τ).matrix_det continuous_const
  have heq : borSat X C = {y : Frame X.Ψ r | ∀ τ, (mat y τ).det ≠ 0} ∩ Prod.fst '' T := by
    ext y
    constructor
    · intro hy
      have hyd : ∀ τ, (mat y τ).det ≠ 0 := fun τ => (borSat_subset_dom X hC hy τ).1
      obtain ⟨x, hx, b, hb, h⟩ := hy
      refine ⟨hyd, (y, ⟨x, hx⟩), ?_, rfl⟩
      exact (FundSetPf.charB 1 hyd fun τ => (hC hx τ).1).mp
        ⟨b, hb, by rw [FundSetPf.lact_one]; exact h⟩
    · rintro ⟨hyd, ⟨y', x, hx⟩, hp, rfl⟩
      obtain ⟨b, hb, h⟩ := (FundSetPf.charB 1 hyd fun τ => (hC hx τ).1).mpr hp
      rw [FundSetPf.lact_one] at h
      exact ⟨x, hx, b, hb, h⟩
  rw [heq]
  exact hU.measurableSet.inter hT'.measurableSet

theorem sat_eq_preimage {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) {C : Set (Frame X.Ψ r)}
    (hC : C ⊆ X.dom) : sat X x0 C = cpt X x0 ⁻¹' borSat X C := by
  ext z
  exact ⟨fun h => h.2, fun h => ⟨borSat_subset_dom X hC h, h⟩⟩

theorem frameMeas_of_local (hI : MeasInvStatement (E := E))
    (hL : ∀ (r : ℕ) (X : Data E r) (x1 : Frame X.Ψ r), IsOrth X x1 → ∀ b1 ∈ Bor X.Ψ r,
      ∃ U ∈ 𝓝 (rmul x1 b1), ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ G : Frame X.Ψ r → ℝ≥0∞, Measurable G →
        (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, G (rmul x b) = G x) →
        ∫⁻ x in U, G x ≤ K * ∫⁻ z, G (cpt X x1 z) ∂muF X x1) :
    FrameMeasStatement (E := E) := by
  intro r X x0 hx0 C hK hC
  have key : ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ G : Frame X.Ψ r → ℝ≥0∞, Measurable G →
      (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, G (rmul x b) = G x) →
      ∫⁻ x in C, G x ≤ K * ∫⁻ z, G (cpt X x0 z) ∂muF X x0 := by
    refine hK.induction_on (p := fun s => ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ G : Frame X.Ψ r → ℝ≥0∞,
      Measurable G → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, G (rmul x b) = G x) →
      ∫⁻ x in s, G x ≤ K * ∫⁻ z, G (cpt X x0 z) ∂muF X x0) ?_ ?_ ?_ ?_
    · exact ⟨0, ENNReal.zero_lt_top, fun G _ _ => by simp⟩
    · rintro s t hst ⟨K, hK, h⟩
      exact ⟨K, hK, fun G hG hB => (lintegral_mono_set hst).trans (h G hG hB)⟩
    · rintro s t ⟨K, hK, h⟩ ⟨K', hK', h'⟩
      refine ⟨K + K', ENNReal.add_lt_top.mpr ⟨hK, hK'⟩, fun G hG hB => ?_⟩
      rw [add_mul]
      exact (lintegral_union_le _ _ _).trans (add_le_add (h G hG hB) (h' G hG hB))
    · intro x hx
      obtain ⟨x1, hx1, b1, hb1, rfl⟩ := ortho_holds r X x (hC hx)
      obtain ⟨U, hU, K, hK, h⟩ := hL r X x1 hx1 b1 hb1
      refine ⟨U, mem_nhdsWithin_of_mem_nhds hU, K, hK, fun G hG hB => ?_⟩
      rw [hI r X x0 x1 hx0 hx1 G hG hB]
      exact h G hG hB
  obtain ⟨K, hKt, h⟩ := key
  refine ⟨K, hKt, fun G hG hB => ?_⟩
  have hS := measurableSet_borSat X hK hC
  have h1 := h ((borSat X C).indicator G) (hG.indicator hS) (by
    intro x hx b hb
    by_cases hxS : x ∈ borSat X C
    · rw [Set.indicator_of_mem hxS, Set.indicator_of_mem ((rmul_mem_borSat_iff X C hb).mpr hxS),
        hB x hx b hb]
    · rw [Set.indicator_of_notMem hxS,
        Set.indicator_of_notMem fun h => hxS ((rmul_mem_borSat_iff X C hb).mp h)])
  have h2 : ∫⁻ x in C, (borSat X C).indicator G x = ∫⁻ x in C, G x :=
    setLIntegral_congr_fun hK.measurableSet fun x hx =>
      Set.indicator_of_mem (subset_borSat X C hx) G
  have h3 : ∫⁻ z, (borSat X C).indicator G (cpt X x0 z) ∂muF X x0 =
      ∫⁻ z in sat X x0 C, G (cpt X x0 z) ∂muF X x0 := by
    rw [sat_eq_preimage X x0 hC,
      ← lintegral_indicator ((FundSetPf.cont_cpt X x0).measurable hS)]
    rfl
  rw [← h2, ← h3]
  exact h1

end GlobalTheory.FrameMeas
end
