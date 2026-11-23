module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle108
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle056
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreKLAtMost
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle133
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle094
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLemB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle111
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LieBracketMultiplication
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle082
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedS
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ParametersUPrimeForULower
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle144
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle004
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ComplexifiedDerivativeCommutator
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DirectionsInParabolic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle092

@[expose] public section

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC

noncomputable section

theorem line_at_most_one_holds : LineAtMost := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl hk Pr hPr π ζ hζ X hX Y hY hX0
  have hζT : P.TT < Complex.normSq ζ := hζ
  obtain ⟨hOK, hz, hz', hTz, hTz', -, -⟩ := id hpl
  have hζ' : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ := by
    rw [hTz, hTz']; exact hζT
  have hT := Bs.T_pos
  obtain ⟨hνfix, hνν, -, -⟩ := DU.base hz hz' Bs.T_pos Bs.T'_pos Bs.sec hζ'
  set ν := SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ with hνdef
  set μ := NF.muZ P.k P.r Bs.μsec ζ with hμ
  have hm := NFRadRedA.muZ_uwb Bs.sec hζ'
  have hG := NFRadRedA.uwb_glev hm
  have hy : inWb P.k P.r (μ *ᵥ Bs.z') := Qx8.inWb_mulVec hG hz'
  have hνW : inWb P.k P.r ν := by
    show inWb P.k P.r (SSn.unitH P.k P.r (SSn.prWv P.k P.r Bs.z (μ *ᵥ Bs.z')))
    unfold SSn.unitH
    exact Qx8.inWb_smul (DU.prWv_inWb hz hy) _
  have hνz : herm (Hpk P.k P.r) ν Bs.z = 0 := by
    rw [← hνfix]; exact DU.prWv_perp hT hνW
  obtain ⟨Fr, hFr⟩ := Topx1.typ_frame_exists P.k P.r (by omega) Bs.z ν hz hT hνW hνz hνν
  obtain ⟨hFr', hpass⟩ := PRho.GL.gauge_left_line_holds Wp Wq P Bs hpl hk ζ hζT Fr hFr
  have hq : ((fun _ => (1 : ℂ)), ζ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨fun _ => one_ne_zero, hζ'⟩
  obtain ⟨-, hg, hGG⟩ := Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' Bs.sec hq
  have hgl' := (Formalism.FourierDecayAlt.P.frame_general_linear Wq P.k P.r (P.k - 1) Bs.z' Bs.π'
    (fun a => μ⁻¹ *ᵥ Fr a) ⟨Bs.π'_rep, Bs.π'_cont⟩
    (Formalism.FourierDecayAlt.P.Qx8.frame_sub hFr' (by simp))).2
  have hpos : 0 < PRho.nrmW P.k P.r Bs.z ν := by
    unfold PRho.nrmW
    rw [hνfix, hνν]; simp
  have hcap : ∀ Z ∈ Line P Bs Pr π ζ, Gauge.GC.CapEig P Bs.π' (fun a => μ⁻¹ *ᵥ Fr a) π Z := by
    intro Z hZ Yc v
    have hZv : Pr π ν (Z v) = Z v := by
      have := DFunLike.congr_fun hZ.2 v
      simpa only [ContinuousLinearMap.comp_apply] using this
    have hr := ((hPr.2.2 ν hpos).2.2.2 π (Z v)).1 hZv Fr (by rw [hνfix]; exact hFr) (Yc + ((P.k : ℂ) - 2) / 2)
    rw [hpass Z hZ.1, hgl'] at hr
    have e : Yc + ((P.k : ℂ) - 2) / 2 - ((P.k : ℂ) - 2) / 2 = Yc := by ring
    rw [e] at hr
    exact hr
  have hXF : X ∈ Gauge.GC.FibAt P.k P.r Bs.z Bs.z' Bs.π Bs.π' μ :=
    fun h hh h' hh' he => hX.1 (h, h') ⟨hh, hh', he⟩
  have hYF : Y ∈ Gauge.GC.FibAt P.k P.r Bs.z Bs.z' Bs.π Bs.π' μ :=
    fun h hh h' hh' he => hY.1 (h, h') ⟨hh, hh', he⟩
  exact Gauge.GC.lie_weight_at_most_holds Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hpl hk _ hg hGG.ne' _ hFr' π X Y hXF hYF
    (hcap X hX) (hcap Y hY) hX0

theorem modConst_of_cut : ModConstOfCut := by
  intro hLN hAM hDT hSR hSN hTF Wp Wq _ _ _ _ _ _ P Bs hk X d hA l hl S hS Pr hPr Bw Bw' hBw hBw' π ρ hUp
  have hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' := hA.1
  obtain ⟨hOK, hz, hz', hTz, hTz', -, -⟩ := id hpl
  set x0 : ℝ := |P.TT| + 1 with hx0
  have hζ0 : ((x0 : ℝ) : ℂ) ∈ Gauge.GC.Ann P := by
    show P.TT < Complex.normSq ((x0 : ℝ) : ℂ)
    rw [Complex.normSq_ofReal]
    nlinarith [abs_nonneg P.TT, le_abs_self P.TT]
  obtain ⟨X0, hX0F, hX0P, hX0ne⟩ := hLN Wp Wq P Bs hpl hk Pr hPr π _ hζ0
  set ζ0 : ℂ := ((x0 : ℝ) : ℂ) with hζ0def
  set T0 := (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ0)).comp
    (tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ0)
      (SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec ζ0) (SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec ζ0) X0) with hT0
  have hB0 : ‖B.hsVec X0‖ ≠ 0 := norm_ne_zero_iff.2 (Gauge.GC.hsVec_ne_zero hX0ne)
  refine ⟨M.Nrm P l π, ‖B.hsVec T0‖ ^ 2 / ‖B.hsVec X0‖ ^ 2, fun ζ hζ Xf hXf hXP => ⟨?_, ?_⟩⟩
  · have hL : Xf ∈ Line P Bs Pr π ζ := ⟨hXf, hXP⟩
    have hR := hSR Wp Wq P Bs hk X d hA l hl S hS Pr hPr π ρ hUp ζ hζ Xf hL
    rw [hR.2]
    exact hSN Wp Wq P Bs hk X d hA l hl S hS Pr hPr π ζ hζ Xf hL
  · have hζT : P.TT < Complex.normSq ζ := hζ
    have hζ' : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ := by
      rw [hTz, hTz']; exact hζT
    have hζ0T : P.TT < Complex.normSq ζ0 := hζ0
    have hζ0' : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ0 := by
      rw [hTz, hTz']; exact hζ0T
    obtain ⟨h, hh, h', hh', hν, hν', hι, hst⟩ :=
      hDT P.k P.r Bs.z Bs.z' Bs.μsec hk hz hz' Bs.T_pos Bs.T'_pos Bs.sec ζ0 ζ hζ0' hζ'
    have hhi := LieBracketMultiplication.uw_inv hh
    have hh'i := LieBracketMultiplication.uw_inv hh'
    have hiso : ∀ Y, ‖B.hsVec ((Bs.π h).comp (Y.comp (Bs.π' h'⁻¹)))‖ = ‖B.hsVec Y‖ :=
      fun Y => CutBP.hsVec_norm_CinL Bs hh hh' Y
    have hinv1 : ∀ w, Bs.π h⁻¹ (Bs.π h w) = w := by
      intro w
      rw [← ContinuousLinearMap.comp_apply, ← Bs.π_rep.2 _ hhi _ hh, NFRadRedS.uw_inv_mul hh, Bs.π_rep.1]
      rfl

    have hF : (Bs.π h).comp (X0.comp (Bs.π' h'⁻¹)) ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ := by
      refine fun p hp => ?_
      have hp1 : p.1 ∈ UWset P.k P.r Bs.z := hp.1
      have hp2 : p.2 ∈ UWset P.k P.r Bs.z' := hp.2.1
      have hm1 : h⁻¹ * p.1 * h ∈ UWset P.k P.r Bs.z := LieBracketMultiplication.uw_mul (LieBracketMultiplication.uw_mul hhi hp1) hh
      have hm2 : h'⁻¹ * p.2 * h' ∈ UWset P.k P.r Bs.z' := LieBracketMultiplication.uw_mul (LieBracketMultiplication.uw_mul hh'i hp2) hh'
      have key := hX0F _ (hst p hp)
      have e1 : (Bs.π p.1).comp (Bs.π h) = (Bs.π h).comp (Bs.π (h⁻¹ * p.1 * h)) := by
        rw [← Bs.π_rep.2 _ hp1 _ hh, ← Bs.π_rep.2 _ hh _ hm1, ← mul_assoc, ← mul_assoc,
          NFRadRedS.uw_mul_inv hh, one_mul]
      have e2 : (Bs.π' h'⁻¹).comp (Bs.π' p.2) = (Bs.π' (h'⁻¹ * p.2 * h')).comp (Bs.π' h'⁻¹) := by
        rw [← Bs.π'_rep.2 _ hh'i _ hp2, ← Bs.π'_rep.2 _ hm2 _ hh'i, mul_assoc (h'⁻¹ * p.2) h' h'⁻¹,
          NFRadRedS.uw_mul_inv hh', mul_one]
      ext v
      have k1 := DFunLike.congr_fun e1 (X0 (Bs.π' h'⁻¹ (Bs.π' p.2 v)))
      have k2 := DFunLike.congr_fun e2 v
      have k3 := DFunLike.congr_fun key (Bs.π' h'⁻¹ v)
      simp only [ContinuousLinearMap.comp_apply] at k1 k2 k3 ⊢
      rw [k1, k2, k3]

    have hP : (Pr π (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp ((Bs.π h).comp (X0.comp (Bs.π' h'⁻¹))) =
        (Bs.π h).comp (X0.comp (Bs.π' h'⁻¹)) := by
      rw [← hν, hPr.2.1 h hh π (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ0)]
      ext v
      have k1 := DFunLike.congr_fun hX0P (Bs.π' h'⁻¹ v)
      simp only [ContinuousLinearMap.comp_apply] at k1 ⊢
      rw [hinv1, k1]
    have hL0 : (Bs.π h).comp (X0.comp (Bs.π' h'⁻¹)) ∈ Line P Bs Pr π ζ := ⟨hF, hP⟩
    have hne : (Bs.π h).comp (X0.comp (Bs.π' h'⁻¹)) ≠ 0 := by
      intro h0
      apply hB0
      have hz0 : B.hsVec (0 : Wq →L[ℂ] Wp) = 0 := by
        rw [← zero_smul ℂ (0 : Wq →L[ℂ] Wp), Gauge.GC.hsVec_smul, zero_smul]
      rw [← hiso X0, h0, hz0, norm_zero]
    obtain ⟨c, hc⟩ := hAM Wp Wq P Bs hpl hk Pr hPr π ζ hζ _ hL0 Xf ⟨hXf, hXP⟩ hne

    have hTe := ((hTF Wp Wq P Bs hpl Bw Bw' hBw hBw').2.2.2.1 h hh h' hh'
      (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ0) (SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec ζ0)
      (SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec ζ0) X0).1
    rw [hν, hν', hι] at hTe
    have hPT : (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp
        (tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)
          (SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec ζ) (SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)
          ((Bs.π h).comp (X0.comp (Bs.π' h'⁻¹)))) = (Bs.π h).comp (T0.comp (Bs.π' h'⁻¹)) := by
      rw [hTe]
      conv_lhs => rw [← hν]
      rw [hPr.2.1 h hh ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ0), hT0]
      ext v
      simp only [ContinuousLinearMap.comp_apply]
      rw [hinv1]
    rw [hc, map_smul, ContinuousLinearMap.comp_smul, hPT, Gauge.GC.hsVec_smul, Gauge.GC.hsVec_smul,
      norm_smul, norm_smul, hiso, hiso]
    field_simp

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC
end

section

open Matrix Filter Topology
open scoped ComplexConjugate ContDiff

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Formalism.FourierDecayAlt.P.WirtingerOperators

open Formalism.REAL

abbrev rdzPZ (j : ℕ) : Type := ℂ × (Fin j → Fin j → ℂ)

def rdzLdL {j : ℕ} (x : MJ j) : rdzPZ j →ₗ[ℝ] rdzPZ j where
  toFun q := (0, fun a b => ∑ c, q.2 a c * x c b)
  map_add' p q := Prod.ext (by simp) (by funext a b; simp [add_mul, Finset.sum_add_distrib])
  map_smul' t q := Prod.ext (by simp) (by funext a b; simp [Finset.smul_sum, mul_assoc])

def rdzLd {j : ℕ} (x : MJ j) : rdzPZ j →L[ℝ] rdzPZ j := LinearMap.toContinuousLinearMap (rdzLdL x)

theorem rdzLd_apply {j : ℕ} (x : MJ j) (q : rdzPZ j) : rdzLd x q = (0, fun a b => ∑ c, q.2 a c * x c b) := rfl

theorem rdzLd_inl {j : ℕ} (x : MJ j) (v : ℂ) : rdzLd x ((v, 0) : rdzPZ j) = 0 := by
  rw [rdzLd_apply]
  exact Prod.ext rfl (by funext a b; simp)

theorem rdz_curve {j : ℕ} (x : MJ j) (τ : ℂ) (Z : MJ j) :
    HasDerivAt (fun t : ℝ => ((τ, (Z * NormedSpace.exp ((t : ℂ) • x) : MJ j)) : rdzPZ j)) (rdzLd x (τ, Z)) 0 := by
  refine HasDerivAt.congr_deriv ((hasDerivAt_const (0 : ℝ) τ).prodMk (hasDerivAt_mul_exp_smul_zero Z x)) ?_
  rw [rdzLd_apply]
  exact Prod.ext rfl (funext fun a => funext fun b => Matrix.mul_apply)

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem rdz_da {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {h : F → E} {V : Set F} (hV : IsOpen V)
    (hh : ContDiffOn ℝ ∞ h V) {Z : F} (hZ : Z ∈ V) : DifferentiableAt ℝ h Z :=
  (hh.contDiffAt (hV.mem_nhds hZ)).differentiableAt (by simp)

theorem rdz_rd {j : ℕ} (x : MJ j) (G : rdzPZ j → E) (τ : ℂ) (Z : MJ j) (hd : DifferentiableAt ℝ G (τ, Z)) :
    RdV x (fun Z' : MJ j => G (τ, Z')) Z = fderiv ℝ G (τ, Z) (rdzLd x (τ, Z)) := by
  have h0 : ((τ, (Z * NormedSpace.exp (((0 : ℝ) : ℂ) • x) : MJ j)) : rdzPZ j) = (τ, Z) := by
    (simp [NormedSpace.exp_zero]; rfl)
  exact (hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (rdz_curve x τ Z) h0.symm).deriv

theorem rdz_loc {j : ℕ} (x : MJ j) (h₁ h₂ : MJ j → E) (Z : MJ j) (h : h₁ =ᶠ[𝓝 Z] h₂) :
    RdV x h₁ Z = RdV x h₂ Z := by
  have ht : Tendsto (fun t : ℝ => Z * NormedSpace.exp ((t : ℂ) • x)) (𝓝 0) (𝓝 Z) := by
    have := (hasDerivAt_mul_exp_smul_zero Z x).continuousAt.tendsto
    simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, mul_one] at this
    exact this
  unfold RdV
  exact Filter.EventuallyEq.deriv_eq (ht.eventually h)

theorem rdz_hd {j : ℕ} (x : MJ j) {h : MJ j → E} {Z : MJ j} (hd : DifferentiableAt ℝ h Z) :
    HasDerivAt (fun t : ℝ => h (Z * NormedSpace.exp ((t : ℂ) • x))) (fderiv ℝ h Z (Z * x)) 0 := by
  have h0 : Z * NormedSpace.exp (((0 : ℝ) : ℂ) • x) = Z := by simp [NormedSpace.exp_zero]
  exact hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (hasDerivAt_mul_exp_smul_zero Z x) h0.symm

def rdzK {j : ℕ} (κ : ℂ → MJ j → E) : rdzPZ j → E := fun q => κ q.1 (Matrix.of q.2)

theorem rdz_slice {j : ℕ} (κ : ℂ → MJ j → E) (τ₀ : ℂ) (Z₀ : MJ j)
    (hd : DifferentiableAt ℝ (rdzK κ) (τ₀, Z₀)) (v : ℂ) :
    fderiv ℝ (fun τ : ℂ => κ τ Z₀) τ₀ v = fderiv ℝ (rdzK κ) (τ₀, Z₀) (v, 0) := by
  have hι : HasFDerivAt (fun τ : ℂ => ((τ, Z₀) : rdzPZ j)) ((ContinuousLinearMap.id ℝ ℂ).prod 0) τ₀ :=
    (hasFDerivAt_id τ₀).prodMk (hasFDerivAt_const _ τ₀)
  have h2 := (hd.hasFDerivAt.comp τ₀ hι).fderiv
  rw [show (fun τ : ℂ => κ τ Z₀) = rdzK κ ∘ (fun τ : ℂ => ((τ, Z₀) : rdzPZ j)) from rfl, h2]
  rfl

def rdzH {j : ℕ} (κ : ℂ → MJ j → E) (c s : ℂ) : rdzPZ j → E := fun p =>
  c • (fderiv ℝ (rdzK κ) p (1, 0) + s • fderiv ℝ (rdzK κ) p (Complex.I, 0))

theorem rdz_dz_eq (f : ℂ → E) (τ : ℂ) :
    PBP.dz f τ = (1 / 2 : ℂ) • (fderiv ℝ f τ 1 + (-Complex.I) • fderiv ℝ f τ Complex.I) := by
  simp only [PBP.dz, neg_smul, sub_eq_add_neg]

theorem rdz_dzb_eq (f : ℂ → E) (τ : ℂ) :
    PBP.dzb f τ = (1 / 2 : ℂ) • (fderiv ℝ f τ 1 + Complex.I • fderiv ℝ f τ Complex.I) := rfl

theorem rdz_H_eq {j : ℕ} (κ : ℂ → MJ j → E) (c s : ℂ) (τ₀ : ℂ) (Z₀ : MJ j)
    (hd : DifferentiableAt ℝ (rdzK κ) (τ₀, Z₀)) :
    c • (fderiv ℝ (fun τ : ℂ => κ τ Z₀) τ₀ 1 + s • fderiv ℝ (fun τ : ℂ => κ τ Z₀) τ₀ Complex.I) =
      rdzH κ c s (τ₀, Z₀) := by
  rw [rdz_slice κ τ₀ Z₀ hd, rdz_slice κ τ₀ Z₀ hd]
  rfl

theorem rdz_H_smooth {j : ℕ} (κ : ℂ → MJ j → E) (c s : ℂ) {U : Set (rdzPZ j)} (hU : IsOpen U)
    (hK : ContDiffOn ℝ ∞ (rdzK κ) U) : ContDiffOn ℝ ∞ (rdzH κ c s) U := by
  have hK1 : ContDiffOn ℝ ∞ (fderiv ℝ (rdzK κ)) U := hK.fderiv_of_isOpen (m := ∞) hU withTop_enat_infty_add_one_le_infty
  exact ((hK1.clm_apply contDiffOn_const).add ((hK1.clm_apply contDiffOn_const).const_smul s)).const_smul c

theorem rdz_par {j : ℕ} (x : MJ j) : ParamCommF (E := E) (fun h => RdV x h) := by
  intro U κ hU _ hK
  have hKc : ContDiffOn ℝ ∞ (rdzK κ) U := hK
  have hKd : ∀ q ∈ U, DifferentiableAt ℝ (rdzK κ) q := fun q hq => rdz_da hU hKc hq
  have hK1 : ContDiffOn ℝ ∞ (fderiv ℝ (rdzK κ)) U := hKc.fderiv_of_isOpen (m := ∞) hU withTop_enat_infty_add_one_le_infty
  have hG1 : ContDiffOn ℝ ∞ (fun q => fderiv ℝ (rdzK κ) q (rdzLd x q)) U :=
    hK1.clm_apply (rdzLd x).contDiff.contDiffOn
  have hrd : ∀ q ∈ U, RdV x (κ q.1) (Matrix.of q.2) = fderiv ℝ (rdzK κ) q (rdzLd x q) :=
    fun q hq => rdz_rd x (rdzK κ) q.1 (Matrix.of q.2) (hKd q hq)
  refine ⟨hG1.congr fun q hq => hrd q hq, fun q hq => ?_⟩
  have hKa : ContDiffAt ℝ ∞ (rdzK κ) q := hKc.contDiffAt (hU.mem_nhds hq)
  have hc : DifferentiableAt ℝ (fderiv ℝ (rdzK κ)) q :=
    (hKa.fderiv_right (m := ∞) withTop_enat_infty_add_one_le_infty).differentiableAt (by simp)
  have hsym : IsSymmSndFDerivAt ℝ (rdzK κ) q := hKa.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
  have hG1d : HasFDerivAt (fun p => fderiv ℝ (rdzK κ) p (rdzLd x p))
      ((fderiv ℝ (rdzK κ) q).comp (rdzLd x) + (fderiv ℝ (fderiv ℝ (rdzK κ)) q).flip (rdzLd x q)) q :=
    hc.hasFDerivAt.clm_apply (rdzLd x).hasFDerivAt
  have hL : ∀ v : ℂ, fderiv ℝ (fun τ => RdV x (κ τ) (Matrix.of q.2)) q.1 v =
      fderiv ℝ (fderiv ℝ (rdzK κ)) q (v, 0) (rdzLd x q) := by
    intro v
    have hev : (fun τ => RdV x (κ τ) (Matrix.of q.2)) =ᶠ[𝓝 q.1]
        (fun τ => fderiv ℝ (rdzK κ) (τ, q.2) (rdzLd x (τ, q.2))) := by
      have hc' : ContinuousAt (fun τ : ℂ => ((τ, q.2) : rdzPZ j)) q.1 :=
        (continuous_id.prodMk continuous_const).continuousAt
      filter_upwards [hc'.preimage_mem_nhds (hU.mem_nhds hq)] with τ hτ
      exact hrd (τ, q.2) hτ
    have hι : HasFDerivAt (fun τ : ℂ => ((τ, q.2) : rdzPZ j)) ((ContinuousLinearMap.id ℝ ℂ).prod 0) q.1 :=
      (hasFDerivAt_id q.1).prodMk (hasFDerivAt_const _ q.1)
    rw [hev.fderiv_eq, show (fun τ => fderiv ℝ (rdzK κ) (τ, q.2) (rdzLd x (τ, q.2))) =
      (fun p => fderiv ℝ (rdzK κ) p (rdzLd x p)) ∘ (fun τ : ℂ => ((τ, q.2) : rdzPZ j)) from rfl,
      (hG1d.comp q.1 hι).fderiv]
    simp [rdzLd_inl]
  have hR : ∀ c s : ℂ, RdV x (fun Z => c • (fderiv ℝ (fun τ : ℂ => κ τ Z) q.1 1 +
      s • fderiv ℝ (fun τ : ℂ => κ τ Z) q.1 Complex.I)) (Matrix.of q.2) =
      c • (fderiv ℝ (fderiv ℝ (rdzK κ)) q (rdzLd x q) (1, 0) +
        s • fderiv ℝ (fderiv ℝ (rdzK κ)) q (rdzLd x q) (Complex.I, 0)) := by
    intro c s
    have hev : (fun Z : MJ j => c • (fderiv ℝ (fun τ : ℂ => κ τ Z) q.1 1 +
        s • fderiv ℝ (fun τ : ℂ => κ τ Z) q.1 Complex.I)) =ᶠ[𝓝 (Matrix.of q.2)]
        (fun Z : MJ j => rdzH κ c s (q.1, Z)) := by
      have hc' : ContinuousAt (fun Z : MJ j => ((q.1, Z) : rdzPZ j)) (Matrix.of q.2) :=
        (continuous_const.prodMk continuous_id).continuousAt
      filter_upwards [hc'.preimage_mem_nhds (hU.mem_nhds hq)] with Z hZ
      exact rdz_H_eq κ c s q.1 Z (hKd _ hZ)
    have hH : HasFDerivAt (rdzH κ c s)
        (c • (((fderiv ℝ (rdzK κ) q).comp 0 + (fderiv ℝ (fderiv ℝ (rdzK κ)) q).flip ((1, 0) : rdzPZ j)) +
          s • ((fderiv ℝ (rdzK κ) q).comp 0 +
            (fderiv ℝ (fderiv ℝ (rdzK κ)) q).flip ((Complex.I, 0) : rdzPZ j)))) q :=
      ((hc.hasFDerivAt.clm_apply (hasFDerivAt_const ((1, 0) : rdzPZ j) q)).add
        ((hc.hasFDerivAt.clm_apply (hasFDerivAt_const ((Complex.I, 0) : rdzPZ j) q)).const_smul s)).const_smul c
    rw [rdz_loc x _ _ _ hev, rdz_rd x (rdzH κ c s) q.1 (Matrix.of q.2) hH.differentiableAt,
      show ((q.1, Matrix.of q.2) : rdzPZ j) = q from rfl, hH.fderiv]
    simp
  have hS : ∀ v : ℂ, fderiv ℝ (fderiv ℝ (rdzK κ)) q (v, 0) (rdzLd x q) =
      fderiv ℝ (fderiv ℝ (rdzK κ)) q (rdzLd x q) (v, 0) := fun v => hsym _ _
  refine ⟨?_, ?_⟩
  · simp only [rdz_dz_eq]
    rw [hR, hL, hL, hS, hS]
  · simp only [rdz_dzb_eq]
    rw [hR, hL, hL, hS, hS]

end Formalism.FourierDecayAlt.P.WirtingerOperators

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.FourierDecayAlt.P.WirtingerOperators

theorem right_derivative_operator_class : WirtingerOperators.ZOpRd := by
  intro j E _ _ x
  refine ⟨fun h₁ h₂ Z h => rdz_loc x h₁ h₂ Z h, ?_, ?_, rdz_par x⟩
  · intro V h₁ h₂ hV _ c1 c2 Z hZ
    have d1 := rdz_hd x (rdz_da hV c1 hZ)
    have d2 := rdz_hd x (rdz_da hV c2 hZ)
    simp only [RdV]
    rw [d1.deriv, d2.deriv]
    exact (d1.add d2).deriv
  · intro V c h hV _ ch Z hZ
    have d := rdz_hd x (rdz_da hV ch hZ)
    simp only [RdV]
    rw [d.deriv]
    exact (d.const_smul c).deriv

theorem wirtinger_slice_smooth : WirtingerOperators.DzSlice := by
  intro j E _ _ U κ hU hK τ₀
  have hKc : ContDiffOn ℝ ∞ (rdzK κ) U := hK
  have hι : ContDiff ℝ ∞ (fun Z : MJ j => ((τ₀, Z) : rdzPZ j)) := contDiff_const.prodMk contDiff_id
  have key : ∀ c s : ℂ, ContDiffOn ℝ ∞ (fun Z : MJ j => c • (fderiv ℝ (fun τ : ℂ => κ τ Z) τ₀ 1 +
      s • fderiv ℝ (fun τ : ℂ => κ τ Z) τ₀ Complex.I)) {Z : MJ j | (τ₀, (Z : Fin j → Fin j → ℂ)) ∈ U} := by
    intro c s
    refine ((rdz_H_smooth κ c s hU hKc).comp hι.contDiffOn (fun Z hZ => hZ)).congr fun Z hZ => ?_
    exact rdz_H_eq κ c s τ₀ Z (rdz_da hU hKc hZ)
  refine ⟨?_, ?_⟩
  · simp only [rdz_dz_eq]
    exact key _ _
  · simp only [rdz_dzb_eq]
    exact key _ _

end Formalism.FourierDecayAlt.P
end
end

section

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.WirtingerOperators.LeviExponential

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates

theorem fsym (m n : ℕ) (i : Fin (m + n)) : finSumFinEquiv.symm i =
    if h : i.val < m then Sum.inl ⟨i, h⟩ else Sum.inr ⟨i - m, by omega⟩ := by
  split_ifs with h
  · rw [Equiv.symm_apply_eq]; ext; simp
  · rw [Equiv.symm_apply_eq]; ext; simp; omega

theorem block_two_apply {p s : ℕ} (A : Matrix (Fin p) (Fin p) ℂ) (B' : Matrix (Fin p) (Fin s) ℂ)
    (C : Matrix (Fin s) (Fin p) ℂ) (D' : Matrix (Fin s) (Fin s) ℂ) (a b : Fin (p + s)) :
    U.blk2 A B' C D' a b =
      if ha : a.val < p then (if hb : b.val < p then A ⟨a, ha⟩ ⟨b, hb⟩ else B' ⟨a, ha⟩ ⟨b - p, by omega⟩)
      else (if hb : b.val < p then C ⟨a - p, by omega⟩ ⟨b, hb⟩ else D' ⟨a - p, by omega⟩ ⟨b - p, by omega⟩) := by
  simp only [U.blk2, Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [fsym, fsym]
  split_ifs <;> rfl

theorem w_mul_apply {d : ℕ} {ι : Type*} (M : Matrix (Fin d) ι ℂ) (a : Fin d) (b : ι) :
    (G.wMat d * M) a b = M a.rev b := by
  simp [G.wMat, Matrix.mul_apply]

theorem mul_w_apply {d : ℕ} {ι : Type*} [Fintype ι] (M : Matrix ι (Fin d) ℂ) (a : ι) (b : Fin d) :
    (M * G.wMat d) a b = M a b.rev := by
  simp only [G.wMat, Matrix.mul_apply, Matrix.of_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single b.rev]
  · simp
  · intro c _ hc; rw [if_neg]; intro h; apply hc; rw [h, Fin.rev_rev]
  · simp

theorem xcongr {j : ℕ} (x : MJ j) {a a' b b' : Fin j} (ha : a.val = a'.val) (hb : b.val = b'.val) :
    x a b = x a' b' := by
  rw [Fin.ext ha, Fin.ext hb]

theorem levi_eq {k r j : ℕ} (hj : j + 1 ≤ r) (x : MJ j) :
    levi k r j x = D.castM (by omega : j + 1 + (r - (j + 1)) = r)
      (U.blk3 (k := k) (j := j + 1) (ρ := r - (j + 1)) (U.blk2 x 0 0 0) 0 0 0 0 0 0 0
        (G.wMat (j + 1) * U.blk2 (-xᴴ) 0 0 0 * G.wMat (j + 1))) := by
  ext p q
  obtain ⟨X, hX⟩ := (U.eB k (j + 1) (r - (j + 1))).surjective (Fin.cast (by omega) p)
  obtain ⟨Y, hY⟩ := (U.eB k (j + 1) (r - (j + 1))).surjective (Fin.cast (by omega) q)
  have hp : p.val = (U.eB k (j + 1) (r - (j + 1)) X).val := by rw [hX]; rfl
  have hq : q.val = (U.eB k (j + 1) (r - (j + 1)) Y).val := by rw [hY]; rfl
  have e : ∀ M : B.Mat k (j + 1 + (r - (j + 1))),
      D.castM (by omega : j + 1 + (r - (j + 1)) = r) M p q =
        M (U.eB k (j + 1) (r - (j + 1)) X) (U.eB k (j + 1) (r - (j + 1)) Y) := by
    intro M
    rw [hX, hY]; rfl
  rw [e, Ux4.block3_apply]
  rcases X with ((a | v) | a) <;> rcases Y with ((b | w) | b) <;>
    simp only [Ux4.block_index_first_val_eq, Ux4.block_index_middle_val_eq, Ux4.block_index_last_val_eq] at hp hq <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl,
      Matrix.fromCols_apply_inr, Matrix.zero_apply, levi, Matrix.of_apply, block_two_apply, w_mul_apply, mul_w_apply,
      Matrix.mul_assoc, Fin.val_rev, Matrix.neg_apply, Matrix.conjTranspose_apply] <;>
    split_ifs <;> first | rfl | (exfalso; omega) | skip
  all_goals first
    | exact xcongr x (by simp; omega) (by simp; omega)
    | (simp only [Complex.star_def]; congr 2; exact xcongr x (by simp; omega) (by simp; omega))

end Formalism.FourierDecayAlt.P.WirtingerOperators.LeviExponential
end
end
