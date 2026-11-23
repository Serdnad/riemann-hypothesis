module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle074
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle102
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreKLExistsOf
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreKLIsoAlg
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle116
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagonalTransferAction
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle133
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle094
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle111
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle082
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ParametersUPrimeForULower
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle131
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GNMulRpow
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle038
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle134
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BaseIndexConstantInjective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.HermitianCurvature.FrameExists2

@[expose] public section

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.PRho.GL

noncomputable section

namespace AsmPf

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

variable [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem hsVec_smul (c : ℂ) (A : Wq →L[ℂ] Wp) : B.hsVec (c • A) = c • B.hsVec A := by
  ext i
  simp [B.hsVec]

theorem base (hR : GLRight) (hLf : GLLeft) (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k)
    (hF : Gauge.IsFrameB P Bs e)
    (hQQ : ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)), Gauge.FamR P Bs Dc Φ →
      ∀ (Y : ℝ) (a b : Fin 2) (ρ : M.Ty P),
        MA.toSm P (Gauge.rawR P Bs.μsec e (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) a b Φ) ρ) =
          MA.actA P (MA.QQr P (MA.DQ P) (Y : ℂ) a b) (fun ρ' => MA.toSm P (Gauge.rawR P Bs.μsec e Φ ρ')) ρ)
    (ζ : ℂ) (hζ : P.TT < Complex.normSq ζ) (ρ : M.Ty P) (Fr : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ)
    (hFr : Q.IsFrameOf P.k P.r [Bs.z, SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ] Fr) (w : ℂ) (x : Wq) :
    Q.capRep P.k P.r Bs.π Fr w (e ρ ζ x) = M.xC P ρ (w - ((P.k : ℂ) - 2) / 2) • e ρ ζ x := by
  obtain ⟨hOK, hz, hz', hTz, hTz', -, -⟩ := id hpl
  have hζ' : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ := by
    rw [hTz, hTz']; exact hζ
  obtain ⟨hFr', hpass⟩ := hLf Wp Wq P Bs hpl hk ζ hζ Fr hFr
  have hq : ((fun _ => (1 : ℂ)), ζ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨fun _ => one_ne_zero, hζ'⟩
  obtain ⟨-, hg, hG⟩ := Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' Bs.sec hq
  have hEx := Gauge.GC.lie_existence_of_iso_group Gauge.GC.KLIso.lie_algebra_isomorphism_holds Gauge.GC.lie_group_realization
  obtain ⟨E, hEfib, hEeig, hE0⟩ := hEx Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hpl hk _ hg hG.ne' _ hFr' ρ
  have hEF : E ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ :=
    fun p hp => hEfib p.1 hp.1 p.2 hp.2.1 hp.2.2
  have hgl' := (Formalism.FourierDecayAlt.P.frame_general_linear Wq P.k P.r (P.k - 1) Bs.z' Bs.π'
    (fun a => (NF.muZ P.k P.r Bs.μsec ζ)⁻¹ *ᵥ Fr a) ⟨Bs.π'_rep, Bs.π'_cont⟩
    (Formalism.FourierDecayAlt.P.Qx8.frame_sub hFr' (by simp))).2
  have hEc : ∀ (Y : ℂ) (v : Wq), E (Q.capRep P.k P.r Bs.π'
      (fun a => (NF.muZ P.k P.r Bs.μsec ζ)⁻¹ *ᵥ Fr a) (Y + ((P.k : ℂ) - 2) / 2) v) = M.xC P ρ Y • E v := by
    intro Y v
    rw [hgl']
    exact hEeig Y v
  obtain ⟨Y₀, hY₀⟩ := Formalism.FourierDecayAlt.P5.Kfp.sep_real hOK
  have horth : ∀ σ, σ ≠ ρ → inner ℂ (B.hsVec (e σ ζ)) (B.hsVec E) = 0 := by
    intro σ hσ
    have h := hR Wp Wq P Bs e hpl hk hF hQQ ζ hζ _ hFr' E hEF Y₀ (M.xC P ρ (Y₀ : ℂ) • E)
      (fun v => by rw [hEc, ContinuousLinearMap.smul_apply]) σ
    rw [hsVec_smul, inner_smul_right] at h
    have h2 : (M.xC P ρ (Y₀ : ℂ) - M.xC P σ (Y₀ : ℂ)) * inner ℂ (B.hsVec (e σ ζ)) (B.hsVec E) = 0 := by
      rw [sub_mul, h, sub_self]
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact absurd (hY₀ (sub_eq_zero.1 h3)).symm hσ
    · exact h3
  have hexp := (hF.2 ζ hζ).2.2 E hEF
  have hE1 : E = inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec E) • e ρ ζ := by
    conv_lhs => rw [hexp]
    rw [Finset.sum_eq_single ρ (fun σ _ hσ => by rw [horth σ hσ, zero_smul])
      (fun h => absurd (Finset.mem_univ ρ) h)]
  have hc0 : inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec E) ≠ 0 := by
    intro h0
    apply hE0
    rw [hE1, h0, zero_smul]
  have heig : ∀ (Y : ℂ) (v : Wq), e ρ ζ (Q.capRep P.k P.r Bs.π'
      (fun a => (NF.muZ P.k P.r Bs.μsec ζ)⁻¹ *ᵥ Fr a) (Y + ((P.k : ℂ) - 2) / 2) v) = M.xC P ρ Y • e ρ ζ v := by
    intro Y v
    have h := hEc Y v
    generalize hcdef : inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec E) = c at hE1 hc0
    rw [hE1] at h
    simp only [ContinuousLinearMap.smul_apply] at h
    rw [smul_comm (M.xC P ρ Y) c] at h
    exact smul_right_injective Wp hc0 h
  rw [hpass (e ρ ζ) ((hF.2 ζ hζ).1 ρ) w x]
  have hw : w = (w - ((P.k : ℂ) - 2) / 2) + ((P.k : ℂ) - 2) / 2 := by ring
  conv_lhs => rw [hw]
  exact heig _ x

end AsmPf

theorem gaugeLines_of_cut : GaugeLinesOfCut := by
  intro hR hL Cc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ v e hH hk ζ hζ ρ Fr hFr w x
  obtain ⟨hB, hFrame, -, hQQ⟩ := hH
  have hpl := (hB.1.2.2.2.1.2 v).2.2.2.1
  exact AsmPf.base hR hL (D.parOf S v) (T v).base e hpl hk hFrame hQQ ζ hζ ρ Fr hFr w x

end

end Formalism.FourierDecayAlt.P.CutMP.JA.PRho.GL
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC

noncomputable section

theorem line_nonvanishing_holds : LineNonzero := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl hk Pr hPr π ζ hζ
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
  have hEx := Gauge.GC.lie_existence_of_iso_group Gauge.GC.KLIso.lie_algebra_isomorphism_holds Gauge.GC.lie_group_realization
  obtain ⟨E, hEfib, hEeig, hE0⟩ := hEx Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hpl hk _ hg hGG.ne' _ hFr' π
  have hEF : E ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ :=
    fun p hp => hEfib p.1 hp.1 p.2 hp.2.1 hp.2.2
  have hgl' := (Formalism.FourierDecayAlt.P.frame_general_linear Wq P.k P.r (P.k - 1) Bs.z' Bs.π'
    (fun a => μ⁻¹ *ᵥ Fr a) ⟨Bs.π'_rep, Bs.π'_cont⟩
    (Formalism.FourierDecayAlt.P.Qx8.frame_sub hFr' (by simp))).2
  have hπrep : Qr.IsRepW P.k P.r Bs.z Bs.π := ⟨Bs.π_rep, Bs.π_cont⟩
  refine ⟨E, hEF, ?_, hE0⟩
  have hpos : 0 < PRho.nrmW P.k P.r Bs.z ν := by
    unfold PRho.nrmW
    rw [hνfix, hνν]; simp
  have hrange := ((hPr.2.2 ν hpos).2.2.2 π)
  ext v
  rw [ContinuousLinearMap.comp_apply]
  refine (hrange (E v)).2 ?_
  intro Fr2 hFr2 w
  rw [hνfix] at hFr2
  rw [Topx1.typ_frame_change P.k P.r (by omega) Bs.z ν Bs.π Fr2 Fr hz hT hνW hνz hνν hπrep hFr2 hFr w (E v),
    hpass E hEF w v, hgl']
  have hw : w = (w - ((P.k : ℂ) - 2) / 2) + ((P.k : ℂ) - 2) / 2 := by ring
  conv_lhs => rw [hw]
  exact hEeig _ v

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC
end

section

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

theorem hphi_meas : Measurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
    (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r)) :=
  meas_hn measurable_id

theorem quad_inner {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mx k r → (H →L[ℂ] H)}
    (hds : PI.UpqRep.IsDSHpk k r ε lam σ) (w0 : H) {e0 : Mx k r → ℂ} (he0 : Continuous e0)
    (hee0 : ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), e0 g = ⟪w0, σ g w0⟫_ℂ)
    {γ : Mx k r} (hγ : γ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    {μW μN μW' : Measure (Formalism.QuantumDeterminants.Mt k r)} [SigmaFinite μW] [SigmaFinite μN] [SigmaFinite μW']
    (hS1 : muSof μW μN {x | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} = 0)
    (hS2 : muSof μW' μN {x | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} = 0)
    {zz zz' : Formalism.QuantumDeterminants.Mt k r} (hz : Matrix.of zz ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hz' : Matrix.of zz' ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    ∫⁻ s, ∫⁻ s', ‖⟪σ (Matrix.of zz) w0, σ (Matrix.of s * γ * (Matrix.of s')⁻¹) (σ (Matrix.of zz') w0)⟫_ℂ‖ₑ
      ∂(muSof μW' μN) ∂(muSof μW μN) = abelian₂ e0 γ (μW.prod μN) (μW'.prod μN) zz zz' := by
  have hae1 : ∀ᵐ s ∂(muSof μW μN), Matrix.of s ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
    rw [ae_iff]; simpa using hS1
  have hae2 : ∀ᵐ s ∂(muSof μW' μN), Matrix.of s ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
    rw [ae_iff]; simpa using hS2
  have hJ : Measurable (fun t : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      ‖e0 ((Matrix.of zz)⁻¹ * Matrix.of t.1 * γ * (Matrix.of t.2)⁻¹ * Matrix.of zz')‖ₑ) := by
    have mγ : Measurable (fun _ : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of.symm γ : Formalism.QuantumDeterminants.Mt k r)) :=
      measurable_const
    exact measurable_enorm_composition he0 (meas_matmul (meas_matmul (meas_matmul (meas_matmul (meas_inv (meas_const_mt zz))
      measurable_fst) mγ) (meas_inv measurable_snd)) (meas_const_mt zz'))
  calc ∫⁻ s, ∫⁻ s', ‖⟪σ (Matrix.of zz) w0, σ (Matrix.of s * γ * (Matrix.of s')⁻¹) (σ (Matrix.of zz') w0)⟫_ℂ‖ₑ
        ∂(muSof μW' μN) ∂(muSof μW μN)
      = ∫⁻ s, ∫⁻ s', ‖e0 ((Matrix.of zz)⁻¹ * Matrix.of s * γ * (Matrix.of s')⁻¹ * Matrix.of zz')‖ₑ
          ∂(muSof μW' μN) ∂(muSof μW μN) := by
        apply lintegral_congr_ae
        filter_upwards [hae1] with s hs
        apply lintegral_congr_ae
        filter_upwards [hae2] with s' hs'
        have hY : Matrix.of s * γ * (Matrix.of s')⁻¹ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
          DDSmoothness.uh_mul (DDSmoothness.uh_mul hs hγ) (MatrixMultiplicationContinuity.uh_inv hs').1
        have hM : (Matrix.of zz)⁻¹ * (Matrix.of s * γ * (Matrix.of s')⁻¹) * Matrix.of zz' ∈
            Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
          DDSmoothness.uh_mul (DDSmoothness.uh_mul (MatrixMultiplicationContinuity.uh_inv hz).1 hY) hz'
        rw [coef_eq hds hz hY hz', ← hee0 _ hM]
        simp only [Matrix.mul_assoc]
    _ = ∫⁻ p, ∫⁻ q, ‖e0 ((Matrix.of zz)⁻¹ * (Matrix.of p.1 * Matrix.of p.2) * γ *
          (Matrix.of q.1 * Matrix.of q.2)⁻¹ * Matrix.of zz')‖ₑ ∂(μW'.prod μN) ∂(μW.prod μN) := by
        unfold muSof
        rw [lintegral_map (hJ.lintegral_prod_right' (ν := (μW'.prod μN).map
          (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j :
            Formalism.QuantumDeterminants.Mt k r)))) hphi_meas]
        apply lintegral_congr
        intro p
        have hK : Measurable (fun y : Formalism.QuantumDeterminants.Mt k r =>
            ‖e0 ((Matrix.of zz)⁻¹ * Matrix.of (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r) *
              γ * (Matrix.of y)⁻¹ * Matrix.of zz')‖ₑ) := by
          have mc : Measurable (fun _ : Formalism.QuantumDeterminants.Mt k r => (fun i j => ((Matrix.of zz)⁻¹ *
              Matrix.of (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r) * γ) i j :
                Formalism.QuantumDeterminants.Mt k r)) := measurable_const
          exact measurable_enorm_composition he0 (meas_matmul (meas_matmul mc (meas_inv measurable_id)) (meas_const_mt zz'))
        show ∫⁻ y, ‖e0 ((Matrix.of zz)⁻¹ * Matrix.of (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j :
            Formalism.QuantumDeterminants.Mt k r) * γ * (Matrix.of y)⁻¹ * Matrix.of zz')‖ₑ ∂((μW'.prod μN).map
              (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
                (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r))) = _
        rw [lintegral_map hK hphi_meas]
        rfl
    _ = abelian₂ e0 γ (μW.prod μN) (μW'.prod μN) zz zz' := rfl

theorem quad_inner1 {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mx k r → (H →L[ℂ] H)}
    (hds : PI.UpqRep.IsDSHpk k r ε lam σ) (w0 : H) {e0 : Mx k r → ℂ} (he0 : Continuous e0)
    (hee0 : ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), e0 g = ⟪w0, σ g w0⟫_ℂ)
    {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)} [SigmaFinite μW] [SigmaFinite μN]
    (hS1 : muSof μW μN {x | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} = 0)
    {zz zz' : Formalism.QuantumDeterminants.Mt k r} (hz : Matrix.of zz ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hz' : Matrix.of zz' ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    ∫⁻ s, ‖⟪σ (Matrix.of zz) w0, σ (Matrix.of s) (σ (Matrix.of zz') w0)⟫_ℂ‖ₑ ∂(muSof μW μN) =
      Lam1 e0 (μW.prod μN) zz zz' := by
  have hae1 : ∀ᵐ s ∂(muSof μW μN), Matrix.of s ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
    rw [ae_iff]; simpa using hS1
  have hJ : Measurable (fun t : Formalism.QuantumDeterminants.Mt k r =>
      ‖e0 ((Matrix.of zz)⁻¹ * Matrix.of t * Matrix.of zz')‖ₑ) :=
    measurable_enorm_composition he0 (meas_matmul (meas_matmul (meas_inv (meas_const_mt zz)) measurable_id) (meas_const_mt zz'))
  calc ∫⁻ s, ‖⟪σ (Matrix.of zz) w0, σ (Matrix.of s) (σ (Matrix.of zz') w0)⟫_ℂ‖ₑ ∂(muSof μW μN)
      = ∫⁻ s, ‖e0 ((Matrix.of zz)⁻¹ * Matrix.of s * Matrix.of zz')‖ₑ ∂(muSof μW μN) := by
        apply lintegral_congr_ae
        filter_upwards [hae1] with s hs
        have hM : (Matrix.of zz)⁻¹ * Matrix.of s * Matrix.of zz' ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
          DDSmoothness.uh_mul (DDSmoothness.uh_mul (MatrixMultiplicationContinuity.uh_inv hz).1 hs) hz'
        rw [coef_eq hds hz hs hz', ← hee0 _ hM]
    _ = Lam1 e0 (μW.prod μN) zz zz' := by
        unfold muSof Lam1
        rw [lintegral_map hJ hphi_meas]
        rfl

end Formalism.FourierDecayAlt.P.S3dx4
end
end

section

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

theorem norm_two_sided_translate_growth_bound (hNI : NormInv) {e0 : Mx k r → ℂ} {C0 a b : ℝ}
    (hb0e : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖e0 y‖ ≤ C0 * B.gN y ^ (-a))
    (hb0 : 0 ≤ b) (hba : b ≤ a) {x A y : Mx k r} (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hA : A ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (hy : y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    ‖e0 (x⁻¹ * A * y)‖ₑ ≤ ENNReal.ofReal (|C0| * (B.gN x * B.gN y) ^ b) * ‖B.gN A ^ (-b)‖ₑ := by
  have hxi := (MatrixMultiplicationContinuity.uh_inv hx).1
  have hM : x⁻¹ * A * y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul (DDSmoothness.uh_mul hxi hA) hy
  have h1 : 1 ≤ B.gN (x⁻¹ * A * y) := ((hNI k r).2 _ hM).2
  have hAp : 0 ≤ B.gN A ^ (-b) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hxy : 0 ≤ (B.gN x * B.gN y) ^ b := Real.rpow_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) _
  rw [Real.enorm_eq_ofReal hAp, ← ENNReal.ofReal_mul (mul_nonneg (abs_nonneg _) hxy), ← ofReal_norm]
  apply ENNReal.ofReal_le_ofReal
  calc ‖e0 (x⁻¹ * A * y)‖ ≤ C0 * B.gN (x⁻¹ * A * y) ^ (-a) := hb0e _ hM
    _ ≤ |C0| * B.gN (x⁻¹ * A * y) ^ (-a) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg (by linarith) _)
    _ ≤ |C0| * B.gN (x⁻¹ * A * y) ^ (-b) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h1 (by linarith)) (abs_nonneg _)
    _ ≤ |C0| * ((B.gN x * B.gN y) ^ b * B.gN A ^ (-b)) :=
        mul_le_mul_of_nonneg_left (gN_sandwich hNI hx hA hy hb0) (abs_nonneg _)
    _ = |C0| * (B.gN x * B.gN y) ^ b * B.gN A ^ (-b) := by ring

theorem lam_bound (hNI : NormInv) {e0 : Mx k r → ℂ} {C0 a b : ℝ}
    (hb0e : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖e0 y‖ ≤ C0 * B.gN y ^ (-a))
    (hb0 : 0 ≤ b) (hba : b ≤ a) {γ : Mx k r} (hγ : γ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    {μp μq : Measure (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)}
    (hp : ∀ᵐ p ∂μp, Matrix.of p.1 * Matrix.of p.2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hq : ∀ᵐ q ∂μq, Matrix.of q.1 * Matrix.of q.2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    {x y : Formalism.QuantumDeterminants.Mt k r} (hx : Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hy : Matrix.of y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    abelian₂ e0 γ μp μq x y ≤ ENNReal.ofReal (|C0| * (B.gN (Matrix.of x) * B.gN (Matrix.of y)) ^ b) *
      ∫⁻ p, ∫⁻ q, ‖B.gN ((Matrix.of p.1 * Matrix.of p.2) * γ * (Matrix.of q.1 * Matrix.of q.2)⁻¹) ^ (-b)‖ₑ ∂μq ∂μp := by
  unfold abelian₂
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [hp] with p hpp
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [hq] with q hqq
  have hQi := (MatrixMultiplicationContinuity.uh_inv hqq).1
  have hA : (Matrix.of p.1 * Matrix.of p.2) * γ * (Matrix.of q.1 * Matrix.of q.2)⁻¹ ∈
      Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul (DDSmoothness.uh_mul hpp hγ) hQi
  have e : (Matrix.of x)⁻¹ * (Matrix.of p.1 * Matrix.of p.2) * γ * (Matrix.of q.1 * Matrix.of q.2)⁻¹ *
      Matrix.of y = (Matrix.of x)⁻¹ * ((Matrix.of p.1 * Matrix.of p.2) * γ * (Matrix.of q.1 * Matrix.of q.2)⁻¹) *
      Matrix.of y := by simp only [Matrix.mul_assoc]
  rw [e]
  exact norm_two_sided_translate_growth_bound hNI hb0e hb0 hba hx hA hy

theorem lambda_integral_bound (hNI : NormInv) {e0 : Mx k r → ℂ} {C0 a b : ℝ}
    (hb0e : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖e0 y‖ ≤ C0 * B.gN y ^ (-a))
    (hb0 : 0 ≤ b) (hba : b ≤ a) {μp : Measure (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)}
    (hp : ∀ᵐ p ∂μp, Matrix.of p.1 * Matrix.of p.2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    {x y : Formalism.QuantumDeterminants.Mt k r} (hx : Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hy : Matrix.of y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    Lam1 e0 μp x y ≤ ENNReal.ofReal (|C0| * (B.gN (Matrix.of x) * B.gN (Matrix.of y)) ^ b) *
      ∫⁻ p, ‖B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-b)‖ₑ ∂μp := by
  unfold Lam1
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [hp] with p hpp
  exact norm_two_sided_translate_growth_bound hNI hb0e hb0 hba hx hpp hy

end Formalism.FourierDecayAlt.P.S3dx4
end
end

section

open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.LevelPointCoordinates

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.Qx5

def RuleOfEq : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ)
    (Φ : Q.Mx k r → E) (g : Q.Mx k r), inWb k r z' →
    (∀ n ∈ QuantumDeterminants.Nset k r, Φ (g * n) = psi k r z' cStd n • Φ g) →
    ∀ p q, C3.InNp k r p q → Q.EH k r p q Φ g = C3.dpsiP k r z' p q • Φ g

def AdjoinNL : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r j : ℕ) (hj : j + 1 ≤ r) (z : Fin (2 * r + k + 1) → ℂ)
    (Dm : Set (Q.Mx k r)) (hD : IsOpen Dm),
    (∀ g ∈ Q.Glev k r 0 ∩ Dm, ∀ a : Fin j → ℂ, nL k r j hj a * g ∈ Dm) →
    ∀ x ∈ Algebra.adjoin ℂ (Set.range fun pq : Fin (2 * r + k + 1) × Fin (2 * r + k + 1) =>
        (PBG.E0 (E := E) hD pq.1 pq.2 : Module.End ℂ (Formalism.FourierDecayAlt.P.Qx5.VS k r 0 Dm E))),
    ∀ v : Formalism.FourierDecayAlt.P.Qx5.VS k r 0 Dm E,
      (∀ g ∈ Q.Glev k r 0 ∩ Dm, ∀ a : Fin j → ℂ,
        (v : Q.Mx k r → E) (nL k r j hj a * g) = psi k r z cStd (nL k r j hj a) • (v : Q.Mx k r → E) g) →
      ∀ g ∈ Q.Glev k r 0 ∩ Dm, ∀ a : Fin j → ℂ,
        ((x v : Formalism.FourierDecayAlt.P.Qx5.VS k r 0 Dm E) : Q.Mx k r → E) (nL k r j hj a * g) =
          psi k r z cStd (nL k r j hj a) • ((x v : Formalism.FourierDecayAlt.P.Qx5.VS k r 0 Dm E) : Q.Mx k r → E) g

end Formalism.FourierDecayAlt.P.LevelPointCoordinates
end
end
