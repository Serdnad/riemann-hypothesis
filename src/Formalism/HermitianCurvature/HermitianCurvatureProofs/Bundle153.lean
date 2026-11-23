module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle055
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormalFormOrderZeroOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle056
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTConnGaugeB
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle139
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle082
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle108
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.BesselUnipotentEquivHolds
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle094
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle079
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle045
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle083
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle140
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle110
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle086
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle029
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle131
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle126
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle027
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle135
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCCurvPoly
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle134
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle145
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle112
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle125
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGaugeVLem
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagonalTransferAction
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle141
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle099
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt MeasureTheory

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.SSAdjH

open Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.NFx4

noncomputable section

section pt

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem hsVec_zero' : B.hsVec (0 : Wq →L[ℂ] Wp) = 0 := by
  unfold B.hsVec
  ext i
  simp

theorem rawR_smul (P : M.Par) (μsec : ℂ → Matrix (Fin (P.k + 1)) (Fin (P.k + 1)) ℂ) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (a : ℂ) (Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (ρ : M.Ty P) (q : MA.Qp P.r P.TT) :
    rawR P μsec e (a • Z) ρ q = a * rawR P μsec e Z ρ q := by
  have hs : ∀ A : Wq →L[ℂ] Wp, B.hsVec (a • A) = a • B.hsVec A := by
    intro A
    unfold B.hsVec
    ext i
    simp
  simp only [rawR, Pi.smul_apply, hs, inner_smul_right]
  ring

theorem rawR_zero (P : M.Par) (μsec : ℂ → Matrix (Fin (P.k + 1)) (Fin (P.k + 1)) ℂ) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (ρ : M.Ty P) (q : MA.Qp P.r P.TT) :
    rawR P μsec e (0 : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ q = 0 := by
  simp only [rawR, Pi.zero_apply, hsVec_zero', inner_zero_right, mul_zero]

theorem smQ_sum_apply (P : M.Par) (x : M.Ty P → MA.SmQ P.r P.TT) (q : MA.Qp P.r P.TT) :
    ((∑ σ, x σ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q = ∑ σ, ((x σ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q := by
  simp only [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]

variable (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk2 : 2 ≤ P.k)
  (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (he : IsFrameB P Bs e)

include hpl hk2 he

theorem kap_pt (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) (hk : KapF P Bs d e)
    (f : M.Ty P → ℂ) (Z : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (σ : M.Ty P) (q : MA.Qp P.r P.TT) :
    rawR P Bs.μsec e (((d.κ f).1 Z : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ q =
      f σ * rawR P Bs.μsec e (Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ q := by
  have h := congrArg (fun x : M.Ty P → MA.SmQ P.r P.TT => ((x σ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q) (hk f Z)
  simp only [actA_kap] at h
  rw [← SSTr.trR_apply P Bs hpl hk2 e he, h, ← SSTr.trR_apply P Bs hpl hk2 e he]
  rfl

theorem ss_pt (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) (s t : ℕ → M.Ty P → M.Ty P → ℂ → ℂ)
    (hst : SmST P s t) (hL : SSLoc P Bs d e s t) {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1))
    (Z : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (ρ' : M.Ty P) (q : MA.Qp P.r P.TT) :
    rawR P Bs.μsec e (((d.SS l).1 Z : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ' q =
        ∑ σ, s l ρ' σ q.1.2 * rawR P Bs.μsec e (Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ q ∧
      rawR P Bs.μsec e (((star (d.SS l)).1 Z : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ' q =
        ∑ σ, t l ρ' σ q.1.2 * rawR P Bs.μsec e (Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ q := by
  obtain ⟨h1, h2⟩ := hL l hl Z ρ'
  constructor
  · rw [← SSTr.trR_apply P Bs hpl hk2 e he, h1, smQ_sum_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Subalgebra.coe_mul, Pi.mul_apply, fnZ_val P (hst l ρ' σ).1, SSTr.trR_apply P Bs hpl hk2 e he]
  · rw [← SSTr.trR_apply P Bs hpl hk2 e he, h2, smQ_sum_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Subalgebra.coe_mul, Pi.mul_apply, fnZ_val P (hst l ρ' σ).2, SSTr.trR_apply P Bs hpl hk2 e he]

theorem sec_expand (Z : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (q : MA.Qp P.r P.TT) :
    (Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1 (NF.muZ P.k P.r Bs.μsec q.1.2) =
      ∑ σ, ((((wR P.k P.TT q.1.2)⁻¹ : ℝ) : ℂ) * rawR P Bs.μsec e (Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ q) •
        e σ q.1.2 := by
  have hq : (q.1 : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := (SSTr.qr_iff P Bs hpl _).2 q.2
  have hmem := Formalism.FourierDecayAlt.P.radical_reduction_mem Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' (SSTr.radBase P Bs hpl)
    (Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) Z.2
  have hF := hmem.2.1 _ hq
  simp only [NF.radR, Set.indicator_of_mem hq] at hF
  have hζ : P.TT < Complex.normSq q.1.2 := q.2.2
  obtain ⟨-, -, hexp⟩ := he.2 q.1.2 hζ
  conv_lhs => rw [hexp _ hF]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  have hw := SSTr.wR_pos P hζ
  simp only [rawR]
  rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hw.ne', Complex.ofReal_one, one_mul]

theorem hs_pair (Z W : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (q : MA.Qp P.r P.TT) :
    (((wR P.k P.TT q.1.2 ^ 2 : ℝ)) : ℂ) *
        inner ℂ (B.hsVec ((Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1 (NF.muZ P.k P.r Bs.μsec q.1.2)))
          (B.hsVec ((W : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1 (NF.muZ P.k P.r Bs.μsec q.1.2))) =
      ∑ σ, star (rawR P Bs.μsec e (Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ q) *
        rawR P Bs.μsec e (W : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ q := by
  rw [sec_expand P Bs hpl hk2 e he W q, SSTr.hsVec_sum, inner_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hw := (SSTr.wR_pos P (q.2.2 : P.TT < Complex.normSq q.1.2)).ne'
  rw [hsVec_smul, inner_smul_right]
  have hc : star (rawR P Bs.μsec e (Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ q) =
      ((wR P.k P.TT q.1.2 : ℝ) : ℂ) *
        inner ℂ (B.hsVec ((Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1 (NF.muZ P.k P.r Bs.μsec q.1.2))) (B.hsVec (e σ q.1.2)) := by
    simp only [rawR]
    rw [star_mul', Complex.star_def, Complex.conj_ofReal, inner_conj_symm]
  rw [hc]
  have hw' : ((wR P.k P.TT q.1.2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hw
  push_cast
  field_simp

theorem exists_proj (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) (hk : KapF P Bs d e)
    (f : ℂ → ℂ) (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Ann P)) (ρ : M.Ty P) :
    ∃ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
      (∀ σ (q : MA.Qp P.r P.TT), rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ q =
        (if σ = ρ then 1 else 0) * f q.1.2) ∧ (NO.Pj d ρ).1 Φ = Φ := by
  obtain ⟨Φ0, hΦ0, -⟩ := SSTr.exists_tr P Bs hpl hk2 e he (fun _ => fnZ P f)
  refine ⟨(NO.Pj d ρ).1 Φ0, fun σ q => ?_, ?_⟩
  · show rawR P Bs.μsec e
        (((d.κ (fun ρ' => if ρ' = ρ then (1 : ℂ) else 0)).1 Φ0 : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
          Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ q = _
    rw [kap_pt P Bs hpl hk2 e he d hk, ← SSTr.trR_apply P Bs hpl hk2 e he, hΦ0, fnZ_val P hf]
  · show ((NO.Pj d ρ) * (NO.Pj d ρ)).1 Φ0 = _
    rw [NO.Pj_idem]

end pt

theorem pt_of_tests {U : Set ℂ} (hU : IsOpen U) {H : ℂ → ℂ} (hH : ContinuousOn H U)
    (h : ∀ φ : ℂ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∫ ζ, φ ζ • H ζ = 0) :
    ∀ ζ0 ∈ U, H ζ0 = 0 := by
  have hae := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume) (hH.locallyIntegrableOn hU.measurableSet) h
  intro ζ0 hζ0
  by_contra hne
  have hc : ContinuousAt H ζ0 := hH.continuousAt (hU.mem_nhds hζ0)
  have hev : ∀ᶠ x in nhds ζ0, H x ≠ 0 ∧ x ∈ U := (hc.eventually_ne hne).and (hU.mem_nhds hζ0)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have hpos := Metric.measure_ball_pos (volume : Measure ℂ) ζ0 hδ
  rw [ae_iff] at hae
  apply hpos.ne'
  apply measure_mono_null _ hae
  intro x hx
  have := hball x hx
  simp only [Set.mem_setOf_eq, not_forall, exists_prop]
  exact ⟨this.2, this.1⟩

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.SSAdjH
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.LT

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

section agree

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def agNN (p : B.SS k r) : B.SS k r :=
  ((Matrix.of.symm (1 : B.Mat k r), p.1.2), (Matrix.of.symm (1 : B.Mat k r), p.2.2))

def agN (p : B.SS k r) : B.SS k r :=
  ((Matrix.of.symm (1 : B.Mat k r), p.1.2), (Matrix.of.symm (1 : B.Mat k r), Matrix.of.symm (1 : B.Mat k r)))

theorem agNN_inSS (Bs : B.RealPlaceData k r Wp Wq) {p : B.SS k r} (hp : Bs.inSS p) : Bs.inSS (agNN p) := by
  obtain ⟨_, h2, _, h4⟩ := hp
  refine ⟨?_, h2, ?_, h4⟩
  · show Matrix.of (Matrix.of.symm (1 : B.Mat k r)) ∈ _
    rw [Equiv.apply_symm_apply]; exact Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _
  · show Matrix.of (Matrix.of.symm (1 : B.Mat k r)) ∈ _
    rw [Equiv.apply_symm_apply]; exact Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _

theorem agN_inSS (Bs : B.RealPlaceData k r Wp Wq) {p : B.SS k r} (hp : Bs.inSS p) : Bs.inSS (agN p) := by
  obtain ⟨_, h2, _, _⟩ := hp
  refine ⟨?_, h2, ?_, ?_⟩
  · show Matrix.of (Matrix.of.symm (1 : B.Mat k r)) ∈ _
    rw [Equiv.apply_symm_apply]; exact Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _
  · show Matrix.of (Matrix.of.symm (1 : B.Mat k r)) ∈ _
    rw [Equiv.apply_symm_apply]; exact Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _
  · show Matrix.of (Matrix.of.symm (1 : B.Mat k r)) ∈ _
    rw [Equiv.apply_symm_apply]; exact WeylGroupFacts.mem_n_one

theorem sgs_agNN (p : B.SS k r) (g : B.Mat k r) :
    B.sgs (agNN p) g = (Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2 := by
  simp only [B.sgs, agNN, Equiv.apply_symm_apply, inv_one, one_mul, mul_one]

theorem sgs_agN (p : B.SS k r) (g : B.Mat k r) :
    B.sgs (agN p) g = (Matrix.of p.1.2)⁻¹ * g := by
  simp only [B.sgs, agN, Equiv.apply_symm_apply, inv_one, one_mul, mul_one]

theorem sgs_split (p : B.SS k r) (g : B.Mat k r) :
    B.sgs p g = (Matrix.of p.1.1)⁻¹ * ((Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2) * Matrix.of p.2.1 := by
  simp only [B.sgs, mul_assoc]

theorem agree_sgs (Bs : B.RealPlaceData k r Wp Wq) (f₁ f₂ : B.Mat k r → (Wq →L[ℂ] Wp))
    (hL₁ : ∀ g ∈ JF.Om k r Bs.z Bs.z', ∀ n ∈ Nset k r, f₁ (n * g) = psi k r Bs.z cStd n • f₁ g)
    (hR₁ : ∀ g ∈ JF.Om k r Bs.z Bs.z', ∀ n ∈ Nset k r, f₁ (g * n) = psi k r Bs.z' cStd n • f₁ g)
    (hU₁ : ∀ g ∈ JF.Om k r Bs.z Bs.z', ∀ h ∈ UWset k r Bs.z, ∀ h' ∈ UWset k r Bs.z',
      f₁ (h * g * h') = (Bs.π h).comp ((f₁ g).comp (Bs.π' h')))
    (hL₂ : ∀ g ∈ JF.Om k r Bs.z Bs.z', ∀ n ∈ Nset k r, f₂ (n * g) = psi k r Bs.z cStd n • f₂ g)
    (hR₂ : ∀ g ∈ JF.Om k r Bs.z Bs.z', ∀ n ∈ Nset k r, f₂ (g * n) = psi k r Bs.z' cStd n • f₂ g)
    (hU₂ : ∀ g ∈ JF.Om k r Bs.z Bs.z', ∀ h ∈ UWset k r Bs.z, ∀ h' ∈ UWset k r Bs.z',
      f₂ (h * g * h') = (Bs.π h).comp ((f₂ g).comp (Bs.π' h')))
    {p : B.SS k r} (hp : Bs.inSS p) {x : B.Mat k r} (hx : x ∈ JF.Om k r Bs.z Bs.z') (he : f₁ x = f₂ x) :
    f₁ (B.sgs p x) = f₂ (B.sgs p x) := by
  have hp' := hp
  obtain ⟨h1, h2, h3, h4⟩ := hp'
  have hx1 : (Matrix.of p.1.2)⁻¹ * x ∈ JF.Om k r Bs.z Bs.z' := by
    rw [← sgs_agN p x]; exact Formalism.FourierDecayAlt.P.PositiveOrbitOpen.sgs_Om Bs (agN_inSS Bs hp) hx
  have hx2 : (Matrix.of p.1.2)⁻¹ * x * Matrix.of p.2.2 ∈ JF.Om k r Bs.z Bs.z' := by
    rw [← sgs_agNN p x]; exact Formalism.FourierDecayAlt.P.PositiveOrbitOpen.sgs_Om Bs (agNN_inSS Bs hp) hx
  have hn := WeylGroupFacts.mem_n_inv h2
  have hu := Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv h1
  rw [sgs_split, hU₁ _ hx2 _ hu _ h3, hU₂ _ hx2 _ hu _ h3, hR₁ _ hx1 _ h4, hR₂ _ hx1 _ h4,
    hL₁ _ hx _ hn, hL₂ _ hx _ hn, he]

variable [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem agreement_on_domain_holds : AgreeOm := by
  intro k r Wp Wq _ _ _ _ _ _ Bs J F U hJ hag g hg hgU
  obtain ⟨p, hp, q, hq, rfl⟩ := Formalism.FourierDecayAlt.P.psiOnto_true k r Wp Wq Bs g hg
  have hgq := Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom Bs hq
  have hGq : Gf k r Bs.z Bs.z' (B.gq Bs q) ∈ U := by
    have e : Gf k r Bs.z Bs.z' (B.sgs p (B.gq Bs q)) = Gf k r Bs.z Bs.z' (B.gq Bs q) := by
      unfold Gf
      rw [Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs Bs hp, Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs Bs hp]
    rw [← e]; exact hgU
  have hD : ∀ y ∈ JF.Om k r Bs.z Bs.z', y ∈ Q.Glev k r 0 ∩ {g | 0 < Gf k r Bs.z Bs.z' g ∧
      ∀ a : Fin r, Dmin k r Bs.z Bs.z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0} := fun y hy =>
    ⟨Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hy.1, Formalism.FourierDecayAlt.P.CutMP.jdc_of_om _ _ hy⟩
  have hNl : ∀ n ∈ Formalism.QuantumDeterminants.Nset k r, n ∈ Q.Nlev k r 0 := fun n hn => ⟨hn, Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hn.1⟩
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bs.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bs.haarN
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bs.haarW'
  have hN := bessel_unipotent_equiv_holds Wp Wq k r Bs.z Bs.z' cStd Bs.π Bs.π' Bs.μW Bs.μN Bs.μW' F Bs.z_mem Bs.z'_mem
    Bs.haarN.conc (fun n₀ h => Bs.haarN.left n₀ h)
  refine agree_sgs Bs J (B.JF Bs F)
    (fun y hy n hn => hJ.2.1 y (hD y hy) n (hNl n hn))
    (fun y hy n hn => hJ.2.2.1 y (hD y hy) n (hNl n hn))
    (fun y hy h hh h' hh' => hJ.2.2.2 y (hD y hy) h hh h' hh')
    (fun y _ n hn => ?_) (fun y _ n hn => ?_)
    (fun y _ h hh h' hh' => Formalism.FourierDecayAlt.P5.jf_uEquiv Bs F y hh hh')
    hp hgq (hag q hq hGq)
  · have e := hN y n hn 1 WeylGroupFacts.mem_n_one
    rw [Matrix.mul_one, Formalism.FourierDecayAlt.P.BesselCapelliCommutation.psi_one Bs.z'_mem, mul_one] at e
    exact e
  · have e := hN y 1 WeylGroupFacts.mem_n_one n hn
    rw [Matrix.one_mul, Formalism.FourierDecayAlt.P.BesselCapelliCommutation.psi_one Bs.z_mem, one_mul] at e
    exact e

end agree

end Formalism.FourierDecayAlt.P.CutMP.JA.LT

end
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem curvature_polynomial_holds : GTCCurvPoly := curvature_polynomial_of_scalar curvature_scalar_holds

theorem curvature_identity_holds : GTCCurvId :=
  gTCCurvId_of_cut curvature_polynomial_holds curvature_radial_torus_holds curvature_block_form_holds

theorem top_normal_form_of_curvature : GTRTopNF := gTRTopNF_of_curvPoly curvature_polynomial_holds

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.GQ

noncomputable section

open Classical

theorem lagrange_all {T : Type} [Fintype T] (K : (T → ℂ) → Prop) (hc : ∀ c : ℂ, K fun _ => c)
    (hadd : ∀ f g, K f → K g → K (f + g)) (hmul : ∀ f g, K f → K g → K (f * g))
    (x : T → ℂ) (hx : K x) (hinj : Function.Injective x) : ∀ f, K f := by
  classical
  have hsum : ∀ (ι : Type) (s : Finset ι) (g : ι → T → ℂ), (∀ i ∈ s, K (g i)) → K (∑ i ∈ s, g i) := by
    intro ι s g
    refine Finset.induction_on s ?_ ?_
    · intro _
      rw [Finset.sum_empty]
      exact hc 0
    · intro a s ha ih hg
      rw [Finset.sum_insert ha]
      exact hadd _ _ (hg a (Finset.mem_insert_self a s)) (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))
  have hprod : ∀ (ι : Type) (s : Finset ι) (g : ι → T → ℂ), (∀ i ∈ s, K (g i)) → K (∏ i ∈ s, g i) := by
    intro ι s g
    refine Finset.induction_on s ?_ ?_
    · intro _
      rw [Finset.prod_empty]
      exact hc 1
    · intro a s ha ih hg
      rw [Finset.prod_insert ha]
      exact hmul _ _ (hg a (Finset.mem_insert_self a s)) (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))
  intro f
  have key : f = ∑ t, (fun _ : T => f t) *
      ∏ s ∈ Finset.univ.erase t, ((x + fun _ : T => -x s) * fun _ : T => (x t - x s)⁻¹) := by
    funext u
    simp only [Finset.sum_apply, Pi.mul_apply, Finset.prod_apply, Pi.add_apply]
    rw [Finset.sum_eq_single u]
    · rw [Finset.prod_eq_one, mul_one]
      intro s hs
      have hne : x u - x s ≠ 0 := sub_ne_zero.mpr (fun h => (Finset.ne_of_mem_erase hs) (hinj h).symm)
      rw [← sub_eq_add_neg, mul_inv_cancel₀ hne]
    · intro t _ htu
      rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm htu, Finset.mem_univ u⟩), mul_zero]
      rw [add_neg_cancel, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ u) h
  rw [key]
  exact hsum _ _ _ fun t _ => hmul _ _ (hc _) (hprod _ _ _ fun s _ => hmul _ _ (hadd _ _ hx (hc _)) (hc _))

section main

open Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.GT

theorem quadratic_kappa_identity : GQKap := by
  intro Wp Wq _ _ _ _ _ _ P Bs hk X d hA e he hQ
  obtain ⟨hpl, hL, -, -, -⟩ := hA
  have hsm : ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') ρ,
      rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ ∈ MA.smSub P.r P.TT :=
    fun Φ ρ => radial_space_smoothness Wp Wq P Bs hpl hk e he Φ ρ
  have hP : P.OK := hpl.1
  have hz := fun q => (sec_pt P Bs hpl q).2
  have hgg : ∀ q : MA.Qp P.r P.TT, ((ggS P : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q =
      q.1.2 * (starRingEnd ℂ) q.1.2 - (P.TT : ℂ) := fun q => by
    show ((MA.coordQ (r := P.r) (TT := P.TT) M.vz : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q *
        ((MA.coordQ (r := P.r) (TT := P.TT) M.vzb : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q - (P.TT : ℂ) = _
    rw [coordQ_vz, coordQ_vzb]
  have hggv : ∀ q : MA.Qp P.r P.TT, ((ggS P : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q ≠ 0 :=
    fun q => by rw [hgg]; exact gg_ne P q
  have hGG : ∀ q : MA.Qp P.r P.TT, ((Q.GGl P.k P.r Bs.z Bs.z' (NF.muZ P.k P.r Bs.μsec q.1.2) : ℝ) : ℂ) =
      q.1.2 * (starRingEnd ℂ) q.1.2 - (P.TT : ℂ) := fun q => by
    rw [Complex.mul_conj]
    unfold Q.GGl
    rw [hz q, hpl.2.2.2.1, hpl.2.2.2.2.1]
    have hT : ((P.TT : ℝ) : ℂ) = (P.T : ℂ) * (P.T' : ℂ) := by
      show (((P.T * P.T' : ℝ)) : ℂ) = _
      push_cast; ring
    rw [hT]
    push_cast
    ring
  have hsc : ∀ (w : (MA.DQ P).Pr) (f : M.Ty P → MA.SmQ P.r P.TT),
      MA.actA P (MA.sc P (MA.DQ P) w) f = fun ρ => w.1 (f ρ) := VLem.actA_sc P
  have hGGi : Intw P Bs e d.L.GGi (MA.ggiA P (MA.DQ P)) := by
    intro Φ
    rw [hL.2.2.2.2.2.2.2.2.2.2.2.1]
    refine (trR_fn P Bs hpl X e 5 (Ring.inverse (ggS P))
      (fun q => by rw [inverse_apply _ hggv]; exact inv_ne_zero (hggv q))
      (fun q => by rw [inverse_apply _ hggv, hgg]; show ((Q.GGl _ _ _ _ _ : ℝ) : ℂ)⁻¹ = _; rw [hGG q]) Φ).trans ?_
    exact (hsc ((MA.DQ P).ggiP P.TT) (trR P Bs e Φ)).symm
  have hTT : 0 ≤ P.TT := (mul_pos hP.T_pos hP.T'_pos).le
  haveI : Fact ((MA.DQ P).Laws P.TT) := ⟨Formalism.FourierDecayAlt.P.analytic_laws P.r P.TT hTT⟩
  have hx : ∀ Y : ℝ, Intw P Bs e (d.κ fun ρ => M.xC P ρ (Y : ℂ)) (MA.kap P (MA.DQ P) fun ρ => M.xC P ρ (Y : ℂ)) := by
    intro Y
    have h1 := intw_mul hsm hGGi (hQ Y 1 1)
    have e1 : d.L.GGi * d.QQ (Y : ℂ) 1 1 = d.κ fun ρ => M.xC P ρ (Y : ℂ) := by
      show d.L.GGi * (d.L.GG * d.x (Y : ℂ)) = _
      rw [← mul_assoc, d.L.GGi_GG, one_mul]; rfl
    have e2 : MA.ggiA P (MA.DQ P) * MA.QQr P (MA.DQ P) (Y : ℂ) 1 1 = MA.kap P (MA.DQ P) fun ρ => M.xC P ρ (Y : ℂ) := by
      show MA.ggiA P (MA.DQ P) * (MA.ggA P (MA.DQ P) * MA.xA P (MA.DQ P) (Y : ℂ)) = _
      rw [← mul_assoc, Formalism.FourierDecayAlt.P.MAx1.D5.ggi_gg, one_mul]; rfl
    rw [e1, e2] at h1; exact h1
  obtain ⟨Y₀, hinj⟩ := Formalism.FourierDecayAlt.P5.Kfp.sep_real hP
  refine lagrange_all (fun f => Intw P Bs e (d.κ f) (MA.kap P (MA.DQ P) f)) ?_ ?_ ?_ _ (hx Y₀) hinj
  · intro c
    have e1 : d.κ (fun _ => c) = algebraMap ℂ _ c := d.κ.commutes c
    have e2 : MA.kap P (MA.DQ P) (fun _ => c) = algebraMap ℂ _ c := (MA.kap P (MA.DQ P)).commutes c
    show Intw P Bs e (d.κ (fun _ => c)) (MA.kap P (MA.DQ P) (fun _ => c))
    rw [e1, e2]; exact intw_alg hsm c
  · intro f g hf hg
    show Intw P Bs e (d.κ (f + g)) (MA.kap P (MA.DQ P) (f + g))
    rw [map_add (f := _), map_add (f := _)]; exact intw_add hsm hf hg
  · intro f g hf hg
    show Intw P Bs e (d.κ (f * g)) (MA.kap P (MA.DQ P) (f * g))
    rw [map_mul, map_mul]; exact intw_mul hsm hf hg

end main

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.GQ
end

section

noncomputable section

namespace Formalism.FourierDecayAlt.P

theorem good_function_leaf : CutFP.GoodFnLeaf :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ hT X j => ParameterFamilyAlgebra.good_fn hT X j

theorem good_transfer_leaf : CutFP.GoodTLeaf :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ hOm hS X Y a b => ParameterFamilyAlgebra.good_alt_bis hOm hS X Y a b

theorem frame_parameter_regularity : PBI.FrameParam :=
  CutFP.frameParam_of good_function_leaf good_transfer_leaf

end Formalism.FourierDecayAlt.P
end
end
