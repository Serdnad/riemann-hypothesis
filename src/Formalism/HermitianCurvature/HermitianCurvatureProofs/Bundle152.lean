module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle055
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle139
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle056
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle087
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle045
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCSecMove
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle112
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGenTransferKPt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle144
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle133
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle094
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle111
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle082
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle135
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ParametersUPrimeForULower
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheSectionStab
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.HermitianCurvature.FrameExists2

@[expose] public section

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def qOne (P : M.Par) (ζ : ℂ) (hζ : ζ ∈ Ann P) : MA.Qp P.r P.TT :=
  ⟨(fun _ => (1 : ℂ), ζ), ⟨fun _ => one_ne_zero, hζ⟩⟩

theorem kap_orth (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π')
    (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) (hyp : GTHyp P Bs X d)
    (e e0 : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (he : IsFrameB P Bs e) (hk : KapF P Bs d e)
    (he0 : IsFrameB P Bs e0) (hk0 : KapF P Bs d e0) (ρ σ : M.Ty P) (hσ : σ ≠ ρ) (ζ : ℂ) (hζ : ζ ∈ Ann P) :
    inner ℂ (B.hsVec (e σ ζ)) (B.hsVec (e0 ρ ζ)) = 0 := by
  have hpl := hyp.1
  have hk2 := hyp.2.1
  let F : M.Ty P → MA.SmQ P.r P.TT := fun τ => if τ = ρ then fnZ P (fun _ => (1 : ℂ)) else 0
  obtain ⟨Φ, hΦ, hΦv⟩ := SSTr.exists_tr P Bs hpl hk2 e0 he0 F
  let f : M.Ty P → ℂ := fun τ => if τ = ρ then 1 else 0
  have hfix : (d.κ f).1 Φ = Φ := by
    apply SSTr.trR_inj P Bs hpl hk2 e0 he0
    rw [hk0 f Φ, hΦ]
    funext τ
    rw [actA_kap]
    by_cases h : τ = ρ
    · simp [f, h]
    · simp [f, F, h]
  have hz : trR P Bs e Φ σ = 0 := by
    have h := congrFun (hk f Φ) σ
    rw [hfix, actA_kap] at h
    rw [h]
    simp [f, hσ]
  have hq := congrArg (fun g : MA.SmQ P.r P.TT => (g : MA.Qp P.r P.TT → ℂ) (qOne P ζ hζ)) hz
  simp only [ZeroMemClass.coe_zero, Pi.zero_apply] at hq
  rw [SSTr.trR_apply P Bs hpl hk2 e he Φ σ, rawR, hΦv] at hq
  have h1 : ((F ρ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) (qOne P ζ hζ) = 1 := by
    simp only [F, if_pos rfl, fnZ_eq_mk P (contDiffOn_const (c := (1 : ℂ)))]
  have hsum : inner ℂ (B.hsVec (e σ ζ)) (B.hsVec (∑ τ, ((((wR P.k P.TT ζ)⁻¹ : ℝ) : ℂ) *
      ((F τ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) (qOne P ζ hζ)) • e0 τ ζ)) =
      (((wR P.k P.TT ζ)⁻¹ : ℝ) : ℂ) * inner ℂ (B.hsVec (e σ ζ)) (B.hsVec (e0 ρ ζ)) := by
    rw [SSTr.hsVec_sum, inner_sum, Finset.sum_eq_single ρ]
    · rw [hsVec_smul, inner_smul_right, h1, mul_one]
    · intro τ _ hτ
      simp only [F, if_neg hτ, ZeroMemClass.coe_zero, Pi.zero_apply, mul_zero, zero_smul]
      rw [← zero_smul ℂ (0 : Wq →L[ℂ] Wp), hsVec_smul, zero_smul, inner_zero_right]
    · intro h; exact absurd (Finset.mem_univ ρ) h
  have hw := SSTr.wR_pos P (ζ := ζ) hζ
  change ((wR P.k P.TT ζ : ℝ) : ℂ) * inner ℂ (B.hsVec (e σ ζ)) (B.hsVec (∑ τ, ((((wR P.k P.TT ζ)⁻¹ : ℝ) : ℂ) *
      ((F τ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) (qOne P ζ hζ)) • e0 τ ζ)) = 0 at hq
  rw [hsum, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hw.ne', Complex.ofReal_one, one_mul] at hq
  exact hq

def hsCLM : (Wq →L[ℂ] Wp) →L[ℝ] PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp) :=
  (LinearMap.toContinuousLinearMap (SSTr.hsL (Wp := Wp) (Wq := Wq))).restrictScalars ℝ

theorem hsCLM_apply (A : Wq →L[ℂ] Wp) : hsCLM A = B.hsVec A := rfl

theorem e0_eq (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π')
    (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) (hyp : GTHyp P Bs X d)
    (e e0 : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (he : IsFrameB P Bs e) (hk : KapF P Bs d e)
    (he0 : IsFrameB P Bs e0) (hk0 : KapF P Bs d e0) (ρ : M.Ty P) (ζ : ℂ) (hζ : ζ ∈ Ann P) :
    e0 ρ ζ = inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec (e0 ρ ζ)) • e ρ ζ := by
  obtain ⟨hfib0, -, -⟩ := (he0.2 ζ hζ)
  obtain ⟨-, -, hexp⟩ := he.2 ζ hζ
  conv_lhs => rw [hexp (e0 ρ ζ) (hfib0 ρ)]
  rw [Finset.sum_eq_single ρ]
  · intro σ _ hσ
    rw [kap_orth P Bs X d hyp e e0 he hk he0 hk0 ρ σ hσ ζ hζ, zero_smul]
  · intro h; exact absurd (Finset.mem_univ ρ) h

end

theorem phase_relation_holds : GTCPhaseRel := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hyp e e0 he hk he0 hk0
  refine ⟨fun ρ ζ => inner ℂ (B.hsVec (e0 ρ ζ)) (B.hsVec (e ρ ζ)), fun ρ => ⟨?_, ?_⟩, ?_⟩
  · have h1 := (hsCLM (Wp := Wp) (Wq := Wq)).contDiff.comp_contDiffOn (he0.1 ρ)
    have h2 := (hsCLM (Wp := Wp) (Wq := Wq)).contDiff.comp_contDiffOn (he.1 ρ)
    have h3 := h1.inner ℂ h2
    simp only [Function.comp_def, hsCLM_apply] at h3
    exact h3
  · intro ζ hζ
    have hrel := e0_eq P Bs X d hyp e0 e he0 hk0 he hk ρ ζ hζ
    have hn := ((he.2 ζ hζ).2.1 ρ ρ)
    rw [if_pos rfl] at hn
    set c := inner ℂ (B.hsVec (e0 ρ ζ)) (B.hsVec (e ρ ζ)) with hc
    have hn0 := ((he0.2 ζ hζ).2.1 ρ ρ)
    rw [if_pos rfl] at hn0
    rw [hrel, hsVec_smul, inner_smul_left, inner_smul_right, hn0, mul_one] at hn
    have h2 : ((‖c‖ ^ 2 : ℝ) : ℂ) = 1 := by
      rw [← hn, Complex.ofReal_pow, ← Complex.mul_conj', mul_comm]
    have h3 : ‖c‖ ^ 2 = 1 := by exact_mod_cast h2
    have h4 : 0 ≤ ‖c‖ := norm_nonneg c
    nlinarith [h3, h4]
  · intro ρ ζ hζ
    exact e0_eq P Bs X d hyp e0 e he0 hk0 he hk ρ ζ hζ

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem radial_gauge_move : GTRMove := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl hk μ0 h0 e0 he0
  have hz := Bs.z_mem
  have hz' := Bs.z'_mem
  have hT : Tz P.k P.r Bs.z = P.T := hpl.2.2.2.1
  have hT' : Tz P.k P.r Bs.z' = P.T' := hpl.2.2.2.2.1
  have hTT : ∀ ζ : ℂ, P.TT < Complex.normSq ζ → Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ := by
    intro ζ hζ
    rw [hT, hT']
    exact hζ
  set c1 : Fin P.r → ℂ := fun _ => 1 with hc1def
  have hc1 : c1 ∈ OmX P.r := fun _ => one_ne_zero

  have hRB : NF.RadBase P.k P.r Bs.z Bs.z' μ0 Bs.π Bs.π' :=
    ⟨Bs.k_pos, hz, hz', Bs.T_pos, Bs.T'_pos, h0, Bs.π_rep, Bs.π'_rep, Bs.π_cont, Bs.π'_cont⟩

  have hφ : ∀ ρ : M.Ty P, (NF.QR P.k P.r Bs.z Bs.z').indicator (fun q => e0 ρ q.2) ∈
      NF.RadSec P.k P.r Bs.z Bs.z' μ0 Bs.π Bs.π' := by
    intro ρ
    refine ⟨?_, ?_, ?_⟩
    · have hc : ContDiffOn ℝ ∞ (fun q : (Fin P.r → ℂ) × ℂ => e0 ρ q.2) (NF.QR P.k P.r Bs.z Bs.z') := by
        refine (he0.1 ρ).comp contDiff_snd.contDiffOn fun q hq => ?_
        show P.TT < Complex.normSq q.2
        have := hq.2
        rw [hT, hT'] at this
        exact this
      exact hc.congr fun q hq => Set.indicator_of_mem hq _
    · intro q hq
      rw [Set.indicator_of_mem hq]
      have hq2 : P.TT < Complex.normSq q.2 := by
        have := hq.2
        rw [hT, hT'] at this
        exact this
      exact (he0.2 q.2 hq2).1 ρ
    · intro q hq
      exact Set.indicator_of_notMem hq _
  choose Φr hΦr hrad using fun ρ => Formalism.FourierDecayAlt.P.radical_reduction_surjective Wp Wq P.k P.r Bs.z Bs.z' μ0 Bs.π Bs.π' hRB _ (hφ ρ)
  obtain ⟨e, he_def⟩ : ∃ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp),
      e = fun ρ ζ => (Φr ρ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c1 (NF.muZ P.k P.r Bs.μsec ζ) := ⟨_, rfl⟩

  have hdom : ∀ ζ : ℂ, P.TT < Complex.normSq ζ →
      (c1, NF.muZ P.k P.r Bs.μsec ζ) ∈ Q.DomR P.k P.r Bs.z Bs.z' :=
    fun ζ hζ => Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' Bs.sec (q := (c1, ζ)) ⟨hc1, hTT ζ hζ⟩
  have hdom0 : ∀ ζ : ℂ, P.TT < Complex.normSq ζ → (c1, NF.muZ P.k P.r μ0 ζ) ∈ Q.DomR P.k P.r Bs.z Bs.z' :=
    fun ζ hζ => Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' h0 (q := (c1, ζ)) ⟨hc1, hTT ζ hζ⟩
  have hdec : ∀ ζ : ℂ, P.TT < Complex.normSq ζ → ∃ h ∈ UWset P.k P.r Bs.z, ∃ h' ∈ UWset P.k P.r Bs.z',
      NF.muZ P.k P.r Bs.μsec ζ = h * NF.muZ P.k P.r μ0 ζ * h' := by
    intro ζ hζ
    obtain ⟨h, hh, h', hh', he⟩ := Formalism.FourierDecayAlt.P.NFRadRedA.decomp Bs.k_pos hz hz' Bs.T_pos Bs.T'_pos h0
      (hdom ζ hζ).2.1 (hdom ζ hζ).2.2
    rw [Formalism.FourierDecayAlt.P.NFRadRedA.zeta_muZ hz hz' Bs.sec (hTT ζ hζ)] at he
    exact ⟨h, hh, h', hh', he⟩

  have hrad0 : ∀ ρ ζ, P.TT < Complex.normSq ζ → (Φr ρ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c1 (NF.muZ P.k P.r μ0 ζ) = e0 ρ ζ := by
    intro ρ ζ hζ
    have hq : (c1, ζ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨hc1, hTT ζ hζ⟩
    have h1 := congrFun (hrad ρ) (c1, ζ)
    unfold NF.radR at h1
    rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq] at h1
    exact h1

  have htr : ∀ ρ ζ, P.TT < Complex.normSq ζ → ∀ h ∈ UWset P.k P.r Bs.z, ∀ h' ∈ UWset P.k P.r Bs.z',
      NF.muZ P.k P.r Bs.μsec ζ = h * NF.muZ P.k P.r μ0 ζ * h' →
      e ρ ζ = (Bs.π h).comp ((e0 ρ ζ).comp (Bs.π' h')) := by
    intro ρ ζ hζ h hh h' hh' hd
    rw [he_def]
    show (Φr ρ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c1 (NF.muZ P.k P.r Bs.μsec ζ) = _
    rw [hd, ← hrad0 ρ ζ hζ]
    exact (hΦr ρ).2.2 (c1, NF.muZ P.k P.r μ0 ζ) (hdom0 ζ hζ) h hh h' hh'

  have hsmooth : ∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (e ρ) {ζ : ℂ | P.TT < Complex.normSq ζ} := by
    intro ρ
    rw [he_def]
    have hmZ : ContDiffOn ℝ ∞ (fun ζ : ℂ => (c1, NF.muZ P.k P.r Bs.μsec ζ)) {ζ : ℂ | P.TT < Complex.normSq ζ} :=
      contDiffOn_const.prodMk ((Formalism.FourierDecayAlt.P.NFRadRedA.muZ_contDiffOn Bs.sec).mono fun ζ hζ => hTT ζ hζ)
    have hopen : IsOpen {ζ : ℂ | P.TT < Complex.normSq ζ} :=
      isOpen_lt continuous_const Complex.continuous_normSq
    refine contDiffOn_of_locally_contDiffOn fun ζ₀ hζ₀ => ?_
    obtain ⟨U, F, hU, hx₀U, hF, hΦF⟩ := (hΦr ρ).2.1 _ (hdom ζ₀ hζ₀)
    refine ⟨{ζ : ℂ | P.TT < Complex.normSq ζ} ∩ (fun ζ : ℂ => (c1, NF.muZ P.k P.r Bs.μsec ζ)) ⁻¹' U,
      hmZ.continuousOn.isOpen_inter_preimage hopen hU, ⟨hζ₀, hx₀U⟩, ?_⟩
    have hc : ContDiffOn ℝ ∞ (fun ζ : ℂ => F (c1, NF.muZ P.k P.r Bs.μsec ζ))
        ({ζ : ℂ | P.TT < Complex.normSq ζ} ∩
          ({ζ : ℂ | P.TT < Complex.normSq ζ} ∩ (fun ζ : ℂ => (c1, NF.muZ P.k P.r Bs.μsec ζ)) ⁻¹' U)) :=
      hF.comp (hmZ.mono fun ζ hζ => hζ.1) fun ζ hζ => hζ.2.2
    exact hc.congr fun ζ hζ => hΦF _ hζ.2.2 (hdom ζ hζ.1).2.1

  have hrep := Bs.π_rep
  have hrep' := Bs.π'_rep
  have pmi : ∀ h ∈ UWset P.k P.r Bs.z, (Bs.π h).comp (Bs.π h⁻¹) = 1 := by
    intro h hh
    rw [← hrep.2 h hh h⁻¹ (Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh), Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul_inv hh, hrep.1]
  have pim' : ∀ h' ∈ UWset P.k P.r Bs.z', (Bs.π' h'⁻¹).comp (Bs.π' h') = 1 := by
    intro h' hh'
    rw [← hrep'.2 h'⁻¹ (Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh') h' hh', Formalism.FourierDecayAlt.P.NFRadRedS.uw_inv_mul hh', hrep'.1]

  have hframe : IsFrameB P Bs e := by
    refine ⟨hsmooth, fun ζ hζ => ⟨?_, ?_, ?_⟩⟩
    · intro ρ p hp
      rw [he_def]
      show (Bs.π p.1).comp (((Φr ρ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c1 (NF.muZ P.k P.r Bs.μsec ζ)).comp (Bs.π' p.2)) =
        (Φr ρ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c1 (NF.muZ P.k P.r Bs.μsec ζ)
      rw [← (hΦr ρ).2.2 (c1, NF.muZ P.k P.r Bs.μsec ζ) (hdom ζ hζ) p.1 hp.1 p.2 hp.2.1]
      show (Φr ρ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c1 (p.1 * NF.muZ P.k P.r Bs.μsec ζ * p.2) = _
      rw [hp.2.2]
    · intro ρ ρ'
      obtain ⟨h, hh, h', hh', hd⟩ := hdec ζ hζ
      rw [htr ρ ζ hζ h hh h' hh' hd, htr ρ' ζ hζ h hh h' hh' hd, sm_inner_conj Bs hh hh']
      exact (he0.2 ζ hζ).2.1 ρ ρ'
    · intro X hX
      obtain ⟨h, hh, h', hh', hd⟩ := hdec ζ hζ
      have hhi := Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh
      have hhi' := Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh'
      set X0 := (Bs.π h⁻¹).comp (X.comp (Bs.π' h'⁻¹)) with hX0def
      have e1 : ∀ Y : B.Mat P.k P.r, h⁻¹ * (h * Y) = Y := fun Y => by
        rw [← Matrix.mul_assoc, Formalism.FourierDecayAlt.P.NFRadRedS.uw_inv_mul hh, Matrix.one_mul]
      have e2 : ∀ Y : B.Mat P.k P.r, h' * (h'⁻¹ * Y) = Y := fun Y => by
        rw [← Matrix.mul_assoc, Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul_inv hh', Matrix.one_mul]
      have hX0 : X0 ∈ NF.Fib P.k P.r Bs.z Bs.z' μ0 Bs.π Bs.π' ζ := by
        intro p hp
        have hp1 := hp.1
        have hp2 := hp.2.1
        have hp3 := hp.2.2
        have ht1 : h * p.1 * h⁻¹ ∈ UWset P.k P.r Bs.z :=
          Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul (Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul hh hp1) hhi
        have ht2 : h'⁻¹ * p.2 * h' ∈ UWset P.k P.r Bs.z' :=
          Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul (Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul hhi' hp2) hh'
        have e3 : ∀ Y : B.Mat P.k P.r, p.1 * (NF.muZ P.k P.r μ0 ζ * (p.2 * Y)) = NF.muZ P.k P.r μ0 ζ * Y := by
          intro Y
          conv_rhs => rw [← hp3]
          simp only [Matrix.mul_assoc]
        have ht : (h * p.1 * h⁻¹, h'⁻¹ * p.2 * h') ∈ NF.Stab P.k P.r Bs.z Bs.z' Bs.μsec ζ := by
          refine ⟨ht1, ht2, ?_⟩
          show h * p.1 * h⁻¹ * NF.muZ P.k P.r Bs.μsec ζ * (h'⁻¹ * p.2 * h') = NF.muZ P.k P.r Bs.μsec ζ
          rw [hd]
          simp only [Matrix.mul_assoc, e1, e2, e3]
        have hXt := hX _ ht
        have hA : (Bs.π p.1).comp (Bs.π h⁻¹) = (Bs.π h⁻¹).comp (Bs.π (h * p.1 * h⁻¹)) := by
          rw [← hrep.2 _ hp1 _ hhi, ← hrep.2 _ hhi _ ht1]
          congr 1
          simp only [Matrix.mul_assoc, e1]
        have hB : (Bs.π' h'⁻¹).comp (Bs.π' p.2) = (Bs.π' (h'⁻¹ * p.2 * h')).comp (Bs.π' h'⁻¹) := by
          rw [← hrep'.2 _ hhi' _ hp2, ← hrep'.2 _ ht2 _ hhi']
          congr 1
          simp only [Matrix.mul_assoc, Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul_inv hh', Matrix.mul_one]
        calc (Bs.π p.1).comp (X0.comp (Bs.π' p.2))
            = ((Bs.π p.1).comp (Bs.π h⁻¹)).comp (X.comp ((Bs.π' h'⁻¹).comp (Bs.π' p.2))) := by
              simp only [hX0def, ContinuousLinearMap.comp_assoc]
          _ = ((Bs.π h⁻¹).comp (Bs.π (h * p.1 * h⁻¹))).comp
                (X.comp ((Bs.π' (h'⁻¹ * p.2 * h')).comp (Bs.π' h'⁻¹))) := by rw [hA, hB]
          _ = (Bs.π h⁻¹).comp (((Bs.π (h * p.1 * h⁻¹)).comp (X.comp (Bs.π' (h'⁻¹ * p.2 * h')))).comp
                (Bs.π' h'⁻¹)) := by simp only [ContinuousLinearMap.comp_assoc]
          _ = X0 := by rw [hXt]
      have hXX : X = (Bs.π h).comp (X0.comp (Bs.π' h')) := by
        have : (Bs.π h).comp (X0.comp (Bs.π' h')) =
            ((Bs.π h).comp (Bs.π h⁻¹)).comp (X.comp ((Bs.π' h'⁻¹).comp (Bs.π' h'))) := by
          simp only [hX0def, ContinuousLinearMap.comp_assoc]
        rw [this, pmi h hh, pim' h' hh']
        ext v
        rfl
      have hc : ∀ ρ, inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec X) = inner ℂ (B.hsVec (e0 ρ ζ)) (B.hsVec X0) := by
        intro ρ
        rw [htr ρ ζ hζ h hh h' hh' hd]
        conv_lhs => rw [hXX]
        exact sm_inner_conj Bs hh hh' _ _
      have hsp0 := (he0.2 ζ hζ).2.2 X0 hX0
      have hrhs : ∑ ρ, inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec X) • e ρ ζ =
          ∑ ρ, inner ℂ (B.hsVec (e0 ρ ζ)) (B.hsVec X0) • (Bs.π h).comp ((e0 ρ ζ).comp (Bs.π' h')) :=
        Finset.sum_congr rfl fun ρ _ => by rw [hc ρ, htr ρ ζ hζ h hh h' hh' hd]
      rw [hrhs]
      conv_lhs => rw [hXX, hsp0]
      ext v

      simp only [ContinuousLinearMap.comp_apply, FunLike.coe_sum, Finset.sum_apply,
      FunLike.coe_smul, Pi.smul_apply, map_sum, map_smul]
  refine ⟨e, hframe, fun Φ => ?_⟩
  funext ρ
  unfold trR
  congr 1
  funext q
  have hζ : P.TT < Complex.normSq q.1.2 := q.2.2
  obtain ⟨h, hh, h', hh', hd⟩ := hdec q.1.2 hζ
  unfold rawR
  congr 1
  rw [htr ρ q.1.2 hζ h hh h' hh' hd, hd]
  have hq : (q.1.1, NF.muZ P.k P.r μ0 q.1.2) ∈ Q.DomR P.k P.r Bs.z Bs.z' :=
    Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' h0 (q := (q.1.1, q.1.2)) ⟨q.2.1, hTT q.1.2 hζ⟩
  rw [Φ.2.2.2 _ hq h hh h' hh']
  exact sm_inner_conj Bs hh hh' _ _

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR

noncomputable section

theorem kappa_line_holds : KapLine := by
  intro Wp Wq _ _ _ _ _ _ P Bs hμs hk X d hA Pr hPr
  obtain ⟨hpl, hL, hS, hRel, hQQ⟩ := id hA
  have hcs := Formalism.FourierDecayAlt.P.TheSecStab.theSection_csec (k := P.k) (r := P.r) (by omega) Bs.z_mem Bs.z'_mem
    Bs.T_pos Bs.T'_pos
  rw [← hμs] at hcs
  have hH : Gauge.GC.GTHyp P Bs X d := ⟨hpl, hk, hcs, hL, hS, hRel, hQQ⟩
  obtain ⟨Qs, hK⟩ := Gauge.GC.gauge_kappa_pointwise_holds Wp Wq P Bs X d hH
  refine ⟨Qs, hK, ?_⟩
  intro ζ hζ Xf hXf ρ
  have hζT : P.TT < Complex.normSq ζ := hζ
  obtain ⟨hOK, hz, hz', hTz, hTz', -, -⟩ := id hpl
  have hζ' : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ := by
    rw [hTz, hTz']; exact hζT
  have hT := Bs.T_pos
  have hT' := Bs.T'_pos
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
  have hgl' := (Formalism.FourierDecayAlt.P.frame_general_linear Wq P.k P.r (P.k - 1) Bs.z' Bs.π'
    (fun a => μ⁻¹ *ᵥ Fr a) ⟨Bs.π'_rep, Bs.π'_cont⟩
    (Formalism.FourierDecayAlt.P.Qx8.frame_sub hFr' (by simp))).2
  have hπrep : Qr.IsRepW P.k P.r Bs.z Bs.π := ⟨Bs.π_rep, Bs.π_cont⟩
  have hpos : 0 < PRho.nrmW P.k P.r Bs.z ν := by
    unfold PRho.nrmW
    rw [hνfix, hνν]; simp

  set c0 : Fin P.r → ℂ := fun _ => 1 with hc0def
  have hq : ((c0, ζ) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨fun _ => one_ne_zero, hζ'⟩
  set φ : (Fin P.r → ℂ) × ℂ → (Wq →L[ℂ] Wp) := (NF.QR P.k P.r Bs.z Bs.z').indicator (fun _ => Xf) with hφdef
  have hφ : φ ∈ NF.RadSec P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' := by
    refine ⟨?_, ?_, ?_⟩
    · exact contDiffOn_const.congr (fun q hq' => Set.indicator_of_mem hq' _)
    · intro q hq'
      rw [hφdef, Set.indicator_of_mem hq']
      have hst := hcs.2 q.2 ζ hq'.2 hζ'
      intro p hp
      exact hXf p (hst ▸ hp)
    · intro q hq'
      exact Set.indicator_of_notMem hq' _
  have hbase : NF.RadBase P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' :=
    ⟨by omega, hz, hz', hT, hT', hcs.1, Bs.π_rep, Bs.π'_rep, Bs.π_cont, Bs.π'_cont⟩
  obtain ⟨Φ, hΦ, hΦr⟩ := Formalism.FourierDecayAlt.P.radical_reduction_surjective Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hbase φ hφ
  have hval : Φ c0 μ = Xf := by
    have h1 := congrFun hΦr (c0, ζ)
    simp only [NF.radR, Set.indicator_of_mem hq, hφdef] at h1
    exact h1
  have hx : (c0, μ) ∈ Q.DomR P.k P.r Bs.z Bs.z' := Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' hcs.1 hq
  set Φ' : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' := ⟨Φ, hΦ⟩ with hΦ'def
  let qq : MA.Qp P.r P.TT := ⟨(c0, ζ), ⟨fun _ => one_ne_zero, hζT⟩⟩

  have hfib : ∀ σ, Xf.comp (Qs σ) ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ := by
    intro σ
    have h1 := hK.2.2.2 (fun τ => if τ = σ then 1 else 0) Φ' qq
    have h2 : (∑ τ, (if τ = σ then (1 : ℂ) else 0) • Qs τ) = Qs σ := by
      simp [ite_smul]
    rw [h2] at h1
    change (((d.κ fun τ => if τ = σ then 1 else 0).1 Φ' : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
      Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c0 μ = (Φ c0 μ).comp (Qs σ) at h1
    rw [hval] at h1
    rw [← h1]
    intro p hp
    have h := ((d.κ fun τ => if τ = σ then 1 else 0).1 Φ').2.2.2 _ hx p.1 hp.1 p.2 hp.2.1
    simp only at h
    rw [hp.2.2] at h
    exact h.symm

  have hfix : ∀ σ, (Pr σ ν).comp (Xf.comp (Qs σ)) = Xf.comp (Qs σ) := by
    intro σ
    have hE : (Xf.comp (Qs σ)).comp (Qs σ) = Xf.comp (Qs σ) := by
      rw [ContinuousLinearMap.comp_assoc, hK.1 σ σ, if_pos rfl]
    have hEeig := (Gauge.GC.lie_eigenvalue_holds Wp Wq P Bs X d hH Qs hK ζ hζT _ hFr' σ _ (hfib σ)).1 hE
    ext v
    rw [ContinuousLinearMap.comp_apply]
    refine ((hPr.2.2 ν hpos).2.2.2 σ _).2 ?_
    intro Fr2 hFr2 w
    rw [hνfix] at hFr2
    rw [Topx1.typ_frame_change P.k P.r (by omega) Bs.z ν Bs.π Fr2 Fr hz hT hνW hνz hνν hπrep hFr2 hFr w
      ((Xf.comp (Qs σ)) v), hpass _ (hfib σ) w v, hgl']
    have hw : w = (w - ((P.k : ℂ) - 2) / 2) + ((P.k : ℂ) - 2) / 2 := by ring
    conv_lhs => rw [hw]
    exact hEeig _ v
  have hs : Xf = ∑ σ, Xf.comp (Qs σ) := by
    rw [← ContinuousLinearMap.comp_finsetSum, hK.2.1]
    rfl
  have hPP := (hPr.2.2 ν hpos).2.2.1
  conv_lhs => rw [hs]
  rw [ContinuousLinearMap.comp_finsetSum, Finset.sum_eq_single ρ]
  · exact hfix ρ
  · intro σ _ hσ
    rw [← hfix σ, ← ContinuousLinearMap.comp_assoc, hPP ρ σ, if_neg (Ne.symm hσ), ContinuousLinearMap.zero_comp]
  · intro h
    exact absurd (Finset.mem_univ ρ) h

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR
end
