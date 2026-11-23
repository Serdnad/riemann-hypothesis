module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle019
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DifferentiableOnAvg
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle024
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle014
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle032
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle022
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle025
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle027
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle020
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle016
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle044
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle045
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle035

@[expose] public section

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.GenOpsH

theorem gen_nbar (hU : UnipTau) (hW : WEx) (hS : SchOps) (hF : FTfact)
    {D : D7} {n : ℕ} {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D}
    {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} {H : G D n → ℝ≥0}
    {l : D.what₂.Tau → ℝ} {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ν : Measure (GA D V)}
    {τ : D.what₂.Tau} {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} {ι : GR n →* G D n}
    (hC : Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι) (y : GR n) (c : Matrix (Fin n) (Fin n) ℂ) (hc : cᴴ = c)
    (hyc : mR y = nbar c) :
    ∃ κ γ : ℂ, κ ≠ 0 ∧ ((∃ (Ψ : Mx D V.rank n → ℂ) (x₀ : Mx D V.rank n), AwayCls θ τ fr Ψ ∧ Ψ x₀ ≠ 0) → γ ≠ 0) ∧
      (∀ f : (Fin V.rank → Fin n → ℂ) → ℂ, IsSch f → IsSch (fun u => κ⁻¹ * ftLoc ε (-tLoc l τ) f u) ∧
        IsSch (fun u => κ * ftLoc ε (tLoc l τ) f u)) ∧
      ∀ (Ψ : Mx D V.rank n → ℂ) (hΨ : AwayCls θ τ fr Ψ) (f : (Fin V.rank → Fin n → ℂ) → ℂ) (hf : IsSch f),
        (ω (ι y) ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩).1 = tens θ τ fr (fun u => γ⁻¹ * (κ * ftLoc ε (tLoc l τ)
          (fun v => Complex.exp (Complex.I * (tLoc l τ : ℂ) * ((-c) * gramX ε v).trace) *
            (κ⁻¹ * ftLoc ε (-tLoc l τ) f v)) u)) Ψ := by
  have hfr : IsUnit fr.det := hC.hfr.1
  obtain ⟨w, hw⟩ := hW D n
  obtain ⟨yn, hyn⟩ := OG.exists_nU n (-c) (by rw [Matrix.conjTranspose_neg, hc])
  have hιn : ι yn = w⁻¹ * ι y * w := OG.iota_conj hC.hθ hC.hι w hw y yn c hyc hyn
  have hιy : ι y = w * ι yn * w⁻¹ := by rw [hιn]; group
  obtain ⟨κ, A, A', hκ, hFT⟩ := hF D n V ψ χ θ μ ω H l s ν τ ε fr ι hC w hw
  obtain ⟨f0, hf0, hf00⟩ := (hS V.rank n).2.2.2.2
  have h0 := hFT 0 (OG.awayCls_zero τ fr)
  let e : (Fin V.rank → Fin n → ℂ) → ℂ := fun u =>
    Complex.exp (Complex.I * (tLoc l τ : ℂ) * ((-c) * gramX ε u).trace)
  let F' : ((Fin V.rank → Fin n → ℂ) → ℂ) → (Fin V.rank → Fin n → ℂ) → ℂ := fun f u =>
    κ⁻¹ * ftLoc ε (-tLoc l τ) f u
  let Fw : ((Fin V.rank → Fin n → ℂ) → ℂ) → (Fin V.rank → Fin n → ℂ) → ℂ := fun f u => κ * ftLoc ε (tLoc l τ) f u
  have hc' : (-c)ᴴ = -c := by rw [Matrix.conjTranspose_neg, hc]
  have hE : ∀ f, IsSch f → IsSch (fun u => e u * F' f u) := fun f hf =>
    (hS V.rank n).2.2.2.1 ε (tLoc l τ) (-c) (F' f) hc' ((h0.2.2 f hf).2.1)
  set γ : ℂ := Fw (F' f0) (0 : Matrix (Fin V.rank) (Fin n) ℂ) with hγdef

  have hrelAll : ∀ Ψ (hΨ : AwayCls θ τ fr Ψ), ∀ x, Ψ x = γ * A (A' Ψ) x := by
    intro Ψ hΨ
    obtain ⟨hAΨ, hA'Ψ, hFΨ⟩ := hFT Ψ hΨ
    have kA := hFT (A' Ψ) hA'Ψ
    have hcons : ∀ g (hg : IsSch g), tens θ τ fr g Ψ = tens θ τ fr (Fw (F' g)) (A (A' Ψ)) := by
      intro g hg
      have k1g := (hFΨ g hg).2.2.2
      have kcg := (kA.2.2 (F' g) ((hFΨ g hg).2.1)).2.2.1
      have hΦ1 : ω w⁻¹ ⟨tens θ τ fr g Ψ, hΨ.2 g hg⟩ = ⟨tens θ τ fr (F' g) (A' Ψ), hA'Ψ.2 _ ((hFΨ g hg).2.1)⟩ :=
        Subtype.ext k1g
      have hid : ω w (ω w⁻¹ ⟨tens θ τ fr g Ψ, hΨ.2 g hg⟩) = ⟨tens θ τ fr g Ψ, hΨ.2 g hg⟩ := by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      rw [hΦ1] at hid
      rw [← kcg, hid]
    intro x
    obtain ⟨x', hx'1, hx'2, hx'3⟩ := OG.exists_slice hC.hθ τ x (fr * (0 : Matrix (Fin V.rank) (Fin n) ℂ))
    have h1 := congrFun (hcons f0 hf0) x'
    have hf00' : f0 (0 : Matrix (Fin V.rank) (Fin n) ℂ) = 1 := hf00
    rw [OG.tens_at τ hfr _ _ x' 0 hx'1, OG.tens_at τ hfr _ _ x' 0 hx'1, hf00', one_mul, hΨ.1 x' x hx'2 hx'3,
      kA.1.1 x' x hx'2 hx'3] at h1
    exact h1
  refine ⟨κ, γ, hκ, ?_, fun f hf => ⟨(h0.2.2 f hf).2.1, (h0.2.2 f hf).1⟩, ?_⟩
  · rintro ⟨Ψ, x₀, hΨ, hx₀⟩ hγ
    exact hx₀ (by rw [hrelAll Ψ hΨ x₀, hγ, zero_mul])
  intro Ψ hΨ f hf
  obtain ⟨hAΨ, hA'Ψ, hFΨ⟩ := hFT Ψ hΨ
  have k1 := (hFΨ f hf).2.2.2
  have kA := hFT (A' Ψ) hA'Ψ
  have kr := (kA.2.2 (fun u => e u * F' f u) (hE f hf)).2.2.1
  have hrel := hrelAll Ψ hΨ
  by_cases hγ : γ = 0
  · have hΨ0 : Ψ = 0 := funext fun x => by rw [hrel x, hγ, zero_mul]; rfl
    subst hΨ0
    have hz : (⟨tens θ τ fr f 0, hΨ.2 f hf⟩ : schwartzA θ V.rank n) = 0 := Subtype.ext (by funext x; simp [tens])
    rw [hz, map_zero]
    funext x
    simp [tens]
  · have hstep : ω (ι y) ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩ =
        ω w ⟨tens θ τ fr (fun u => e u * F' f u) (A' Ψ), hA'Ψ.2 _ (hE f hf)⟩ := by
      rw [hιy, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
      congr 1
      apply Subtype.ext
      funext x
      rw [hU D n V ψ χ θ μ ω H l s ν τ ε fr ι hC yn (-c) hc' hyn, k1]
      simp only [tens, e, F', mul_assoc]
    funext x
    rw [hstep, kr]
    simp only [tens]
    rw [hrel x]
    simp only [e, F']
    field_simp

end PositivityTheory.Rg.Sw.Glob.GenOpsH
end
end

section

noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct ENNReal Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn GlobalTheory.SiegelFormula
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

open DHolH

theorem dHol : DHol := by
  intro hP D n V hn hr θ hθ ν hν P _ _ U hU φ h1 h2 h3 h4 h5
  intro F

  have hfacts : ∀ (p₀ : P) (z₀ : ℂ), z₀ ∈ U → ∃ (N : Set (P × ℂ)) (M : Mx D V.rank n → ℂ), N ∈ 𝓝 (p₀, z₀) ∧
      Continuous M ∧ absThetaInt V ν M < ⊤ ∧ ∀ pz ∈ N, pz.2 ∈ U → ∀ x, ‖φ pz.1 pz.2 x‖ ≤ ‖M x‖ := by
    intro p₀ z₀ hz₀
    obtain ⟨N, M, hN, hM, hb⟩ := h5 p₀ z₀ hz₀
    obtain ⟨hMc, hMf⟩ := sch_facts hP V hn hr θ hθ ν hν hM
    exact ⟨N, M, hN, hMc, hMf, hb⟩
  have hcontx : ∀ p, ∀ z ∈ U, Continuous (φ p z) := by
    intro p z hz
    exact (h4 p).comp_continuous (continuous_const.prodMk continuous_id) fun x => ⟨hz, Set.mem_univ _⟩
  have hfin : ∀ p, ∀ z ∈ U, absThetaInt V ν (φ p z) < ⊤ := by
    intro p z hz
    obtain ⟨N, M, hN, -, hMf, hb⟩ := hfacts p z hz
    exact lt_of_le_of_lt (absThetaInt_mono V ν (hb (p, z) (mem_of_mem_nhds hN) hz)) hMf
  have hmeas : ∀ p, ∀ z ∈ U, AEStronglyMeasurable (descend (GQ V) (thS V (φ p z))) (autMeasure V ν) :=
    fun p z hz => aestronglyMeasurable_thS V ν (hcontx p z hz) (hfin p z hz)
  have hfam : ∀ p, Fam V ν U (φ p) := by
    intro p
    refine ⟨h2 p, fun z₀ hz₀ => ?_, hmeas p⟩
    obtain ⟨N, M, hN, hMc, hMf, hb⟩ := hfacts p z₀ hz₀
    obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.1 hN
    obtain ⟨ε₁, hε₁, hb₁⟩ := Metric.mem_nhds_iff.1 hv
    obtain ⟨ε₂, hε₂, hb₂⟩ := Metric.mem_nhds_iff.1 (hU.mem_nhds hz₀)
    refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, (Metric.ball_subset_ball (min_le_right _ _)).trans hb₂, M, hMc, hMf, ?_⟩
    intro z hz x
    have hzv : z ∈ v := hb₁ (Metric.ball_subset_ball (min_le_left _ _) hz)
    have hzU : z ∈ U := hb₂ (Metric.ball_subset_ball (min_le_right _ _) hz)
    exact hb (p, z) (huv ⟨mem_of_mem_nhds hu, hzv⟩) hzU x
  refine ⟨?_, fun p => ?_, fun p r z hz => ?_⟩
  ·
    rintro ⟨p₀, z₀⟩ ⟨-, hz₀⟩
    obtain ⟨N, M, hN, hMc, hMf, hb⟩ := hfacts p₀ z₀ hz₀
    have hfinq := ae_absTheta_lt V ν hMc hMf
    have hsumM : ∀ q : Quot (GQ V), descend (GQ V) (absTheta V M) q < ⊤ →
        Summable fun ξ : Matrix (Fin V.rank) (Fin n) D.host.E => ‖M (invPt V q.out ξ)‖ := by
      intro q hq
      refine Summable.of_enorm ?_
      simpa [GlobalTheory.AutomorphicL2Unitary.descend, absTheta] using hq.ne
    have htsM : ∀ q : Quot (GQ V), descend (GQ V) (absTheta V M) q < ⊤ →
        ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, ‖M (invPt V q.out ξ)‖ =
          (descend (GQ V) (absTheta V M) q).toReal := by
      intro q hq
      simp only [GlobalTheory.AutomorphicL2Unitary.descend, absTheta]
      rw [ENNReal.tsum_toReal_eq fun ξ => enorm_ne_top]
      simp
    have hs : Set.univ ×ˢ U ∈ 𝓝[Set.univ ×ˢ U] (p₀, z₀) := self_mem_nhdsWithin
    have hNs : N ∩ Set.univ ×ˢ U ∈ 𝓝[Set.univ ×ˢ U] (p₀, z₀) := inter_mem (mem_nhdsWithin_of_mem_nhds hN) hs
    have hint : ContinuousWithinAt (fun pz : P × ℂ => ∫ q, descend (GQ V) (thS V (φ pz.1 pz.2)) q ∂autMeasure V ν)
        (Set.univ ×ˢ U) (p₀, z₀) := by
      refine continuousWithinAt_of_dominated (bound := fun q => (descend (GQ V) (absTheta V M) q).toReal) ?_ ?_
        (integrable_absTheta_toReal V ν hMc hMf) ?_
      · exact Eventually.mono hs fun pz hpz => hmeas pz.1 pz.2 hpz.2
      · refine Eventually.mono hNs fun pz hpz => ?_
        filter_upwards [hfinq] with q hq
        have hs1 := hsumM q hq
        have hs' : Summable fun ξ => ‖φ pz.1 pz.2 (invPt V q.out ξ)‖ :=
          Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ξ => hb pz hpz.1 hpz.2.2 _) hs1
        simp only [GlobalTheory.AutomorphicL2Unitary.descend, thS]
        calc ‖∑' ξ, φ pz.1 pz.2 (invPt V q.out ξ)‖ ≤ ∑' ξ, ‖φ pz.1 pz.2 (invPt V q.out ξ)‖ := norm_tsum_le_tsum_norm hs'
          _ ≤ ∑' ξ, ‖M (invPt V q.out ξ)‖ := hs'.tsum_le_tsum (fun ξ => hb pz hpz.1 hpz.2.2 _) hs1
          _ = _ := htsM q hq
      · filter_upwards [hfinq] with q hq
        have hs1 := hsumM q hq
        have hon : ContinuousOn (fun pz : P × ℂ => ∑' ξ, φ pz.1 pz.2 (invPt V q.out ξ)) (N ∩ Set.univ ×ˢ U) :=
          continuousOn_tsum (fun ξ => (h3 _).mono Set.inter_subset_right) hs1
            (fun ξ pz hpz => hb pz hpz.1 hpz.2.2 _)
        exact (hon.continuousWithinAt ⟨mem_of_mem_nhds hN, ⟨Set.mem_univ _, hz₀⟩⟩).mono_of_mem_nhdsWithin hNs
    have : (fun pz : P × ℂ => F pz.1 pz.2) = fun pz => ((autMeasure V ν) Set.univ).toReal⁻¹ •
        ∫ q, descend (GQ V) (thS V (φ pz.1 pz.2)) q ∂autMeasure V ν := by
      funext pz
      simp only [F, average_eq]
      rfl
    rw [this]
    exact hint.const_smul ((autMeasure V ν) Set.univ).toReal⁻¹
  · exact differentiableOn_avg V ν hU (hfam p)
  · exact iteratedDeriv_avg V ν hU (hfam p) r z hz

end PositivityTheory.Rg.Sw.Glob
end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

open NbarH GaussH

theorem lawNbar_of (hU : UnipTau) (hW : WEx) (hF : FTfact) (hTI : TensInj) (hLNe : LNe) : LawNbar := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC L hL y c hc hyc f hf
  have htc : |tLoc l τ| = cLoc l τ := abs_tLoc l τ
  have hc0 : 0 < cLoc l τ := by
    unfold cLoc
    exact mul_pos (mul_pos two_pos Real.pi_pos) (abs_pos.2 (hLNe D ψ θ l hC.hψ hC.hθ hC.hl τ))
  have hsq : (tLoc l τ) ^ 2 = (cLoc l τ) ^ 2 := by rw [← htc, sq_abs]
  have hsq' : (-tLoc l τ) ^ 2 = (cLoc l τ) ^ 2 := by rw [neg_sq, hsq]
  obtain ⟨w, hw⟩ := hW D n
  have hc' : (-c)ᴴ = -c := by rw [Matrix.conjTranspose_neg, hc]
  obtain ⟨yn, hyn⟩ := OG.exists_nU n (-c) hc'
  have hιy : ι y = w * ι yn * w⁻¹ := by rw [OG.iota_conj hC.hθ hC.hι w hw y yn c hyc hyn]; group
  obtain ⟨κ, A, A', hκ, hFT⟩ := hF D n V ψ χ θ μ ω H l s ν τ ε fr ι hC w hw
  have hvS : IsSch (vac (n := n) ε (tLoc l τ) (cLoc l τ)) := gZSch V.rank n ε _ _ hc0 htc _ isSiegel_I
  set K : ℂ := ((Real.pi : ℂ) / (cLoc l τ)) ^ (V.rank * n) with hK
  have hK0 : K ≠ 0 := pow_ne_zero _ (div_ne_zero (by exact_mod_cast Real.pi_pos.ne') (by exact_mod_cast hc0.ne'))
  refine hTI D n V ψ χ θ μ ω H l s ν τ ε fr ι hC _ _ fun Ψ hΨ => ?_
  obtain ⟨hAΨ, hA'Ψ, hFΨ⟩ := hFT Ψ hΨ
  have kA := hFT (A' Ψ) hA'Ψ

  have hid : ∀ g (hg : IsSch g), tens θ τ fr g Ψ =
      tens θ τ fr (fun u => κ * ftLoc ε (tLoc l τ) (fun v => κ⁻¹ * ftLoc ε (-tLoc l τ) g v) u) (A (A' Ψ)) := by
    intro g hg
    have h1 : ω w⁻¹ ⟨tens θ τ fr g Ψ, hΨ.2 g hg⟩ =
        ⟨tens θ τ fr (fun u => κ⁻¹ * ftLoc ε (-tLoc l τ) g u) (A' Ψ), hA'Ψ.2 _ ((hFΨ g hg).2.1)⟩ :=
      Subtype.ext (hFΨ g hg).2.2.2
    have h2 := (kA.2.2 _ ((hFΨ g hg).2.1)).2.2.1
    have h3 : ω w (ω w⁻¹ ⟨tens θ τ fr g Ψ, hΨ.2 g hg⟩) = ⟨tens θ τ fr g Ψ, hΨ.2 g hg⟩ := by
      rw [← mul_apply_eq_comp, ← map_mul, mul_inv_cancel, map_one, one_apply_eq_self]
    rw [h1] at h3
    rw [← h2, h3]
  have hAA : ∀ x, A (A' Ψ) x = (K * K)⁻¹ * Ψ x := by
    intro x
    have h := congrFun (hid _ hvS) x
    simp only [tens, ftLoc_vac ε _ _ _ hc0 hsq', ftLoc_const_mul', ftLoc_vac ε _ _ _ hc0 hsq] at h
    have hv0 : vac (n := n) ε (tLoc l τ) (cLoc l τ) (fr⁻¹ * compAt θ τ x) ≠ 0 := Complex.exp_ne_zero _
    have hκ' : κ * κ⁻¹ = 1 := mul_inv_cancel₀ hκ
    field_simp at h
    rw [h, hK]
    field_simp

  rw [← hL.2 y Ψ hΨ f hf]
  have hE : IsSch (fun u => chN ε (tLoc l τ) (-c) u * (κ⁻¹ * ftLoc ε (-tLoc l τ) f u)) :=
    (schOps V.rank n).2.2.2.1 ε (tLoc l τ) (-c) _ hc' (hFΨ f hf).2.1
  have s1 : ω w⁻¹ ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩ =
      ⟨tens θ τ fr (fun u => κ⁻¹ * ftLoc ε (-tLoc l τ) f u) (A' Ψ), hA'Ψ.2 _ ((hFΨ f hf).2.1)⟩ :=
    Subtype.ext (hFΨ f hf).2.2.2
  have s2 : ω (ι yn) ⟨tens θ τ fr (fun u => κ⁻¹ * ftLoc ε (-tLoc l τ) f u) (A' Ψ), hA'Ψ.2 _ ((hFΨ f hf).2.1)⟩ =
      ⟨tens θ τ fr (fun u => chN ε (tLoc l τ) (-c) u * (κ⁻¹ * ftLoc ε (-tLoc l τ) f u)) (A' Ψ), hA'Ψ.2 _ hE⟩ := by
    apply Subtype.ext
    funext x
    rw [hU D n V ψ χ θ μ ω H l s ν τ ε fr ι hC yn (-c) hc' hyn]
    simp only [tens, chN, mul_assoc]
  have s3 := (kA.2.2 _ hE).2.2.1
  rw [hιy, map_mul, map_mul, mul_apply_eq_comp, mul_apply_eq_comp, s1, s2, s3]
  funext x
  simp only [tens]
  rw [hAA x]
  have hKK : ((|tLoc l τ| / Real.pi : ℝ) : ℂ) ^ (2 * V.rank * n) = (K * K)⁻¹ := by
    rw [hK, htc, ← pow_two, ← pow_mul, ← inv_pow, inv_div]
    push_cast
    ring_nf
  rw [hKK]
  have hκ' : κ * κ⁻¹ = 1 := mul_inv_cancel₀ hκ
  have e : (fun v => chN ε (tLoc l τ) (-c) v * (κ⁻¹ * ftLoc ε (-tLoc l τ) f v)) =
      fun v => κ⁻¹ * (chN ε (tLoc l τ) (-c) v * ftLoc ε (-tLoc l τ) f v) := by funext v; ring
  rw [e, ftLoc_const_mul']
  linear_combination (ftLoc ε (tLoc l τ) (fun v => chN ε (tLoc l τ) (-c) v * ftLoc ε (-tLoc l τ) f v)
    (fr⁻¹ * compAt θ τ x)) * (K * K)⁻¹ * Ψ x * hκ'

end PositivityTheory.Rg.Sw.Glob
end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.FTH

open PositivityTheory.Rg.Sw.Glob.FTP
open Classical

variable {D : D7} {n m : ℕ}

def Pk (μ : Measure (Mx D m n)) (π : Mx D m n → (Fin m → Fin n → ℂ)) (B : Mx D m n → ℂ) (κ : ℂ) : Prop :=
  ∀ a : (Fin m → Fin n → ℂ) → ℂ, Measurable a → (∃ C, ∀ u, ‖a u‖ ≤ C * (1 + ‖u‖) ^ (-rr m n)) →
    ∫ z, a (π z) * B z ∂μ = κ * ∫ u, a u

def kap (μ : Measure (Mx D m n)) (π : Mx D m n → (Fin m → Fin n → ℂ)) (B : Mx D m n → ℂ) : ℂ :=
  Classical.epsilon (Pk μ π B)


theorem kap_spec {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau}
    {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hdet : IsUnit fr.det) (μ : Measure (Mx D V.rank n)) [μ.IsAddHaarMeasure]
    {Ψ : Mx D V.rank n → ℂ} (hΨ : AwayCls θ τ fr Ψ) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ)
    (x : Mx D V.rank n) :
    Pk μ (piF θ τ fr) (Bw ψ V θ τ fr Ψ x) (kap μ (piF θ τ fr) (Bw ψ V θ τ fr Ψ x)) := by
  have := GlobalTheory.Doubling.isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have : BorelSpace (Mx D V.rank n) := ⟨rfl⟩
  apply Classical.epsilon_spec
  have hρc : Continuous fun u : Fin V.rank → Fin n → ℂ => (1 + ‖u‖) ^ (-rr V.rank n) :=
    (continuous_const.add continuous_norm).rpow_const fun u => Or.inl (add_pos_of_pos_of_nonneg one_pos (norm_nonneg u)).ne'
  exact LocCellT.tauFact μ (piF θ τ fr) (continuous_piF hθ τ fr) (sIns τ fr)
    (fun z u => by rw [map_add (piF θ τ fr), piF_sIns hθ τ hdet]) (Bw ψ V θ τ fr Ψ x)
    (continuous_Bw hθ hψ hΨ x).measurable (fun z u => Bw_add hθ hdet ψ hΨ x z u)
    (fun u => (1 + ‖u‖) ^ (-rr V.rank n)) hρc (fun u => Real.rpow_pos_of_pos (by positivity) _)
    (hint_int hθ hdet μ hΨ hψ x)

theorem sch_decay (f : (Fin m → Fin n → ℂ) → ℂ) (hf : IsSch f) :
    ∃ C, ∀ u, ‖f u‖ ≤ C * (1 + ‖u‖) ^ (-rr m n) := by
  obtain ⟨S, rfl⟩ := hf
  set k : ℕ := Module.finrank ℝ (Fin m → Fin n → ℂ) + 1 with hk
  refine ⟨2 ^ k * (Finset.Iic (k, 0)).sup (schwartzSeminormFamily ℂ (Fin m → Fin n → ℂ) ℂ) S, fun u => ?_⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k, 0)) le_rfl le_rfl S u
  rw [norm_iteratedFDeriv_zero] at h
  have hpos : 0 < (1 + ‖u‖) ^ k := by positivity
  have e : (1 + ‖u‖) ^ (-rr m n) = ((1 + ‖u‖) ^ k)⁻¹ := by
    rw [rr, Real.rpow_neg (by positivity), Real.rpow_natCast]
  rw [e, ← div_eq_mul_inv, le_div_iff₀ hpos, mul_comm]
  exact h

end PositivityTheory.Rg.Sw.Glob.FTH
end
end
