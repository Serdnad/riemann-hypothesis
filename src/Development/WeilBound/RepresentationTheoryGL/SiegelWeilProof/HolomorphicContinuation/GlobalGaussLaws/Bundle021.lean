module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle017
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle016
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle014
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.BoundMulTranslate
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.NormIterFstComp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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

@[expose] public section

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

theorem locFact_of (hD : Decomp) (hG : OpGen) : LocFact := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC
  have hop : ∀ y : GR n, ((∃ b : Matrix (Fin n) (Fin n) ℂ, bᴴ = b ∧ mR y = nU b) ∨
      (∃ c : Matrix (Fin n) (Fin n) ℂ, cᴴ = c ∧ mR y = nbar c) ∨
      (∃ a : Matrix (Fin n) (Fin n) ℂ, IsUnit a.det ∧ mR y = mM a)) →
    ∃ L : ((Fin V.rank → Fin n → ℂ) → ℂ) → ((Fin V.rank → Fin n → ℂ) → ℂ), (∀ f, IsSch f → IsSch (L f)) ∧
      ∀ Ψ (hΨ : AwayCls θ τ fr Ψ) f (hf : IsSch f),
        (ω (ι y) ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩).1 = tens θ τ fr (L f) Ψ :=
    fun y hy => hG D n V ψ χ θ μ ω H l s ν τ ε fr ι hC y hy
  choose! large₂ hLgS hLg using hop
  have hdec := fun y : GR n => hD n y
  choose y1 y2 y3 y4 hy h1 h2 h3 h4 using hdec
  have g1 : ∀ y, (∃ b : Matrix (Fin n) (Fin n) ℂ, bᴴ = b ∧ mR (y1 y) = nU b) ∨
      (∃ c : Matrix (Fin n) (Fin n) ℂ, cᴴ = c ∧ mR (y1 y) = nbar c) ∨
      (∃ a : Matrix (Fin n) (Fin n) ℂ, IsUnit a.det ∧ mR (y1 y) = mM a) := fun y => by
    obtain ⟨t, ht⟩ := h1 y
    exact Or.inl ⟨_, herm_smul_one t, ht⟩
  have g2 : ∀ y, (∃ b : Matrix (Fin n) (Fin n) ℂ, bᴴ = b ∧ mR (y2 y) = nU b) ∨
      (∃ c : Matrix (Fin n) (Fin n) ℂ, cᴴ = c ∧ mR (y2 y) = nbar c) ∨
      (∃ a : Matrix (Fin n) (Fin n) ℂ, IsUnit a.det ∧ mR (y2 y) = mM a) := fun y => Or.inr (Or.inl (h2 y))
  have g3 : ∀ y, (∃ b : Matrix (Fin n) (Fin n) ℂ, bᴴ = b ∧ mR (y3 y) = nU b) ∨
      (∃ c : Matrix (Fin n) (Fin n) ℂ, cᴴ = c ∧ mR (y3 y) = nbar c) ∨
      (∃ a : Matrix (Fin n) (Fin n) ℂ, IsUnit a.det ∧ mR (y3 y) = mM a) := fun y => Or.inr (Or.inr (h3 y))
  have g4 : ∀ y, (∃ b : Matrix (Fin n) (Fin n) ℂ, bᴴ = b ∧ mR (y4 y) = nU b) ∨
      (∃ c : Matrix (Fin n) (Fin n) ℂ, cᴴ = c ∧ mR (y4 y) = nbar c) ∨
      (∃ a : Matrix (Fin n) (Fin n) ℂ, IsUnit a.det ∧ mR (y4 y) = mM a) := fun y => Or.inl (h4 y)
  refine ⟨fun y f => large₂ (y1 y) (large₂ (y2 y) (large₂ (y3 y) (large₂ (y4 y) f))), fun y f hf => ?_, fun y Ψ hΨ f hf => ?_⟩
  · exact hLgS _ (g1 y) _ (hLgS _ (g2 y) _ (hLgS _ (g3 y) _ (hLgS _ (g4 y) _ hf)))
  · have step : ∀ (z : GR n) (hz : (∃ b : Matrix (Fin n) (Fin n) ℂ, bᴴ = b ∧ mR z = nU b) ∨
        (∃ c : Matrix (Fin n) (Fin n) ℂ, cᴴ = c ∧ mR z = nbar c) ∨
        (∃ a : Matrix (Fin n) (Fin n) ℂ, IsUnit a.det ∧ mR z = mM a)), ∀ f (hf : IsSch f)
        (h : tens θ τ fr f Ψ ∈ schwartzA θ V.rank n),
        ω (ι z) ⟨tens θ τ fr f Ψ, h⟩ = ⟨tens θ τ fr (large₂ z f) Ψ, hΨ.2 _ (hLgS z hz f hf)⟩ := by
      intro z hz f hf h
      exact Subtype.ext (hLg z hz Ψ hΨ f hf)
    have hprod : ω (ι y) = ω (ι (y1 y)) * ω (ι (y2 y)) * ω (ι (y3 y)) * ω (ι (y4 y)) := by
      conv_lhs => rw [hy y]
      simp only [map_mul]
    rw [hprod]
    simp only [Module.End.mul_apply]
    have s4 := hLgS (y4 y) (g4 y) _ hf
    have s3 := hLgS (y3 y) (g3 y) _ s4
    have s2 := hLgS (y2 y) (g2 y) _ s3
    rw [step (y4 y) (g4 y) _ hf, step (y3 y) (g3 y) _ s4, step (y2 y) (g2 y) _ s3, step (y1 y) (g1 y) _ s2]

theorem locOpEx_of_fact (hF : LocFact) (hA : AwayIn) (hS : SchFP) (hL : LNe) : LocOpEx := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC
  obtain ⟨L, -, hL2⟩ := hF D n V ψ χ θ μ ω H l s ν τ ε fr ι hC
  refine ⟨L, ?_⟩
  intro y Ψ hΨ P
  have hAw : AwayCls θ τ fr Ψ :=
    hA D n V θ l s τ ε fr hC.hθ hC.hs hC.hfr (fun τ' => hL D ψ θ l hC.hψ hC.hθ hC.hl τ') Ψ hΨ
  have hc : 0 < cLoc l τ := by
    have hne := hL D ψ θ l hC.hψ hC.hθ hC.hl τ
    unfold cLoc
    have : 0 < |l τ| := abs_pos.mpr hne
    positivity
  have hf0 : IsSch (fP (cLoc l τ) P) := hS _ _ _ hc P
  rw [phiS_eq' (hAw.2 _ hf0)]
  exact hL2 y Ψ hAw _ hf0

end PositivityTheory.Rg.Sw.Glob
end
end

section

noncomputable section

open Filter Topology Set
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.Glob

open SchDH

theorem schDeriv : SchDeriv := by
  intro m n c hc X P
  obtain ⟨φ0, hφ0⟩ := exists_fP (m := m) (n := n) c hc P
  obtain ⟨φ1, hφ1⟩ := exists_fP (m := m) (n := n) c hc (vfX c X P)
  set A : ℝ → (Fin m → Fin n → ℂ) →L[ℝ] (Fin m → Fin n → ℂ) :=
    fun t => matL (NormedSpace.exp ((t : ℂ) • X)) with hAdef
  have hA : ContDiff ℝ ∞ A := contDiff_A X
  have hinv : ∀ t y, A (-t) (A t y) = y := by
    intro t y
    simp only [hAdef]
    rw [← matL_mul, ← Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left _).smul_right _)]
    rw [← add_smul, Complex.ofReal_neg, neg_add_cancel, zero_smul, NormedSpace.exp_zero, matL_one]
  let Aeq : ℝ → (Fin m → Fin n → ℂ) ≃L[ℝ] (Fin m → Fin n → ℂ) := fun t =>
    ContinuousLinearEquiv.equivOfInverse (A t) (A (-t)) (fun y => hinv t y)
      (fun y => by have h := hinv (-t) y; rwa [neg_neg] at h)
  have hAeq : ∀ t y, Aeq t y = A t y := fun t y => rfl
  let S : ℝ → SchwartzMap (Fin m → Fin n → ℂ) ℂ := fun t => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (Aeq t) φ0
  have hS : ∀ t y, S t y = φ0 (A t y) := fun t y => by
    simp only [S, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, hAeq]
  refine ⟨S, φ1, fun t y => ?_, fun y => hφ1 y, ?_⟩
  · rw [hS, hφ0]
    congr 1
  · set F : ℝ × (Fin m → Fin n → ℂ) → ℂ := fun q => φ0 (A q.1 q.2) with hFdef
    have hF : ContDiff ℝ ∞ F := (φ0.smooth ⊤).comp ((hA.comp contDiff_fst).clm_apply contDiff_snd)
    have hR : ∀ p, ⇑(S p) = fun x => F (p, x) := fun p => by funext x; rw [hS]
    have hder : ∀ x, HasDerivAt (fun t : ℝ => F (t, x)) (φ1 x) 0 := fun x => by
      have h := hasDerivAt_curve c X P x
      rw [hφ1]
      have e : (fun t : ℝ => F (t, x)) = fun t : ℝ => fP c P (matL (NormedSpace.exp ((t : ℂ) • X)) x) := by
        funext t; simp only [hFdef, hAdef, hφ0]
      rw [e]; exact h
    have hD : ∀ v : ℝ, ⇑(v • φ1) = fun x => fderiv ℝ F ((0 : ℝ), x) (v, 0) := by
      intro v
      funext x
      have hFd : HasFDerivAt F (fderiv ℝ F ((0 : ℝ), x)) ((0 : ℝ), x) :=
        ((hF.differentiable (by simp)) _).hasFDerivAt
      have hc : HasDerivAt (fun t : ℝ => ((t, x) : ℝ × (Fin m → Fin n → ℂ))) ((1 : ℝ), (0 : Fin m → Fin n → ℂ)) 0 :=
        (hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) x)
      have h1 := hFd.comp_hasDerivAt (0 : ℝ) hc
      have h2 := (hder x).unique h1
      have e : ((v, 0) : ℝ × (Fin m → Fin n → ℂ)) = v • ((1 : ℝ), (0 : Fin m → Fin n → ℂ)) := by
        ext <;> simp
      rw [SchwartzMap.smul_apply, e, map_smul]
      change v • φ1 x = v • (fderiv ℝ F ((0 : ℝ), x)) ((1 : ℝ), (0 : Fin m → Fin n → ℂ))
      rw [h2]
    have hb : ∀ k N : ℕ, ∃ C, ∀ p : ℝ, ‖p - 0‖ ≤ 1 → ∀ x : Fin m → Fin n → ℂ,
        ‖x‖ ^ k * ‖iteratedFDeriv ℝ N F (p, x)‖ ≤ C := fun k N => bound_comp φ0 A hA hinv k N
    rw [(schwartz_withSeminorms ℂ (Fin m → Fin n → ℂ) ℂ).tendsto_nhds]
    rintro ⟨k, N⟩ ε hε
    obtain ⟨C, hC⟩ := GlobalTheory.CompanionTheory.OM.SchDiff.seminorm_remainder hF (0 : ℝ) hb S (fun v => v • φ1) hR hD k N
    set C' := max C 1 with hC'
    have hC'0 : 0 < C' := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hev : ∀ᶠ t in 𝓝[≠] (0 : ℝ), |t| < min 1 (ε / C') := by
      have h := (continuous_abs.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
      rw [abs_zero] at h
      exact h (Iio_mem_nhds (lt_min one_pos (div_pos hε hC'0)))
    filter_upwards [hev, self_mem_nhdsWithin] with t ht htne
    have htne' : t ≠ 0 := htne
    have ht1 : ‖t‖ ≤ 1 := by rw [Real.norm_eq_abs]; exact (lt_of_lt_of_le ht (min_le_left _ _)).le
    have key : t⁻¹ • (S t - S 0) - φ1 = ((t⁻¹ : ℝ) : ℂ) • (S (0 + t) - S 0 - t • φ1) := by
      rw [Complex.coe_smul, zero_add]
      simp only [smul_sub, smul_smul, inv_mul_cancel₀ htne', one_smul]
    change SchwartzMap.seminorm ℂ k N (t⁻¹ • (S t - S 0) - φ1) < ε
    rw [key, map_smul_eq_mul, Complex.norm_real, norm_inv]
    have hCt := hC t ht1
    have hpos : 0 < ‖t‖ := norm_pos_iff.2 htne'
    calc ‖t‖⁻¹ * (SchwartzMap.seminorm ℂ k N) (S (0 + t) - S 0 - t • φ1)
        ≤ ‖t‖⁻¹ * (C * ‖t‖ ^ 2) := by gcongr
      _ = C * ‖t‖ := by field_simp
      _ ≤ C' * ‖t‖ := by gcongr; exact le_max_left _ _
      _ < C' * (ε / C') := by
          gcongr
          rw [Real.norm_eq_abs]; exact lt_of_lt_of_le ht (min_le_right _ _)
      _ = ε := by field_simp

end PositivityTheory.Rg.Sw.Glob
end
end

section

namespace PositivityTheory.Rg.Sw.Glob

theorem awayFact_of (hA : AwayAct) (hD : DecompAway) : AwayFact := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC g
  have hθι : Formalism.L2.Theta.IsInfFam θ ∧ IsPlaceEmb θ τ ι := by
    obtain ⟨-, -, -, hθ, -, -, -, -, -, -, -, -, -, hι, -⟩ := hC
    exact ⟨hθ, hι⟩
  obtain ⟨x, y, hx, hg, -⟩ := hD D n θ τ ι hθι.1 hθι.2 g
  obtain ⟨A, hA'⟩ := hA D n V ψ χ θ μ ω H l s ν τ ε fr ι hC x hx
  exact ⟨x, y, hg, fun Ψ hΨ => ⟨A Ψ, (hA' Ψ hΨ).1, fun S hS => (hA' Ψ hΨ).2 (⇑S) ⟨S, rfl⟩⟩⟩

end PositivityTheory.Rg.Sw.Glob
end
