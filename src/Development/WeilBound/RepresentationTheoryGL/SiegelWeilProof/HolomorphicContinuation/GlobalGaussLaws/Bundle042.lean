module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LamSing
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle260
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle224
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle461
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle617
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle471
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle681
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle039
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocKvacA
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle038
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle014
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle012
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.PlaceFacts
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle040
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open scoped Matrix ComplexConjugate
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

theorem awayIn : AwayIn := by
  intro D n V θ l s τ ε fr hθ hs hfr hl Ψ hΨ
  refine ⟨fun x x' hx hf => AwayPf.dep θ V l s τ hΨ x x' hx hf, fun f hf => ?_⟩
  induction hΨ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨p, g, hg, hp, rfl⟩ := hφ
    exact AwayPf.gen_sch θ V l s τ fr hfr.1 hs hl p hp g hg f hf
  | zero =>
    have : tens θ τ fr f (0 : Mx D V.rank n → ℂ) = 0 := by
      funext x
      simp [tens]
    rw [this]
    exact Submodule.zero_mem _
  | add a b _ _ ha hb =>
    have : tens θ τ fr f (a + b) = tens θ τ fr f a + tens θ τ fr f b := by
      funext x
      simp only [tens, Pi.add_apply, mul_add]
    rw [this]
    exact Submodule.add_mem _ ha hb
  | smul c a _ ha =>
    have : tens θ τ fr f (c • a) = c • tens θ τ fr f a := by
      funext x
      simp only [tens, Pi.smul_apply, smul_eq_mul]
      ring
    rw [this]
    exact Submodule.smul_mem _ c ha

end PositivityTheory.Rg.Sw.Glob
end
end

section

noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AdelicU GlobalTheory.StdUnn MvPolynomial
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.RhoH

variable {D : D7} {n : ℕ}




theorem const_of_annS {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau}
    {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hfr : IsTauFrame V τ s ε fr) (hM : ∀ τ, (gramAt D V τ * s τ).IsHermitian) (l : D.what₂.Tau → ℝ)
    (Q : PX V.rank n) (h : ∀ X, annS V l s θ τ X (tens θ τ fr (fP (cLoc l τ) Q) (psi0 θ V n l s τ)) = 0) :
    Q = C (evX Q 0) := by
  have hk : ∀ u W : Matrix (Fin V.rank) (Fin n) ℂ, ∑ k, ptX W k * eval (ptX u) (pderiv k Q) = 0 := by
    intro u W
    have e := congrFun (h (fr * W)) (xL θ τ (fr * u))
    rw [annS_tens hθ hfr hM l] at e
    have hinv : ∀ v : Matrix (Fin V.rank) (Fin n) ℂ, fr⁻¹ * (fr * v) = v := fun v => by
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hfr.1, Matrix.one_mul]
    have hc : compAt θ τ (xL θ τ (fr * u)) = fr * u := by
      have := congrFun (compAt_xL hθ τ (fr * u)) τ
      simpa [dirAt_self] using this
    have hp : psi0 θ V n l s τ (xL θ τ (fr * u)) = 1 := by
      unfold psi0
      rw [compAt_xL hθ, gAway_dirAt, finPart_xL hθ]
      simp only [one_mul]
      exact gaussian_at_zero_eq_one D V.rank n
    rw [hc, hinv, hinv, hp, mul_one] at e
    exact (mul_eq_zero.1 e).resolve_right (gs_ne_zero _ _)
  have hconst : ∀ u : Matrix (Fin V.rank) (Fin n) ℂ, evX Q u = evX Q 0 := by
    intro u
    let F : ℝ → ℂ := fun t => eval (ptX (0 : Matrix (Fin V.rank) (Fin n) ℂ) + (t : ℂ) • ptX u) Q
    have hF : ∀ t, HasDerivAt F 0 t := by
      intro t
      have hd := GlobalTheory.FockAnnKill.hasDerivAt_eval_line Q (ptX (0 : Matrix (Fin V.rank) (Fin n) ℂ)) (ptX u) t
      refine hd.congr_deriv ?_
      have e2 : ptX (0 : Matrix (Fin V.rank) (Fin n) ℂ) + (t : ℂ) • ptX u = ptX ((0 : Matrix (Fin V.rank) (Fin n) ℂ) + (t : ℂ) • u) :=
        (ptX_add_smul _ _ t).symm
      rw [e2]
      exact hk _ u
    have hdiff : Differentiable ℝ F := fun t => (hF t).differentiableAt
    have hc := is_const_of_deriv_eq_zero hdiff (fun t => (hF t).deriv) 1 0
    have e1 : F 1 = evX Q u := by
      show eval (ptX (0 : Matrix (Fin V.rank) (Fin n) ℂ) + ((1 : ℝ) : ℂ) • ptX u) Q = eval (ptX u) Q
      rw [Complex.ofReal_one, one_smul]
      have e3 : ptX (0 : Matrix (Fin V.rank) (Fin n) ℂ) + ptX u = ptX u := by
        funext k
        obtain ⟨a, i, b⟩ := k
        cases b <;> simp [ptX]
      rw [e3]
    have e0 : F 0 = evX Q 0 := by
      show eval (ptX (0 : Matrix (Fin V.rank) (Fin n) ℂ) + ((0 : ℝ) : ℂ) • ptX u) Q = eval (ptX 0) Q
      rw [Complex.ofReal_zero, zero_smul, add_zero]
    rw [← e1, ← e0, hc]
  apply sub_eq_zero.1
  apply evX_eq_zero
  intro u
  show eval _ (Q - C (evX Q 0)) = 0
  rw [map_sub, eval_C]
  exact sub_eq_zero.2 (hconst u)

end PositivityTheory.Rg.Sw.Glob.RhoH
end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

theorem nbFacts : NbFacts := GlobalTheory.T.unipotent_map_continuous_additive

theorem charFacts : CharFacts := GlobalTheory.T.hermitian_character_continuous_unit

theorem gLamBd : GLamBd := gLamBd_of nbFacts charFacts hermCocompact

theorem splitTauP : SplitTauP := fun _ _ _ _ _ hθ hι g => splitTau hθ hι g

namespace LamTopH

theorem chiPer : ChiPer := by
  intro D n ψ hψ β l hl
  have hl' : (hermA D n).subtype l ∈ ratMx D n n := AddSubgroup.mem_comap.1 hl
  obtain ⟨γ, hγ⟩ := hl'
  have e : Matrix.trace (HMul.hMul (β.1.map (incA D)) l.1 : Mx D n n) = incA D (Matrix.trace (β.1 * γ)) := by
    change Matrix.trace (β.1.map (incA D) * ((hermA D n).subtype l)) = _
    rw [← hγ]
    change Matrix.trace (β.1.map (incA D) * γ.map (incA D)) = _
    rw [← Matrix.map_mul]
    exact (AddMonoidHom.map_trace (incA D).toAddMonoidHom (β.1 * γ)).symm
  rw [e]
  have h2 : -halfTr (incA D (Matrix.trace (β.1 * γ))) = halfTr (incA D (-(Matrix.trace (β.1 * γ)))) := by
    simp only [halfTr, map_neg, mul_neg]
  rw [h2]
  exact GlobalTheory.CompanionTheory.EisUnfold.Summand.psi_halfTr_incA ψ hψ _

theorem nbTauP : NbTauP := by
  intro D n ψ θ τ ι hψ hθ hι nb hnb nb' hnb'
  refine ⟨fun x => ?_, fun β => ?_⟩
  · obtain ⟨b, hb, -⟩ := nbTau hθ hι nb hnb nb' hnb' x
    exact ⟨b, hb⟩
  obtain ⟨l, hl⟩ := GlobalTheory.StdUnn.exists_realPar_of_isCharAF D ψ hψ θ hθ
  have hβh : (β.1.map (tauE D τ)).IsHermitian := by
    ext i j
    have h1 : (β.1.map (D.sp.cm.sig : D.host.E → D.host.E)).transpose = β.1 := β.2
    have h2 : D.sp.cm.sig (β.1 j i) = β.1 i j := by
      have := congrFun (congrFun h1 i) j
      simpa [Matrix.transpose_apply, Matrix.map_apply] using this
    have h3 : tauE D τ (D.sp.cm.sig (β.1 j i)) = starRingEnd ℂ (tauE D τ (β.1 j i)) := D.sp.cm.cmUnram.2.1 _ _
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply]
    rw [← h2, h3]
    rfl
  refine ⟨((l τ : ℝ) : ℂ) • β.1.map (tauE D τ), ?_, ?_, ?_⟩
  · unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, hβh.eq, Complex.star_def, Complex.conj_ofReal]
  · intro h0
    have h4 : (β.1.map (tauE D τ)).det = tauE D τ β.1.det := (RingHom.map_det (tauE D τ) β.1).symm
    rw [Matrix.det_smul, h4, h0, map_zero, mul_zero]
  · intro x b hb
    obtain ⟨b0, hb0, hfin, hτ, hoth, -⟩ := nbTau hθ hι nb hnb nb' hnb' x
    have hbb : b = b0 := by
      have h3 : nb b = nb b0 := hb.symm.trans hb0
      have hm := congrArg mat h3
      rw [hnb b, hnb b0] at hm
      have := congrArg PlaceFactsH.bOf hm
      rw [PlaceFactsH.upper_right_entry_block_matrix, PlaceFactsH.upper_right_entry_block_matrix] at this
      exact Subtype.ext this
    subst hbb
    set t := Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n) with ht
    have htfin : finPart D t = 0 := GlobalTheory.PhaseReal.finPart_trace _ _ hfin
    have hT := GlobalTheory.PhaseReal.trace_real htfin
    have hH : halfTr t = pairA D.host.F (fstA D.host.F (halfTr t)) 0 := by
      refine Prod.ext rfl ?_
      have h2 : (Algebra.trace (AF D.host.F) (AE D) t).2 = 0 := by rw [hT]; rfl
      show (algebraMap D.host.F (AF D.host.F) (1 / 2) * Algebra.trace (AF D.host.F) (AE D) t).2 = 0
      rw [show (algebraMap D.host.F (AF D.host.F) (1 / 2) * Algebra.trace (AF D.host.F) (AE D) t).2 =
        (algebraMap D.host.F (AF D.host.F) (1 / 2)).2 * (Algebra.trace (AF D.host.F) (AE D) t).2 from rfl, h2, mul_zero]
    rw [hH]
    have hpsi := hl (fstA D.host.F (halfTr t))
    rw [show psiInf D.host.F ψ (fstA D.host.F (halfTr t)) = ψ (pairA D.host.F (fstA D.host.F (halfTr t)) 0) from rfl]
      at hpsi
    rw [hpsi]

    have hθv : ∀ ρ, θ ρ (fstA D.host.F (halfTr t) ⊗ₜ[D.host.F] (1 : D.host.E)) = ((θ ρ (infPart D t)).re : ℂ) := by
      intro ρ
      have h2t : Algebra.trace (AF D.host.F) (AE D) t = algebraMap D.host.F (AF D.host.F) 2 * halfTr t := by
        show _ = algebraMap D.host.F (AF D.host.F) 2 *
          (algebraMap D.host.F (AF D.host.F) (1 / 2) * Algebra.trace (AF D.host.F) (AE D) t)
        rw [← mul_assoc, ← map_mul]
        norm_num
      have hf : fstA D.host.F (Algebra.trace (AF D.host.F) (AE D) t) = 2 * fstA D.host.F (halfTr t) := by
        rw [h2t, map_mul, AlgHom.commutes, map_ofNat]
      have hT2 := GlobalTheory.PhaseReal.theta_trace θ hθ ρ t
      rw [hf] at hT2
      have hmul : θ ρ ((2 * fstA D.host.F (halfTr t)) ⊗ₜ[D.host.F] (1 : D.host.E)) =
          2 * θ ρ (fstA D.host.F (halfTr t) ⊗ₜ[D.host.F] (1 : D.host.E)) := by
        have e : (2 * fstA D.host.F (halfTr t)) ⊗ₜ[D.host.F] (1 : D.host.E) =
            2 * (fstA D.host.F (halfTr t) ⊗ₜ[D.host.F] (1 : D.host.E)) := by
          rw [two_mul, TensorProduct.add_tmul, two_mul]
        rw [e, map_mul, map_ofNat]
      rw [hmul] at hT2
      push_cast at hT2
      linear_combination hT2 / 2
    simp_rw [hθv]
    have hpair : ∀ ρ, θ ρ (infPart D t) = Matrix.trace (β.1.map (tauE D ρ) * compAt θ ρ b.1) :=
      fun ρ => GlobalTheory.PhaseReal.theta_pair θ hθ ρ β.1 b.1
    rw [Finset.sum_eq_single τ]
    · rw [hpair, hτ]
      have hreal : (((Matrix.trace (β.1.map (tauE D τ) * herm x)).re : ℝ) : ℂ) =
          Matrix.trace (β.1.map (tauE D τ) * herm x) := by
        apply Complex.conj_eq_iff_re.1
        rw [← Complex.star_def, ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
          PlaceFactsH.herm_conjTranspose, hβh.eq, Matrix.trace_mul_comm]
      rw [hreal]
      simp only [eTr, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    · intro ρ _ hρ
      rw [hpair, hoth ρ hρ, Matrix.mul_zero, Matrix.trace_zero, Complex.zero_re, Complex.ofReal_zero, mul_zero]
    · intro h; exact absurd (Finset.mem_univ τ) h

end LamTopH

open LamTopH

theorem gLsing_of (hFZ : FourierZeroN) (hTS : TwoSided) (hD : DenseTau) : GLsing :=
  gLsing_core hFZ hTS hD GlobalTheory.T.coefficient_data_exists nbFacts charFacts hermCocompact splitTauP nbTauP chiPer

theorem gLsing (hTS : TwoSided) (hD : DenseTau) : GLsing := gLsing_of fourierZeroN hTS hD

end PositivityTheory.Rg.Sw.Glob
end
end
