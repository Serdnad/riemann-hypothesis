module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.AbsInvOf
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.NormLtOneOfIrreducible
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison TensorProduct GlobalTheory.LogCris DividedPowers UpperTheory.Ru.crystallineComparison

private theorem cc_sW {l : ℕ} [Fact l.Prime] (A : PAlg l) (y : Ainf l) :
    WittVector.constantCoeff (A.sW y) = A.s (WittVector.constantCoeff y) :=
  WittVector.map_coeff A.s y 0

private theorem cc_xi {l : ℕ} [Fact l.Prime] (A : PAlg l) :
    WittVector.constantCoeff A.xi = - A.s (pFlat l) := by
  have h : WittVector.constantCoeff (xi0 l) = - pFlat l := by
    rw [xi0, map_sub, map_natCast, CharP.cast_eq_zero, zero_sub]
    congr 1
  rw [PAlg.xi, cc_sW, h, map_neg]

private theorem cc_of_thetaN {l : ℕ} [Fact l.Prime] (A : PAlg l) (z : A.W) (hz : A.toAcr 1 z ∈ A.PFil 1) :
    WittVector.constantCoeff z ∈ Ideal.span {A.s (pFlat l)} := by
  have hl : (l : A.Acr 1) = 0 := by simpa using A.pow_l_acr 1
  have h1 : A.toAcr 1 z ∈ A.Fil 1 1 := by
    rw [PAlg.PFil, hl, Ideal.span_singleton_eq_bot.2 rfl, bot_sup_eq] at hz
    exact hz
  rw [← A.ker_thetaN, RingHom.mem_ker, A.thetaN_toAcr, Ideal.Quotient.eq_zero_iff_mem] at h1
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h1
  obtain ⟨c', rfl⟩ : ∃ c', A.th c' = c := Ideal.Quotient.mk_surjective c
  have h2 : z - c' * (l : A.W) ∈ Ideal.span {A.xi} := by
    apply Ideal.Quotient.eq_zero_iff_mem.1
    change A.th _ = 0
    rw [map_sub, map_mul, map_natCast, ← hc, pow_one, sub_self]
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 h2
  have h3 := congrArg (WittVector.constantCoeff (p := l) (R := A.A)) hd
  rw [map_mul, map_sub, map_mul, map_natCast, A.natCast_l, mul_zero, sub_zero, cc_xi] at h3
  rw [← h3]
  exact Ideal.mul_mem_left _ _ (neg_mem (Ideal.mem_span_singleton_self _))

theorem UpperTheory.integersResidue_eq_theta_coeff_pow_of_teichmuller :
    ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : Res l K) (N : ℕ), Pb.Mid.TeichmullerCongruence r N → ∀ (x : OK l K) (w : Ainf l),
        theta0 l w = okToOC l K x → gRes r x = Ideal.Quotient.mk _ (w.coeff 0) ^ l ^ N := by
  intro l _ K r N hT x w hw
  obtain ⟨w', hw'⟩ := WittVector.constantCoeff_surjective (p := l) (R := r.k) (r.ρ x)
  have T := hT 1 x
  rw [Pb.Mid.phiQ_pow] at T
  have e1 : B.κb (okToOC l K) true 1 x =
      Ideal.Quotient.mk _ ((PAlg.base l).toAcr 1 ((PAlg.base l).sW w)) := by
    change B.uJ true (PAlg.base l) 1 ((PAlg.base l).oC (okToOC l K x)) = _
    rw [← hw, PAlg.oC_theta0, B.uJ_th]
  have e2 : Pb.Mid.κm r 1 x =
      Ideal.Quotient.mk _ ((PAlg.base l).toAcr 1 ((PAlg.base l).sW (WittVector.map r.s w'))) := by
    change Ideal.quotientMap _ (Pb.Mid.wn r 1) (Pb.Mid.im_le r 1) (Wc.res l r.k 1 (r.ρ x)) = _
    rw [← hw', Wc.res_coeff, Ideal.quotientMap_mk, Pb.Mid.wn_mk]
    change Ideal.Quotient.mk _ ((PAlg.base l).cris 1 (algebraMap (Ainf l) (Acris l) (WittVector.map r.s w'))) = _
    rw [PAlg.cris_algebraMap]
  rw [e1, e2, ← map_pow] at T
  have hz : (PAlg.base l).toAcr 1 ((PAlg.base l).sW w ^ l ^ N - (PAlg.base l).sW (WittVector.map r.s w')) ∈
      (PAlg.base l).PFil 1 := by
    rw [map_sub, map_pow]
    exact Ideal.Quotient.eq.1 T
  have hc := cc_of_thetaN (PAlg.base l) _ hz
  rw [map_sub, map_pow, cc_sW, cc_sW] at hc
  have e3 : WittVector.constantCoeff (WittVector.map r.s w') = r.s (r.ρ x) := by
    rw [← hw']
    exact WittVector.map_coeff r.s w' 0
  rw [e3] at hc
  change Ideal.Quotient.mk _ (r.s (r.ρ x)) = _
  rw [← map_pow, eq_comm, Ideal.Quotient.eq]
  exact hc
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison TensorProduct GlobalTheory.LogCris DividedPowers UpperTheory.Ru.crystallineComparison

theorem UpperTheory.integersResidue_eq_zero_of_not_isUnit :
    ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : Res l K) (ϖ : OK l K), ¬ IsUnit ϖ → gRes r ϖ = 0 := by
  intro l _ K r ϖ hϖ
  have hu0 : (PreTilt.untilt (0 : Ob l) : OC l) = 0 := by
    rw [← WittVector.fontaineTheta_teichmuller, WittVector.teichmuller_zero, map_zero]
  have hnorm : ∀ x : OK l K, ‖((okToOC l K x : OC l) : ℂ_[l])‖ = ‖((x : K) : PadicAlgCl l)‖ :=
    fun x => norm_clToC _
  have hker : ∀ z : OK l K, r.ρ z = 0 → ‖((z : K) : PadicAlgCl l)‖ < 1 := fun z hz => by
    have h := r.hs z
    rw [hz, map_zero, hu0, zero_sub] at h
    have e : ((-(okToOC l K z) : OC l) : ℂ_[l]) = -((okToOC l K z : OC l) : ℂ_[l]) := rfl
    rw [e, norm_neg, hnorm] at h
    exact h
  have hρ : r.ρ ϖ = 0 := by
    by_contra hne
    obtain ⟨y, hy⟩ := r.surj (r.ρ ϖ)⁻¹
    have hz : r.ρ (1 - ϖ * y) = 0 := by
      rw [map_sub, map_one, map_mul, hy, mul_inv_cancel₀ hne, sub_self]
    have h1 := hker _ hz
    have hsum : ((ϖ * y : OK l K) : K) = 1 - ((1 - ϖ * y : OK l K) : K) := by
      push_cast; ring
    have hlt : ‖(((ϖ * y : OK l K) : K) : PadicAlgCl l)‖ = 1 := by
      have e : (((ϖ * y : OK l K) : K) : PadicAlgCl l) = 1 - (((1 - ϖ * y : OK l K) : K) : PadicAlgCl l) := by
        rw [hsum]; push_cast; rfl
      refine le_antisymm (by simpa using norm_OK_le (ϖ * y)) ?_
      have h4 : ‖(1 : PadicAlgCl l)‖ ≤ max ‖(((ϖ * y : OK l K) : K) : PadicAlgCl l)‖ ‖(((1 - ϖ * y : OK l K) : K) : PadicAlgCl l)‖ := by
        have e' : (1 : PadicAlgCl l) = (((ϖ * y : OK l K) : K) : PadicAlgCl l) + (((1 - ϖ * y : OK l K) : K) : PadicAlgCl l) := by
          rw [e]; ring
        conv_lhs => rw [e']
        exact IsUltrametricDist.norm_add_le_max _ _
      rw [norm_one] at h4
      rcases le_max_iff.1 h4 with h5 | h5
      · exact h5
      · exact absurd h5 (not_le.2 h1)
    have hmul : ‖((ϖ : K) : PadicAlgCl l)‖ * ‖((y : K) : PadicAlgCl l)‖ = 1 := by
      rw [← norm_mul]; simpa using hlt
    have h2 := norm_OK_le ϖ
    have h3 := norm_OK_le y
    apply hϖ
    rw [isUnit_OK_iff]
    nlinarith [norm_nonneg ((ϖ : K) : PadicAlgCl l), norm_nonneg ((y : K) : PadicAlgCl l)]
  show Ideal.Quotient.mk _ (r.s (r.ρ ϖ)) = 0
  rw [hρ, map_zero, map_zero]
end
