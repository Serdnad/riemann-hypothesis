module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle002
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import GroundTheory.GlobalFields.ComplexMultiplication.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.Units.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
public import Mathlib.Analysis.Complex.Cardinality
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle002

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial TensorProduct

noncomputable section

theorem IndependentModBaseChange.proof : IndependentModBaseChange.Statement := by
  intro σ P r g hg
  let θ : MvPolynomial σ ℂ →ₐ[ℂ] ℂ ⊗[ℤ] (MvPolynomial σ ℤ ⧸ P) :=
    (Algebra.TensorProduct.map (AlgHom.id ℂ ℂ) (Ideal.Quotient.mkₐ ℤ P)).comp
      (MvPolynomial.algebraTensorAlgEquiv ℤ ℂ).symm.toAlgHom
  have hθ : ∀ p : MvPolynomial σ ℤ,
      θ (MvPolynomial.map (Int.castRingHom ℂ) p) = (1 : ℂ) ⊗ₜ Ideal.Quotient.mk P p := by
    intro p
    have h1 : MvPolynomial.map (Int.castRingHom ℂ) p =
        MvPolynomial.algebraTensorAlgEquiv ℤ ℂ ((1 : ℂ) ⊗ₜ p) := by
      rw [MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]
      congr 1
    rw [h1]
    change Algebra.TensorProduct.map (AlgHom.id ℂ ℂ) (Ideal.Quotient.mkₐ ℤ P)
      ((MvPolynomial.algebraTensorAlgEquiv ℤ ℂ).symm (MvPolynomial.algebraTensorAlgEquiv ℤ ℂ ((1 : ℂ) ⊗ₜ p))) = _
    rw [AlgEquiv.symm_apply_apply, Algebra.TensorProduct.map_tmul]
    rfl
  have hle : ∀ a ∈ P.map (MvPolynomial.map (Int.castRingHom ℂ)), θ a = 0 := by
    have hker : P.map (MvPolynomial.map (Int.castRingHom ℂ)) ≤ RingHom.ker θ := by
      rw [Ideal.map_le_iff_le_comap]
      intro p hp
      rw [Ideal.mem_comap, RingHom.mem_ker, hθ, Ideal.Quotient.eq_zero_iff_mem.mpr hp, tmul_zero]
    exact fun a ha => hker ha
  let ψ := Ideal.Quotient.liftₐ _ θ hle
  have key : LinearIndependent ℂ (fun i => (1 : ℂ) ⊗ₜ[ℤ] Ideal.Quotient.mk P (g i)) :=
    Module.Flat.linearIndependent_one_tmul hg
  have hfun : (ψ.toLinearMap ∘ fun i => Ideal.Quotient.mk (P.map (MvPolynomial.map (Int.castRingHom ℂ)))
      (MvPolynomial.map (Int.castRingHom ℂ) (g i))) = fun i => (1 : ℂ) ⊗ₜ[ℤ] Ideal.Quotient.mk P (g i) := by
    funext i
    exact hθ (g i)
  rw [← hfun] at key
  exact key.of_comp

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open Filter Topology

theorem PolyNonnegAtZero.proof : PolyNonnegAtZero.Statement := by
  intro d p c hc hdom hev
  by_contra h0
  push Not at h0
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  let S : Set ℝ := {t | 0 ≤ t ∧ p.eval t ≤ 0}
  have h0S : (0 : ℝ) ∈ S := ⟨le_rfl, h0.le⟩
  have hbdd : BddAbove S := ⟨N, fun t ht => by
    by_contra hlt
    push Not at hlt
    exact absurd ht.2 (not_le.2 (hN t hlt.le))⟩
  have hclosed : IsClosed S :=
    (isClosed_le continuous_const continuous_id).inter
      (isClosed_le p.continuous continuous_const)
  have ht0S : sSup S ∈ S := hclosed.csSup_mem ⟨0, h0S⟩ hbdd
  obtain ⟨ht0nn, hpt0⟩ := ht0S
  have hpos : ∀ t, sSup S < t → 0 < p.eval t := by
    intro t ht
    by_contra hle
    push Not at hle
    exact absurd (le_csSup hbdd ⟨ht0nn.trans ht.le, hle⟩) (not_le.2 ht)
  have hlim : c * (sSup S) ^ d ≤ p.eval (sSup S) := by
    by_contra hlt
    push Not at hlt
    have hcont : Continuous fun t : ℝ => p.eval t - c * t ^ d :=
      p.continuous.sub (continuous_const.mul (continuous_pow d))
    have hev' : ∀ᶠ t in 𝓝 (sSup S), p.eval t - c * t ^ d < 0 :=
      hcont.continuousAt.eventually (gt_mem_nhds (by linarith))
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev'
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show sSup S < sSup S + ε by linarith)
    have hqpos : (0 : ℝ) < q := lt_of_le_of_lt ht0nn hq1
    have hd : dist (q : ℝ) (sSup S) < ε := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith
    have h1 := hball hd
    have h2 := hdom q (by exact_mod_cast hqpos) (hpos q hq1)
    linarith
  rcases ht0nn.lt_or_eq with htpos | htz
  · have : 0 < c * (sSup S) ^ d := mul_pos hc (pow_pos htpos d)
    linarith
  · have hp0 : 0 ≤ p.eval (sSup S) := le_trans (mul_nonneg hc.le (pow_nonneg ht0nn d)) hlim
    rw [← htz] at hp0
    linarith

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open NumberField NumberField.InfinitePlace NumberField.Units
  NumberField.Units.dirichletUnitTheorem

theorem UnitApprox.proof : UnitApprox.Statement := by
  intro F _ _ u hconj hsum
  classical
  let uw : InfinitePlace F → ℝ := fun w => u w.embedding
  have hu_mk : ∀ sg, u sg = uw (InfinitePlace.mk sg) := by
    intro sg
    rcases embedding_mk_eq sg with h | h
    · simp only [uw, h]
    · simp only [uw, h, hconj]
  have hsum' : ∑ w : InfinitePlace F, (mult w : ℝ) * uw w = 0 := by
    rw [← hsum, ← Finset.sum_fiberwise Finset.univ (fun sg => InfinitePlace.mk sg) u]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.sum_congr rfl (g := fun _ => uw w), Finset.sum_const, nsmul_eq_mul,
      card_filter_mk_eq]
    intro sg hsg
    rw [Finset.mem_filter] at hsg
    rw [hu_mk, hsg.2]
  let b := (basisUnitLattice F).ofZLatticeBasis ℝ (unitLattice F)
  let R : ℝ := ∑ i, ‖b i‖
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hcard : (1 : ℝ) ≤ Fintype.card (InfinitePlace F) := by exact_mod_cast Fintype.card_pos
  refine ⟨Fintype.card (InfinitePlace F) * R, fun n => ?_⟩
  let v : logSpace F := fun w => n * ((mult w.val : ℝ) * uw w.val)
  have hfl : ((ZSpan.floor b v : _) : logSpace F) ∈ unitLattice F := by
    rw [← (basisUnitLattice F).ofZLatticeBasis_span ℝ (unitLattice F)]
    exact (ZSpan.floor b v).2
  obtain ⟨x, -, hx⟩ := Submodule.mem_map.mp hfl
  refine ⟨Additive.toMul x, ?_⟩
  set ε := Additive.toMul x with hε
  have hfr : ‖v - (ZSpan.floor b v : logSpace F)‖ ≤ R := by
    simpa [ZSpan.fract_apply] using ZSpan.norm_fract_le b v
  let e : InfinitePlace F → ℝ := fun w =>
    mult w * (Real.log (w ((ε : 𝓞 F) : F)) - n * uw w)
  have he_ne : ∀ w (hw : w ≠ w₀), |e w| ≤ R := by
    intro w hw
    have h1 := norm_le_pi_norm (v - (ZSpan.floor b v : logSpace F)) ⟨w, hw⟩
    rw [← hx] at h1
    have h2 : (logEmbedding F).toIntLinearMap x ⟨w, hw⟩
        = mult w * Real.log (w ((ε : 𝓞 F) : F)) := rfl
    rw [Pi.sub_apply, h2, Real.norm_eq_abs] at h1
    have h3 : e w = -(v ⟨w, hw⟩ - mult w * Real.log (w ((ε : 𝓞 F) : F))) := by
      simp only [e, v]; ring
    rw [h3, abs_neg]
    rw [← hx] at hfr
    linarith
  have he_sum : ∑ w, e w = 0 := by
    have h := sum_mult_mul_log ε
    have h2 : ∑ w : InfinitePlace F, (mult w : ℝ) * (n * uw w)
        = n * ∑ w, (mult w : ℝ) * uw w := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    simp only [e, mul_sub, Finset.sum_sub_distrib, h2, hsum', mul_zero, sub_zero]
    exact h
  have he : ∀ w, |e w| ≤ Fintype.card (InfinitePlace F) * R := by
    intro w
    by_cases hw : w = w₀
    · subst hw
      have h := Finset.add_sum_erase Finset.univ e (Finset.mem_univ w₀)
      rw [he_sum] at h
      have h3 : e w₀ = -∑ w ∈ Finset.univ.erase w₀, e w := by linarith
      rw [h3, abs_neg]
      calc |∑ w ∈ Finset.univ.erase w₀, e w| ≤ ∑ w ∈ Finset.univ.erase w₀, |e w| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _w ∈ Finset.univ.erase w₀, R :=
            Finset.sum_le_sum fun w hw => he_ne w (Finset.ne_of_mem_erase hw)
        _ ≤ _ := by
          rw [Finset.sum_const, nsmul_eq_mul]
          gcongr
          exact_mod_cast (Finset.card_erase_le).trans (le_of_eq Finset.card_univ)
    · exact (he_ne w hw).trans (le_mul_of_one_le_left hR0 hcard)
  intro sg
  have hm : (1 : ℝ) ≤ mult (InfinitePlace.mk sg) := one_le_mult
  have h4 : |Real.log ‖sg ((ε : 𝓞 F) : F)‖ - n * u sg| ≤ |e (InfinitePlace.mk sg)| := by
    simp only [e, abs_mul, hu_mk sg, InfinitePlace.apply, Nat.abs_cast]
    exact le_mul_of_one_le_left (abs_nonneg _) hm
  exact h4.trans (he _)

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace FSLevi

variable {J : Type} [Fintype J]

def reP (p : J) : (J → ℂ) →L[ℝ] ℝ := Complex.reCLM.comp (ContinuousLinearMap.proj p)

def imaginary (p : J) : (J → ℂ) →L[ℝ] ℝ := Complex.imCLM.comp (ContinuousLinearMap.proj p)

def nsq (z : J → ℂ) : ℝ := ∑ p, (reP p z ^ 2 + imaginary p z ^ 2)

theorem reP_apply (p : J) (z : J → ℂ) : reP p z = (z p).re := rfl

theorem imaginaryPart_apply (p : J) (z : J → ℂ) : imaginary p z = (z p).im := rfl

theorem norm_sq_eq (w : ℂ) : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

theorem nsq_pos {z : J → ℂ} (hz : z ≠ 0) : 0 < nsq z := by
  obtain ⟨p, hp⟩ := Function.ne_iff.mp hz
  refine Finset.sum_pos' (fun q _ ↦ by positivity) ⟨p, Finset.mem_univ _, ?_⟩
  rw [reP_apply, imaginaryPart_apply, ← norm_sq_eq]
  exact pow_pos (norm_pos_iff.mpr hp) 2

end FSLevi

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

noncomputable section

namespace PieceDegreeAlt

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {F : Type} [Field F] [Algebra F Ω]




theorem exists_ringEquiv_comp [NumberField F] (sg sg' : F →+* ℂ) :
    ∃ τ : ℂ ≃+* ℂ, (τ : ℂ →+* ℂ).comp sg = sg' := by
  have hc : Countable F := Countable.of_equiv _ (Module.finBasis ℚ F).equivFun.toEquiv.symm
  have hΩ : Cardinal.aleph0 < Cardinal.mk ℂ := by
    rw [Cardinal.mk_complex]
    exact Cardinal.aleph0_lt_continuum
  have h1 := @GroundTheory.Global.trdeg_eq_cardinalMk_of_countable ℂ _ _ F _ sg.toAlgebra hc hΩ
  have h2 := @GroundTheory.Global.trdeg_eq_cardinalMk_of_countable ℂ _ _ F _ sg'.toAlgebra hc hΩ
  obtain ⟨τ, hτ⟩ := @GroundTheory.Global.exists_ringEquiv_extend_of_trdeg_eq ℂ _ _ F F _ _ sg.toAlgebra sg'.toAlgebra
    (RingEquiv.refl F) (h1.trans h2.symm)
  exact ⟨τ, RingHom.ext fun a => hτ a⟩

end PieceDegreeAlt

open PieceDegreeAlt

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
