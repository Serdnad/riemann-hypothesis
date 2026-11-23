module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle879
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CmBridge
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.Bundle001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle006
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle003
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle001
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ContinuousPrN
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle002
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle011
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Dynamics.Ergodic.Action.Regular
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CycCOfCyclic

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

private theorem tsum_split (δ : ℚ) (f : (Fin 4 → ℚ) → ℂ) (hf : Summable f) :
    ∑' ξ, f ξ = f 0 + (∑' ξ : ({ξ | ξ ≠ 0 ∧ qr δ ξ = 0} : Set (Fin 4 → ℚ)), f ξ) +
      ∑' ξ : ({ξ | qr δ ξ ≠ 0} : Set (Fin 4 → ℚ)), f ξ := by
  set R : Set (Fin 4 → ℚ) := {ξ | ξ ≠ 0 ∧ qr δ ξ = 0}
  set Q : Set (Fin 4 → ℚ) := {ξ | qr δ ξ ≠ 0}
  have h0 : qr δ 0 = 0 := by simp [qr]
  have hpt : ∀ ξ, f ξ = (({0} : Set (Fin 4 → ℚ)).indicator f ξ + R.indicator f ξ) + Q.indicator f ξ := by
    intro ξ
    by_cases hq : qr δ ξ = 0
    · by_cases hξ : ξ = 0
      · subst hξ
        simp [R, Q, h0]
      · simp [R, Q, hξ, hq]
    · have hξ : ξ ≠ 0 := fun e => hq (e ▸ h0)
      simp [R, Q, hξ, hq]
  have s0 := hf.indicator ({0} : Set (Fin 4 → ℚ))
  have sR := hf.indicator R
  have sQ := hf.indicator Q
  rw [tsum_subtype R f, tsum_subtype Q f]
  have e0 : ∑' ξ, ({0} : Set (Fin 4 → ℚ)).indicator f ξ = f 0 := by
    rw [← tsum_subtype]; simp
  rw [← e0, ← (s0.tsum_add sR), ← ((s0.add sR).tsum_add sQ)]
  exact tsum_congr hpt

private theorem cD_one (g : G1 ℚ) : cD 1 g = g := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cD]

private theorem ab_one' : ab (1 : (A ℚ)ˣ) = 1 := by
  simp [ab]

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {D : Dat ℚ E}

private theorem act_zero (h : GL (Fin 2) (A E)) : D.act h (0 : V4 ℚ) = 0 := by
  have e : D.herm (0 : V4 ℚ) = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Dat.herm, Dat.mkE]
  have e2 : D.unherm (0 : Matrix (Fin 2) (Fin 2) (A E)) = 0 := by
    funext i
    fin_cases i <;> simp [Dat.unherm, Dat.co]
  simp [Dat.act, e, e2]

private theorem om_zero (W : Weil D) (g : G1 ℚ) (ph : S4 ℚ) (x : GL (Fin 2) (A E)) (hx : nu ℚ x = 1) :
    (W.Om g (W.L x ph)).1 (rp 0) = (W.Om g ph).1 (rp 0) := by
  have h1 := W.comm x g
  rw [hx, cD_one] at h1
  have h2 : W.Om g (W.L x ph) = W.L x (W.Om g ph) := by
    have := congrArg (fun T : Module.End ℂ (S4 ℚ) => T ph) h1
    simpa [Module.End.mul_apply] using this.symm
  have hz : rp (0 : Fin 4 → ℚ) = (0 : V4 ℚ) := by
    funext i; simp [rp]
  rw [h2, W.L_apply, hx, ab_one', hz, act_zero]
  simp

private theorem core (hMaj : Maj) (hTh : ThCont) (hMean : MeanZero) (hR1 : Rank1)
    (W : Weil D) (M : Meas ℚ) (N : MeasE E) (P : CuspSub E 2) (hV : N.μ N.D < ⊤)
    (ph : S4 ℚ) (hph : ph ∈ Fock D.δ) (φ : Sm E 2) (hφ : φ ∈ P.V) (g : G1 ℚ)
    (y : GL (Fin 2) (A E)) (hy : nu ℚ y = 1) (hgl : ∀ h : G1 E, nu ℚ (gl h) = 1) :
    (mean N fun x => Th (W.Om g (W.L (x * y) ph)).1 * φ.1 (x * y)) =
      mean N fun x => ThOn {ξ | qr D.δ ξ ≠ 0} (W.Om g (W.L (x * y) ph)).1 * φ.1 (x * y) := by
  obtain ⟨b, a, k', hk', hg⟩ := UpperTheory.ConvolutionTheory.R2.M.iwa ℚ g
  have hapos : 0 < ab a := (IdeleGroup.ideleModule ℚ a).2
  obtain ⟨B, hB⟩ := hMaj E D W M N P ph hph φ hφ {y} isCompact_singleton
    (by rintro k rfl; exact hy) (ab a) hapos 0
  have hB' : ∀ h : G1 E, (Summable fun ξ : Fin 4 → ℚ => ‖(W.Om g (W.L (gl h * y) ph)).1 (rp ξ)‖) ∧
      (∑' ξ : Fin 4 → ℚ, ‖(W.Om g (W.L (gl h * y) ph)).1 (rp ξ)‖) * ‖φ.1 (gl h * y)‖ ≤ B * ab a ^ 2 := by
    intro h
    have := hB b a k' hk' le_rfl h y rfl
    rw [← hg] at this
    exact ⟨this.1, this.2.1⟩
  have hnu : ∀ h : G1 E, nu ℚ (gl h * y) = 1 := fun h => by rw [nu_mul, hgl, hy, one_mul]
  have hcφ : Continuous φ.1 := GlobalTheory.T.automorphicForm_GL_continuous E 2 φ (P.cusp φ hφ).1
  have hcg : Continuous fun h : G1 E => gl h := by fun_prop
  have hcx : Continuous fun h : G1 E => gl h * y := hcg.mul continuous_const
  haveI : IsFiniteMeasure (N.μ.restrict N.D) := ⟨by simpa using hV⟩
  have hint : ∀ S : Set (Fin 4 → ℚ), IntegrableOn
      (fun h : G1 E => ThOn S (W.Om g (W.L (gl h * y) ph)).1 * φ.1 (gl h * y)) N.D N.μ := by
    intro S
    have hc1 : Continuous fun h : G1 E => ThOn S (W.Om g (W.L (gl h * y) ph)).1 :=
      (hTh E D W M N P ph hph S).comp_continuous (f := fun h : G1 E => (g, gl h * y))
        (continuous_const.prodMk hcx) (fun h => hnu h)
    have hc : Continuous fun h : G1 E => ThOn S (W.Om g (W.L (gl h * y) ph)).1 * φ.1 (gl h * y) :=
      hc1.mul (hcφ.comp hcx)
    refine Integrable.of_bound hc.aestronglyMeasurable (B * ab a ^ 2) (Eventually.of_forall fun h => ?_)
    obtain ⟨hs, hb⟩ := hB' h
    have hle : ‖ThOn S (W.Om g (W.L (gl h * y) ph)).1‖ ≤
        ∑' ξ : Fin 4 → ℚ, ‖(W.Om g (W.L (gl h * y) ph)).1 (rp ξ)‖ := by
      have hsS := hs.subtype (fun x => x ∈ S)
      refine (norm_tsum_le_tsum_norm hsS).trans ?_
      exact tsum_comp_le_tsum_of_inj hs (fun _ => norm_nonneg _) Subtype.val_injective
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right hle (norm_nonneg _)).trans hb
  set c : ℂ := (W.Om g ph).1 (rp 0)
  have hz : ∀ h : G1 E, ThOn {0} (W.Om g (W.L (gl h * y) ph)).1 = c := by
    intro h
    have e : ThOn {0} (W.Om g (W.L (gl h * y) ph)).1 = (W.Om g (W.L (gl h * y) ph)).1 (rp 0) := by
      simp [ThOn]
    rw [e]
    exact om_zero W g ph _ (hnu h)
  have hφi : IntegrableOn (fun h : G1 E => c * φ.1 (gl h * y)) N.D N.μ := by
    refine (hint {0}).congr (Eventually.of_forall fun h => ?_)
    simp only [hz]
  have hpt : ∀ h : G1 E, Th (W.Om g (W.L (gl h * y) ph)).1 * φ.1 (gl h * y) =
      c * φ.1 (gl h * y) +
        ThOn {ξ | ξ ≠ 0 ∧ qr D.δ ξ = 0} (W.Om g (W.L (gl h * y) ph)).1 * φ.1 (gl h * y) +
        ThOn {ξ | qr D.δ ξ ≠ 0} (W.Om g (W.L (gl h * y) ph)).1 * φ.1 (gl h * y) := by
    intro h
    have hsp := tsum_split D.δ (fun ξ => (W.Om g (W.L (gl h * y) ph)).1 (rp ξ)) (hB' h).1.of_norm
    have e0 : (W.Om g (W.L (gl h * y) ph)).1 (rp 0) = c := om_zero W g ph _ (hnu h)
    have : Th (W.Om g (W.L (gl h * y) ph)).1 = c + ThOn {ξ | ξ ≠ 0 ∧ qr D.δ ξ = 0} (W.Om g (W.L (gl h * y) ph)).1 +
        ThOn {ξ | qr D.δ ξ ≠ 0} (W.Om g (W.L (gl h * y) ph)).1 := by
      rw [← e0]
      exact hsp
    rw [this]
    ring
  have z1 : ∫ h in N.D, φ.1 (gl h * y) ∂N.μ = 0 := hMean E D W M N P φ hφ y
  have z2 : ∫ h in N.D, ThOn {ξ | ξ ≠ 0 ∧ qr D.δ ξ = 0} (W.Om g (W.L (gl h * y) ph)).1 * φ.1 (gl h * y) ∂N.μ = 0 :=
    hR1 E D W M N P ph hph φ hφ g y hy
  simp only [mean]
  simp only [hpt]
  have i1 : IntegrableOn (fun h : G1 E => c * φ.1 (gl h * y) +
      ThOn {ξ | ξ ≠ 0 ∧ qr D.δ ξ = 0} (W.Om g (W.L (gl h * y) ph)).1 * φ.1 (gl h * y)) N.D N.μ := hφi.add (hint _)
  rw [integral_add i1 (hint _), integral_add hφi (hint _), integral_const_mul, z1, z2]
  simp

end UpperTheory.ConvolutionTheory.RankTwoDescent

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.f0Eq :
    Maj → ThCont → MeanZero → Rank1 → ThetaLiftEqAnisotropicPart := by
  intro hMaj hTh hMean hR1 E _ _ _ D W M N P ph hph φ hφ
  funext g
  have hS := szLaws E D
  simp only [f0, fOn, J1]
  refine congrArg (UI (E := E)) (funext fun z => ?_)
  exact core hMaj hTh hMean hR1 W M N P (UpperTheory.ConvolutionTheory.RankTwoDescent.volE E N) ph hph φ hφ g (sZ D z) (hS.2.2.1 z) hS.2.2.2.1
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

namespace UpperTheory.ConvolutionTheory.RankTwoDescent.UnitaryMatrixFamily

private theorem char_int (r : ℚ) (hr : r ≠ 0) :
    ∫ b in fundamentalSet ℚ, ψ (b * rt r) ∂(adeleMeasure ℚ) = 0 := by
  obtain ⟨x, hx⟩ : ∃ x : A ℚ, adelicChar ℚ x ≠ 1 := by
    by_contra h
    push_neg at h
    exact adelicChar_ne_one (K := ℚ) (DFunLike.ext _ _ fun x => by simpa using h x)
  have hx' : ψ x ≠ 1 := fun h => hx (Circle.ext (by simpa [ψ] using h))
  have hper : ∀ (k : ℚ) (y : A ℚ), ψ ((rt k + y) * rt r) = ψ (y * rt r) := by
    intro k y
    rw [add_mul, Pp.ψ_add, ← map_mul, Pp.ψ_rt, one_mul]
  have h := Pp.int_add (F := ℚ) (h := fun b => ψ (b * rt r)) hper (rt r⁻¹ * x)
  have hrr : rt r⁻¹ * rt r = (1 : A ℚ) := by rw [← map_mul, inv_mul_cancel₀ hr, map_one]
  have e : ∀ b : A ℚ, ψ ((b + rt r⁻¹ * x) * rt r) = ψ (b * rt r) * ψ x := by
    intro b
    rw [add_mul, Pp.ψ_add, mul_right_comm, hrr, one_mul]
  simp only [e] at h
  rw [integral_mul_const] at h
  have h1 : (∫ b in fundamentalSet ℚ, ψ (b * rt r) ∂(adeleMeasure ℚ)) * (ψ x - 1) = 0 := by
    rw [mul_sub, h, mul_one, sub_self]
  exact (mul_eq_zero.1 h1).resolve_right (sub_ne_zero.2 hx')

private theorem vol_one : (adeleMeasure ℚ).real (fundamentalSet ℚ) = 1 := by
  rw [measureReal_def, adeleMeasure_fundamentalSet, ENNReal.toReal_one]

private theorem fourier (S T : Set (Fin 4 → ℚ)) (q : (Fin 4 → ℚ) → ℚ) (t : ℚ) (c : (Fin 4 → ℚ) → ℂ)
    (hT : ∀ ξ, ξ ∈ T ↔ ξ ∈ S ∧ q ξ = t) (hc : Summable fun ξ : S => ‖c ξ‖) :
    ∫ b in fundamentalSet ℚ, (∑' ξ : S, ψ (b * rt (q ξ)) * c ξ) * ψ (-(b * rt t)) ∂(adeleMeasure ℚ) =
      ∑' ξ : T, c ξ := by
  have hvol : ((adeleMeasure ℚ).restrict (fundamentalSet ℚ)) Set.univ = 1 := by
    rw [Measure.restrict_apply_univ, adeleMeasure_fundamentalSet]
  haveI : IsProbabilityMeasure ((adeleMeasure ℚ).restrict (fundamentalSet ℚ)) := ⟨hvol⟩
  set G : S → A ℚ → ℂ := fun ξ b => ψ (b * rt (q ξ - t)) * c ξ with hG
  have hGc : ∀ ξ, Continuous (G ξ) := fun ξ =>
    (Pp.cont_ψ.comp (continuous_id.mul continuous_const)).mul continuous_const
  have hGn : ∀ ξ b, ‖G ξ b‖ = ‖c ξ‖ := fun ξ b => by simp [hG, Pp.norm_ψ]
  have e : ∀ b : A ℚ, (∑' ξ : S, ψ (b * rt (q ξ)) * c ξ) * ψ (-(b * rt t)) = ∑' ξ, G ξ b := by
    intro b
    rw [← tsum_mul_right]
    refine tsum_congr fun ξ => ?_
    have h0 : rt (q ξ - t) = rt (q ξ) - rt t := map_sub (algebraMap ℚ (A ℚ)) _ _
    have : b * rt (q ξ - t) = b * rt (q ξ) + -(b * rt t) := by
      rw [h0, mul_sub, sub_eq_add_neg]
    simp only [hG, this, Pp.ψ_add]
    ring
  simp only [e]
  have hS := hasSum_integral_of_summable_integral_norm (μ := (adeleMeasure ℚ).restrict (fundamentalSet ℚ))
    (F := G) (fun ξ => Pp.intOn (hGc ξ)) (by
      simp only [hGn, integral_const, probReal_univ, one_smul]
      exact hc)
  rw [← hS.tsum_eq]
  have term : ∀ ξ : S, ∫ b in fundamentalSet ℚ, G ξ b ∂(adeleMeasure ℚ) = T.indicator c ξ := by
    intro ξ
    simp only [hG]
    rw [integral_mul_const]
    by_cases h : q ξ = t
    · have hm : (ξ : Fin 4 → ℚ) ∈ T := (hT _).2 ⟨ξ.2, h⟩
      simp [h, hm, Set.indicator_of_mem, measureReal_def, hvol]
    · have hm : (ξ : Fin 4 → ℚ) ∉ T := fun hm => h ((hT _).1 hm).2
      rw [char_int _ (sub_ne_zero.2 h), zero_mul, Set.indicator_of_notMem hm]
  simp only [term]
  rw [tsum_subtype S (T.indicator c), tsum_subtype T c]
  refine tsum_congr fun ξ => ?_
  by_cases h : ξ ∈ T
  · simp [h, ((hT _).1 h).1]
  · by_cases h' : ξ ∈ S <;> simp [h, h']

private theorem swap3 {B Z H : Type} [MeasurableSpace B] [MeasurableSpace Z] [MeasurableSpace H]
    (m : Measure B) (μ₁ : Measure Z) (μ₂ : Measure H) [IsFiniteMeasure m] [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    (f : B → Z → H → ℂ) (hf : AEStronglyMeasurable (fun p : B × Z × H => f p.1 p.2.1 p.2.2) (m.prod (μ₁.prod μ₂)))
    (C : ℝ) (hb : ∀ᵐ z ∂μ₁, ∀ b h, ‖f b z h‖ ≤ C) :
    ∫ b, ∫ z, ∫ h, f b z h ∂μ₂ ∂μ₁ ∂m = ∫ z, ∫ h, ∫ b, f b z h ∂m ∂μ₂ ∂μ₁ := by
  have hae : ∀ᵐ p ∂(m.prod (μ₁.prod μ₂)), ‖f p.1 p.2.1 p.2.2‖ ≤ C := by
    have h1 : ∀ᵐ p ∂(μ₁.prod μ₂), ∀ b h, ‖f b p.1 h‖ ≤ C := Measure.quasiMeasurePreserving_fst.ae hb
    have h2 : ∀ᵐ p ∂(m.prod (μ₁.prod μ₂)), ∀ b h, ‖f b p.2.1 h‖ ≤ C := Measure.quasiMeasurePreserving_snd.ae h1
    exact h2.mono fun p hp => hp _ _
  have hF : Integrable (fun p : B × Z × H => f p.1 p.2.1 p.2.2) (m.prod (μ₁.prod μ₂)) :=
    Integrable.of_bound hf C hae
  have s1 : ∫ b, ∫ z, ∫ h, f b z h ∂μ₂ ∂μ₁ ∂m = ∫ b, ∫ p : Z × H, f b p.1 p.2 ∂(μ₁.prod μ₂) ∂m := by
    refine integral_congr_ae (hF.prod_right_ae.mono fun b hb' => ?_)
    exact (integral_prod _ hb').symm
  have s2 : ∫ b, ∫ p : Z × H, f b p.1 p.2 ∂(μ₁.prod μ₂) ∂m = ∫ p : Z × H, ∫ b, f b p.1 p.2 ∂m ∂(μ₁.prod μ₂) :=
    integral_integral_swap (f := fun b (p : Z × H) => f b p.1 p.2) hF
  rw [s1, s2]
  exact integral_prod (fun p : Z × H => ∫ b, f b p.1 p.2 ∂m) hF.integral_prod_right

end UpperTheory.ConvolutionTheory.RankTwoDescent.UnitaryMatrixFamily

open UpperTheory.ConvolutionTheory.RankTwoDescent.UnitaryMatrixFamily in
private theorem coefOf (hV : VolE) :
    Maj → ThCont → Coef := by
  intro hMaj hTh E _ _ _ D W M N P ph hph φ hφ t g
  obtain ⟨hs1, hsc, hnz, hng, -, -, -, -, -, -, hq⟩ := szLaws E D
  obtain ⟨b₀, a₀, k₀, hk₀, rfl⟩ := UpperTheory.ConvolutionTheory.R2.M.iwa ℚ g
  have hφc : Continuous φ.1 := by
    obtain ⟨ψ', hψ'⟩ := LinearMap.mem_range.mp (UpperTheory.V.Cm.mem_range_ofCusp.2 (P.cusp φ hφ))
    rw [← hψ']
    exact ψ'.2.1.continuous
  have hzc : Continuous fun u : IdeleGroup.normOneSubgroup E => sZ D (u : IdeleGroup E) :=
    hsc.comp continuous_subtype_val
  have hCc := (isCompact_closure_normOneFundamentalDomain E).image hzc
  have hCn : ∀ k ∈ (fun u : IdeleGroup.normOneSubgroup E => sZ D (u : IdeleGroup E)) '' closure (normOneFundamentalDomain E),
      nu ℚ k = 1 := by
    rintro _ ⟨u, -, rfl⟩
    exact hnz _
  have hapos : 0 < ab a₀ := (IdeleGroup.ideleModule ℚ a₀).2
  obtain ⟨B, hB⟩ := hMaj E D W M N P ph hph φ hφ _ hCc hCn (ab a₀) hapos 0
  set S : Set (Fin 4 → ℚ) := {ξ | qr D.δ ξ ≠ 0} with hS
  set T : Set (Fin 4 → ℚ) := {ξ | qr D.δ ξ ≠ 0 ∧ qr D.δ ξ = t} with hTd
  set g₀ : G1 ℚ := nU b₀ * mD a₀ * k₀ with hg₀
  let x : IdeleGroup.normOneSubgroup E → G1 E → GL (Fin 2) (A E) := fun z h => gl h * sZ D (z : IdeleGroup E)
  have hxc : Continuous fun p : IdeleGroup.normOneSubgroup E × G1 E => x p.1 p.2 := by
    have h1 : Continuous (gl : G1 E → GL (Fin 2) (A E)) := by fun_prop
    exact (h1.comp continuous_snd).mul (hzc.comp continuous_fst)
  have hnux : ∀ z h, nu ℚ (x z h) = 1 := fun z h => by
    have : nu ℚ (x z h) = nu ℚ (gl h) * nu ℚ (sZ D (z : IdeleGroup E)) := by simp [x, nu, map_mul]
    rw [this, hng, hnz, one_mul]
  let c : IdeleGroup.normOneSubgroup E → G1 E → (Fin 4 → ℚ) → ℂ := fun z h ξ => (W.Om g₀ (W.L (x z h) ph)).1 (rp ξ)
  have hterm : ∀ b z h ξ, (W.Om (nU b * g₀) (W.L (x z h) ph)).1 (rp ξ) = ψ (b * rt (qr D.δ ξ)) * c z h ξ := by
    intro b z h ξ
    rw [map_mul, Module.End.mul_apply, W.Om_n, hq]
  have hmaj := fun (b : A ℚ) (z : IdeleGroup.normOneSubgroup E) (hz : z ∈ normOneFundamentalDomain E) (h : G1 E) =>
    hB b a₀ k₀ hk₀ le_rfl h (sZ D (z : IdeleGroup E)) ⟨z, subset_closure hz, rfl⟩
  have hsum : ∀ z ∈ normOneFundamentalDomain E, ∀ h, Summable fun ξ : S => ‖c z h ξ‖ := fun z hz h =>
    (hmaj b₀ z hz h).1.subtype (fun ξ => ξ ∈ S)
  have hnU : ∀ b, nU (b + b₀) * mD a₀ * k₀ = nU b * g₀ := by
    intro b
    rw [UpperTheory.ConvolutionTheory.R2.M.nU_add]
    simp only [hg₀, mul_assoc]
  let T' : A ℚ → IdeleGroup.normOneSubgroup E → G1 E → ℂ := fun b z h =>
    ThOn S (W.Om (nU b * g₀) (W.L (x z h) ph)).1 * φ.1 (x z h)
  let f : A ℚ → IdeleGroup.normOneSubgroup E → G1 E → ℂ := fun b z h => T' b z h * ψ (-(b * rt t))
  have hbd : ∀ z ∈ normOneFundamentalDomain E, ∀ b h, ‖f b z h‖ ≤ B := by
    intro z hz b h
    have h1 := (hmaj (b + b₀) z hz h).1
    have h3 := (hmaj (b + b₀) z hz h).2.2
    simp only [hnU, pow_zero, mul_one] at h1 h3
    have h2 : ‖ThOn S (W.Om (nU b * g₀) (W.L (x z h) ph)).1‖ ≤
        ∑' ξ : {ξ : Fin 4 → ℚ // qr D.δ ξ ≠ 0}, ‖(W.Om (nU b * g₀) (W.L (gl h * sZ D (z : IdeleGroup E)) ph)).1 (rp ξ.1)‖ :=
      norm_tsum_le_tsum_norm (h1.subtype (fun ξ => ξ ∈ S))
    calc ‖f b z h‖ = ‖ThOn S (W.Om (nU b * g₀) (W.L (x z h) ph)).1‖ * ‖φ.1 (x z h)‖ := by
          simp only [f, T', norm_mul, Pp.norm_ψ, mul_one]
      _ ≤ _ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      _ ≤ B := h3
  have hNc : Continuous fun b : A ℚ => nU b := by
    refine Continuous.subtype_mk (continuous_matrix fun i j => ?_) _
    fin_cases i <;> fin_cases j <;> simp [nU] <;> fun_prop
  have hcont : Continuous fun p : A ℚ × IdeleGroup.normOneSubgroup E × G1 E => f p.1 p.2.1 p.2.2 := by
    have hp : Continuous fun p : A ℚ × IdeleGroup.normOneSubgroup E × G1 E => (nU p.1 * g₀, x p.2.1 p.2.2) :=
      ((hNc.comp continuous_fst).mul continuous_const).prodMk (hxc.comp continuous_snd)
    have h1 := (hTh E D W M N P ph hph S).comp_continuous hp (fun p => hnux _ _)
    exact (h1.mul (hφc.comp (hxc.comp continuous_snd))).mul
      (Pp.cont_ψ.comp ((continuous_fst.mul continuous_const).neg))
  haveI : IsFiniteMeasure ((adeleMeasure ℚ).restrict (fundamentalSet ℚ)) :=
    ⟨by rw [Measure.restrict_apply_univ, adeleMeasure_fundamentalSet]; exact ENNReal.one_lt_top⟩
  haveI : IsFiniteMeasure ((normOneMeasure E).restrict (normOneFundamentalDomain E)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact normOneMeasure_normOneFundamentalDomain_lt_top E⟩
  haveI : IsFiniteMeasure (N.μ.restrict N.D) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hV E N⟩
  have step : ∀ b, fOn W N S ph φ.1 (nU b * g₀) * ψ (-(b * rt t)) =
      ∫ z in normOneFundamentalDomain E, ∫ h in N.D, f b z h ∂N.μ ∂normOneMeasure E := by
    intro b
    change (∫ z in normOneFundamentalDomain E, ∫ h in N.D, T' b z h ∂N.μ ∂normOneMeasure E) * _ = _
    rw [← integral_mul_const]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    exact (integral_mul_const _ _).symm
  simp only [step]
  rw [swap3 _ _ _ f hcont.aestronglyMeasurable B
    (ae_restrict_of_forall_mem (measurableSet_normOneFundamentalDomain E) hbd), vol_one, Complex.ofReal_one, one_mul]
  change _ = ∫ z in normOneFundamentalDomain E, ∫ h in N.D, ThOn T (W.Om g₀ (W.L (x z h) ph)).1 * φ.1 (x z h) ∂N.μ ∂normOneMeasure E
  refine setIntegral_congr_fun (measurableSet_normOneFundamentalDomain E) fun z hz => ?_
  refine integral_congr_ae (ae_of_all _ fun h => ?_)
  have e : ∀ b, f b z h = ((∑' ξ : S, ψ (b * rt (qr D.δ ξ)) * c z h ξ) * ψ (-(b * rt t))) * φ.1 (x z h) := by
    intro b
    simp only [f, T', ThOn, hterm]
    ring
  simp only [e]
  rw [integral_mul_const, fourier S T (qr D.δ) t (c z h) (fun ξ => Iff.rfl) (hsum z hz h)]
  rfl

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.coef :
    Maj → ThCont → Coef :=
  coefOf volE
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.V.Z.Bc
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.RankTwoDescent

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.uiLaws :
    UILaws := by
  intro E _ _ β hc hinv
  have hf : Continuous fun z : IdeleGroup.normOneSubgroup E => β (z : IdeleGroup E) :=
    hc.comp continuous_subtype_val
  have hcl := isCompact_closure_normOneFundamentalDomain E
  have hinv' : ∀ (k : Eˣ) (u : IdeleGroup.normOneSubgroup E),
      β ((u * diagonalToNormOne E k : IdeleGroup.normOneSubgroup E) : IdeleGroup E) = β (u : IdeleGroup E) := by
    intro k u
    have h := hinv k (u : IdeleGroup E)
    rw [mul_comm] at h
    exact h
  refine ⟨?_, ?_, ?_⟩
  · exact (hf.continuousOn.integrableOn_compact hcl).mono_set subset_closure
  · obtain ⟨B, hB⟩ := hcl.exists_bound_of_continuousOn hf.continuousOn
    refine ⟨B, fun t ht => ?_⟩
    have hm : t ∈ IdeleGroup.normOneSubgroup E := by
      refine MonoidHom.mem_ker.2 (Subtype.ext ?_)
      exact ht
    obtain ⟨k, hk, -⟩ := existsUnique_mul_mem_normOneFundamentalDomain E ⟨t, hm⟩
    have h := hB _ (subset_closure hk)
    rwa [hinv' k ⟨t, hm⟩] at h
  · intro d hd
    have hm : d ∈ IdeleGroup.normOneSubgroup E := by
      refine MonoidHom.mem_ker.2 (Subtype.ext ?_)
      exact hd
    set b : IdeleGroup.normOneSubgroup E := ⟨d, hm⟩ with hb
    set g : IdeleGroup.normOneSubgroup E → ℂ := fun z => β (z : IdeleGroup E) with hg
    have hD := isFundamentalDomain_normOneFundamentalDomain E (normOneMeasure E)
    have hD' := hD.smul_of_comm b
    have hI : ∀ (γ : (diagonalNormOne E).op) (x : IdeleGroup.normOneSubgroup E), g (γ • x) = g x := by
      rintro ⟨γ, hγ⟩ x
      obtain ⟨k, hk⟩ := Subgroup.mem_op.1 hγ
      have e : γ.unop = diagonalToNormOne E k := Subtype.ext hk.symm
      change g (x * γ.unop) = g x
      rw [e]
      exact hinv' k x
    have h1 := hD.setIntegral_eq hD' hI
    have h2 := (measurePreserving_mul_left (normOneMeasure E) b).setIntegral_image_emb
      (MeasurableEquiv.mulLeft b).measurableEmbedding g (normOneFundamentalDomain E)
    unfold UI
    change ∫ z in normOneFundamentalDomain E, g (z * b) ∂normOneMeasure E = ∫ z in normOneFundamentalDomain E, g z ∂normOneMeasure E
    rw [h1]
    simp_rw [mul_comm _ b]
    exact h2.symm
end

section

open NumberField IsDedekindDomain
open Formalism.L2.Host GroundTheory.Global
open UpperTheory.ConvolutionTheory.R2

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

theorem charDown : CharDown := by
  intro E _ _ _ D χ h
  have hE : Module.finrank ℚ E = 2 := by
    rw [Module.finrank_eq_card_basis D.b]
    simp
  have hθ : D.θ ≠ 0 := by
    rw [← D.b1]
    exact D.b.ne_zero 1
  have hσ : D.σ ≠ 1 := by
    intro h1
    have h2 := D.conj
    rw [h1] at h2
    have h3 : D.θ = -D.θ := by simpa using h2
    have h4 : (2 : E) * D.θ = 0 := by linear_combination h3
    exact hθ (by simpa using h4)
  refine A.normChar_of_inv hE χ fun c z => ?_
  rcases GlobalTheory.AdLat.aut_eq_one_or_of_finrank_two D.σ hE hσ c with rfl | rfl
  · rw [one_smul]
  · have h1 := h z
    rw [map_mul, map_inv, mul_inv_eq_one] at h1
    have h2 : Units.map (D.bar : A E →* A E) z = D.σ • z := Units.ext (coe_smul_idele D.σ z).symm
    rw [← h2]
    exact h1.symm

end UpperTheory.ConvolutionTheory.RankTwoDescent
end
