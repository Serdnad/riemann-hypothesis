module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.Bundle002
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.Bundle003
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle005
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.EmbPiInjective
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle011
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ThMeas
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ZpowLeAbs
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle009
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle006
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle001
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.weilLift_one_cuspidal :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), UnfoldedThetaIntegralConvergesSimilitudeOne W M π := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ x
  have hL := (UpperTheory.ConvolutionTheory.R2.Pp.cuspZero F π f hf).1
  have hW := UpperTheory.ConvolutionTheory.R2.Pp.wfBasic F f.1 hL
  have hWc : Continuous fun g : G1 F => Wf f.1 (gl g * x) :=
    hW.1.comp (UpperTheory.ConvolutionTheory.R2.continuous_gl.mul continuous_const)
  have hm : ∀ φ : S4 F, Measurable fun g => Wf f.1 (gl g * x) * hat (W.Om g φ).1 ![0, 1, 1, 0] := fun φ =>
    hWc.measurable.mul ((thMeas F E D W φ).2.2.2.2 _)
  refine ⟨hm φ, ?_, ?_⟩
  · intro b g
    have h1 : Wf f.1 (gl (nU b * g) * x) = ψ (-b) * Wf f.1 (gl g * x) := by
      rw [UpperTheory.ConvolutionTheory.R2.gl_mul, mul_assoc]
      exact hW.2.1 b _
    have h2 : hat (W.Om (nU b * g) φ).1 ![0, 1, 1, 0] = ψ b * hat (W.Om g φ).1 ![0, 1, 1, 0] := by
      rw [map_mul, Module.End.mul_apply, (hatSt F E D W).n b (W.Om g φ) ![0, 1, 1, 0]]
      have e : Function.update ![(0 : A F), 1, 1, 0] 1 (![(0 : A F), 1, 1, 0] 1 + b * ![(0 : A F), 1, 1, 0] 0) = ![0, 1, 1, 0] := by
        ext i; fin_cases i <;> simp
      rw [e]
      simp
    rw [h1, h2]
    have h3 : ψ (-b) * ψ b = 1 := by
      rw [UpperTheory.ConvolutionTheory.R2.ψ_neg]; exact inv_mul_cancel₀ (UpperTheory.ConvolutionTheory.R2.ψ_ne_zero b)
    calc _ = (ψ (-b) * ψ b) * (Wf f.1 (gl g * x) * hat (W.Om g φ).1 ![0, 1, 1, 0]) := by ring
      _ = _ := by rw [h3, one_mul]
  · intro hφ y hy
    obtain ⟨N, hN⟩ := wtId F
    obtain ⟨K, hK, hB'⟩ := hatMaj F E D W φ hφ y hy
    obtain ⟨B', hB'⟩ := hB' N
    obtain ⟨B, hB⟩ := UpperTheory.ConvolutionTheory.R2.Pp.bdd F π f hf {x} isCompact_singleton
    have := M.prob
    have hI := (hN K hK).comp_fst M.κ
    have hmaj : Integrable (fun p : IdeleGroup F × G1 F => (B * B') * ((ab p.1)⁻¹ * wt K N ![0, ((p.1⁻¹ : (A F)ˣ) : A F), (p.1 : A F), 0])) M.ν :=
      hI.const_mul _
    refine hmaj.mono' ?_ ?_
    · have hc : Continuous fun p : IdeleGroup F × G1 F => mD p.1 * p.2 :=
        (UpperTheory.ConvolutionTheory.R2.continuous_mD.comp continuous_fst).mul continuous_snd
      have hab : Continuous fun p : IdeleGroup F × G1 F => ab p.1 :=
        UpperTheory.ConvolutionTheory.R2.continuous_ab.comp continuous_fst
      have hmm : Measurable (iw fun g => Wf f.1 (gl g * x) * hat (W.Om g (W.L (infGL E 2 y) φ)).1 ![0, 1, 1, 0]) :=
        (Complex.continuous_ofReal.comp ((hab.inv₀ fun p => UpperTheory.ConvolutionTheory.R2.ab_ne_zero _).pow 2)).measurable.mul
          ((hm (W.L (infGL E 2 y) φ)).comp hc.measurable)
      exact hmm.aestronglyMeasurable
    · have hk : ∀ᵐ p ∂M.ν, p.2 ∈ KK F := Measure.quasiMeasurePreserving_snd.ae (by
        have := M.supp
        exact measure_eq_zero_iff_ae_notMem.1 (by simpa using this) |>.mono (fun k hk => by simpa using hk))
      filter_upwards [hk] with p hp
      obtain ⟨a, k⟩ := p
      have hk' : k ∈ KK F := hp
      have h1 := (hB (mD a * k) x rfl).2
      have h2 := hB' 0 a k hk' 1 1 0
      rw [UpperTheory.ConvolutionTheory.R2.nU_zero, one_mul, mul_one, mul_one, mul_zero] at h2
      have hpos : 0 < ab a := UpperTheory.ConvolutionTheory.R2.ab_pos a
      have hB0 : 0 ≤ B := (norm_nonneg _).trans h1
      simp only [iw, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_pos (by positivity)]
      calc ((ab a)⁻¹ ^ 2) * (‖Wf f.1 (gl (mD a * k) * x)‖ * ‖hat (W.Om (mD a * k) (W.L (infGL E 2 y) φ)).1 ![0, 1, 1, 0]‖)
          ≤ ((ab a)⁻¹ ^ 2) * (B * (B' * ab a * wt K N ![0, ((a⁻¹ : (A F)ˣ) : A F), (a : A F), 0])) := by
            gcongr
        _ = _ := by field_simp
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.thDerOm :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D), ThDerOm W := by
  intro F E _ _ _ _ _ _ _ D W φ φ' hφ' G hG hD g h t

  have hcomm : ∀ (g : G1 F) (x : S4 F),
      W.Om g (W.L h x) = W.L h (W.Om (cD (nu F h)⁻¹ g) x) := by
    intro g x
    have e := W.comm h (cD (nu F h)⁻¹ g)
    rw [← cD_mul_left, mul_inv_cancel, cD_one_left] at e
    have e' := congrArg (fun T : Module.End ℂ (S4 F) => T x) e
    simpa only [Module.End.mul_apply] using e'.symm
  have hmul : ∀ (a b : G1 F) (x : S4 F), W.Om (a * b) x = W.Om a (W.Om b x) := by
    intro a b x
    rw [map_mul, Module.End.mul_apply]

  have hDL : Der (fun s => W.L h (W.Om (G s) φ)) (fun s => W.L h (W.Om (G s) φ')) := by
    intro s v
    simp only [W.L_apply]
    exact (hD s _).const_mul _

  have hdom : ∀ (g : G1 F) (t : ℝ),
      Dom (Metric.ball t 1) fun s => (W.Om g (W.L h (W.Om (G s) φ'))).1 := by
    intro g t
    let c : ℝ → G1 F := fun s => cD (nu F h)⁻¹ g * G s
    have hc : Continuous c := continuous_const.mul hG
    have hC : IsCompact (c '' Metric.closedBall t 1) := (isCompact_closedBall t 1).image hc
    obtain ⟨K, hK, hB⟩ := lDom F E D W (G1 F) (c '' Metric.closedBall t 1) (fun k => W.Om k φ')
      (omCpt F E D W φ' hφ' _ hC) {h} isCompact_singleton
    refine ⟨K, hK, fun N => ?_⟩
    obtain ⟨B, hB⟩ := hB N
    refine ⟨B, fun s hs v => ?_⟩
    have hmem : ((h, c s) : GL (Fin 2) (A E) × G1 F) ∈ ({h} : Set _) ×ˢ (c '' Metric.closedBall t 1) :=
      ⟨rfl, s, Metric.ball_subset_closedBall hs, rfl⟩
    have := hB _ hmem v
    simpa only [hcomm, hmul, c] using this
  exact thDer F _ _ (omDer F E D W _ _ hDL hdom g) t (hdom g t)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

private theorem wt_nonneg' {F : Type} [Field F] [NumberField F]
    (K : Set (Fin 4 → FiniteAdeleRing (𝓞 F) F)) (N : ℕ) (v : V4 F) : 0 ≤ wt K N v := by
  unfold wt
  split_ifs
  · positivity
  · exact le_rfl

theorem UpperTheory.ConvolutionTheory.R2.Ff.rowMaj :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D), RowMaj W := by
  intro F E _ _ _ _ _ _ _ D W φ hφ y hy c hc
  obtain ⟨K, hK, hBK⟩ := hatMaj F E D W φ hφ y hy
  obtain ⟨N, hN⟩ := wtSum F
  obtain ⟨C, hC⟩ := hN K hK c hc
  obtain ⟨B, hB⟩ := hBK N
  refine ⟨|B| * C, fun b a k hk hca => ?_⟩
  obtain ⟨hs, hle⟩ := hC a hca
  have hab : 0 < ab a := (IdeleGroup.ideleModule F a).2
  let ι : (Fin 2 → F) → (Fin 4 → F) := fun ξ => ![0, 0, ξ 0, ξ 1]
  have hι : Function.Injective ι := by
    intro ξ ξ' h
    funext i
    fin_cases i
    · exact congrFun h 2
    · exact congrFun h 3
  have hpt : ∀ ξ : Fin 2 → F,
      (![0, ((a⁻¹ : (A F)ˣ) : A F) * 0, a * rt (ξ 0), a * rt (ξ 1)] : V4 F) = sc a (ι ξ) := by
    intro ξ
    funext i
    fin_cases i <;> simp [sc, ι]
  have hterm : ∀ ξ : Fin 2 → F,
      ‖hat (W.Om (nU b * mD a * k) (W.L (infGL E 2 y) φ)).1 ![0, 0, rt (ξ 0), rt (ξ 1)]‖ ≤
        |B| * ab a * wt K N (sc a (ι ξ)) := by
    intro ξ
    have h := hB b a k hk 0 (rt (ξ 0)) (rt (ξ 1))
    rw [hpt] at h
    refine h.trans ?_
    have hw := wt_nonneg' K N (sc a (ι ξ))
    have : B ≤ |B| := le_abs_self B
    gcongr
  have hsι : Summable fun ξ : Fin 2 → F => wt K N (sc a (ι ξ)) := hs.comp_injective hι
  have hsn : Summable fun ξ : Fin 2 → F =>
      ‖hat (W.Om (nU b * mD a * k) (W.L (infGL E 2 y) φ)).1 ![0, 0, rt (ξ 0), rt (ξ 1)]‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm (hsι.mul_left _)
  have hsum : ∑' ξ : Fin 2 → F, wt K N (sc a (ι ξ)) ≤ C :=
    (Summable.tsum_le_tsum_of_inj ι hι (fun _ _ => wt_nonneg' K N _) (fun _ => le_rfl) hsι hs).trans hle
  unfold ThRow
  calc ‖∑' ξ : Fin 2 → F, hat (W.Om (nU b * mD a * k) (W.L (infGL E 2 y) φ)).1 ![0, 0, rt (ξ 0), rt (ξ 1)]‖
      ≤ ∑' ξ : Fin 2 → F, ‖hat (W.Om (nU b * mD a * k) (W.L (infGL E 2 y) φ)).1 ![0, 0, rt (ξ 0), rt (ξ 1)]‖ :=
        norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' ξ : Fin 2 → F, |B| * ab a * wt K N (sc a (ι ξ)) :=
        Summable.tsum_le_tsum hterm hsn (hsι.mul_left _)
    _ = |B| * ab a * ∑' ξ : Fin 2 → F, wt K N (sc a (ι ξ)) := tsum_mul_left
    _ ≤ |B| * ab a * C := by gcongr
    _ = |B| * C * ab a := by ring
end
