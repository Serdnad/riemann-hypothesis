module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle004
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.EmbPiInjective
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.WtLeOfNorm
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ActRat
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle001
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle002
public import Development.AutomorphicArithmetic.UnipotentInvariants.AbLeMulOneAddNormOfFinPartMemCompact
public import Development.AutomorphicArithmetic.UnipotentInvariants.ExistsCompactSiegelDecompositionHeightLe
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InfCharConjEmbeddingNegOfInvariantPairing
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ContinuousPrN
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.DiagInvVal
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CycCOfCyclic

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

private theorem wt_nonneg' (K : Set (Fin 4 → FiniteAdeleRing (𝓞 ℚ) ℚ)) (N : ℕ) (v : V4 ℚ) : 0 ≤ wt K N v := by
  unfold wt
  split_ifs
  · positivity
  · exact le_rfl

private theorem wt_add_le (K : Set (Fin 4 → FiniteAdeleRing (𝓞 ℚ) ℚ)) (N s : ℕ) (v : V4 ℚ) :
    wt K (N + s) v ≤ wt K N v := by
  unfold wt
  split_ifs
  · have h1 : (1 : ℝ) ≤ 1 + ‖infPartPi v‖ := by linarith [norm_nonneg (infPartPi v)]
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ h1 (Nat.le_add_right N s))
  · exact le_rfl

private theorem wt_decay {K : Set (Fin 4 → FiniteAdeleRing (𝓞 ℚ) ℚ)} (N s : ℕ) {v : V4 ℚ} {T L : ℝ}
    (hT : 0 < T) (hL : 0 < L) (h : finPartPi v ∈ K → T ≤ L * (1 + ‖infPartPi v‖)) :
    wt K (N + s) v ≤ (L * T⁻¹) ^ s * wt K N v := by
  unfold wt
  by_cases hv : finPartPi v ∈ K
  · rw [if_pos hv, if_pos hv]
    have hp : 0 < 1 + ‖infPartPi v‖ := by linarith [norm_nonneg (infPartPi v)]
    have h1 : (1 + ‖infPartPi v‖)⁻¹ ≤ L * T⁻¹ := by
      rw [inv_le_iff_one_le_mul₀ hp]
      have := h hv
      calc (1 : ℝ) = T * T⁻¹ := (mul_inv_cancel₀ hT.ne').symm
        _ ≤ (L * (1 + ‖infPartPi v‖)) * T⁻¹ := by gcongr
        _ = L * T⁻¹ * (1 + ‖infPartPi v‖) := by ring
    rw [pow_add, mul_inv, mul_comm, ← inv_pow (1 + ‖infPartPi v‖) s]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) h1 s) (by positivity)
  · rw [if_neg hv, if_neg hv, mul_zero]

private theorem rt_injective : Function.Injective (rt : ℚ → A ℚ) := by
  haveI : Nontrivial (A ℚ) := ⟨⟨0, 1, fun h => by
    have e : ((0 : A ℚ).1 Rat.infinitePlace) = ((1 : A ℚ).1 Rat.infinitePlace) :=
      congrArg (fun x : A ℚ => x.1 Rat.infinitePlace) h
    exact zero_ne_one e⟩⟩
  exact (algebraMap ℚ (A ℚ)).injective

private theorem rp_injective : Function.Injective (rp : (Fin 4 → ℚ) → V4 ℚ) := fun _ _ h =>
  funext fun i => rt_injective (congrFun h i)

section Act

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {D : Dat ℚ E}
  {ρ : GL (Fin 2) (A E) →* GL (Fin 4) (A ℚ)}

private theorem act_mul (hact : ∀ h v, D.act h v = (ρ h).val *ᵥ v) (h h' : GL (Fin 2) (A E)) (v : V4 ℚ) :
    D.act (h * h') v = D.act h (D.act h' v) := by
  rw [hact, hact, hact, map_mul, Units.val_mul, Matrix.mulVec_mulVec]

private theorem act_one (hact : ∀ h v, D.act h v = (ρ h).val *ᵥ v) (v : V4 ℚ) : D.act 1 v = v := by
  rw [hact, map_one, Units.val_one, Matrix.one_mulVec]

private theorem act_scale (hact : ∀ h v, D.act h v = (ρ h).val *ᵥ v) (h : GL (Fin 2) (A E)) (x : A ℚ) (v : V4 ℚ) :
    D.act h (fun i => x * v i) = fun i => x * D.act h v i := by
  have e : (fun i => x * v i) = x • v := rfl
  rw [e, hact, hact, Matrix.mulVec_smul]
  rfl

private theorem rat_equiv (hact : ∀ h v, D.act h v = (ρ h).val *ᵥ v) (γ : Matrix.SpecialLinearGroup (Fin 2) E) :
    ∃ e : (Fin 4 → ℚ) ≃ (Fin 4 → ℚ), (∀ ξ, D.act (gl (ratS E γ))⁻¹ (rp ξ) = rp (e ξ)) ∧
      ∀ ξ, qr D.δ (e ξ) = qr D.δ ξ := by
  have h : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) E) (ξ : Fin 4 → ℚ), ∃ ξ', D.act (gl (ratS E γ)) (rp ξ) = rp ξ' := by
    intro γ ξ
    obtain ⟨N, -, hN⟩ := actRat ℚ E D (Matrix.SpecialLinearGroup.toGL γ)
    exact ⟨_, by rw [gl_ratS]; exact hN ξ⟩
  choose f hf using h
  have hinv : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) E, (gl (ratS E γ))⁻¹ = gl (ratS E γ⁻¹) := fun γ => by
    rw [map_inv, gl_inv]
  have hcomp : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) E) ξ, f γ (f γ⁻¹ ξ) = ξ := fun γ ξ => rp_injective (by
    rw [← hf, ← hf, ← act_mul hact, ← gl_mul, ← map_mul, mul_inv_cancel, map_one, gl_one, act_one hact])
  have hcomp' : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) E) ξ, f γ⁻¹ (f γ ξ) = ξ := fun γ ξ => by
    simpa using hcomp γ⁻¹ ξ
  obtain ⟨-, -, -, hnu, -, -, -, -, -, hqi, hqr⟩ := szLaws E D
  refine ⟨⟨f γ⁻¹, f γ, hcomp γ, hcomp' γ⟩, fun ξ => ?_, fun ξ => rt_injective ?_⟩
  · rw [hinv]
    exact hf _ ξ
  · change rt (qr D.δ (f γ⁻¹ ξ)) = _
    rw [← hqr, ← hf, hqi _ (hnu _), hqr]

private theorem term_le (hact : ∀ h v, D.act h v = (ρ h).val *ᵥ v) {K K' : Set (Fin 4 → FiniteAdeleRing (𝓞 ℚ) ℚ)} {n : ℕ}
    {B₁ Tz : ℝ} {x y : GL (Fin 2) (A E)} {g₀ : GL (Fin 2) (A E)} {z : GL (Fin 2) (Cinf E)} {e : (Fin 4 → ℚ) → Fin 4 → ℚ}
    (hx : x = g₀ * infGL E 2 z * y) (hlin : ∀ v, wt K n ((ρ y⁻¹).val *ᵥ v) ≤ B₁ * wt K' n v)
    (hz : ∀ v, wt K' n (D.act (infGL E 2 z)⁻¹ v) ≤ Tz * wt K' n v)
    (he : ∀ ξ, D.act g₀⁻¹ (rp ξ) = rp (e ξ)) (a : (A ℚ)ˣ) (ξ : Fin 4 → ℚ) :
    (wt K n fun i => (a : A ℚ) * D.act x⁻¹ (rp ξ) i) ≤ |B₁| * (Tz * wt K' n (sc a (e ξ))) := by
  have hxi : x⁻¹ = y⁻¹ * ((infGL E 2 z)⁻¹ * g₀⁻¹) := by
    rw [hx]
    group
  have h1 : (fun i => (a : A ℚ) * D.act x⁻¹ (rp ξ) i) =
      (ρ y⁻¹).val *ᵥ D.act (infGL E 2 z)⁻¹ (sc a (e ξ)) := by
    rw [← hact, hxi, act_mul hact, act_mul hact, he]
    have e1 : sc a (e ξ) = fun i => (a : A ℚ) * rp (e ξ) i := rfl
    rw [e1, act_scale hact, act_scale hact]
  rw [h1]
  have hw1 := wt_nonneg' K' n (D.act (infGL E 2 z)⁻¹ (sc a (e ξ)))
  exact (hlin _).trans ((mul_le_mul_of_nonneg_right (le_abs_self _) hw1).trans
    (mul_le_mul_of_nonneg_left (hz _) (abs_nonneg _)))

end Act

private theorem pow_bound {C₀ C₂ H t : ℝ} (n : ℕ) (hH : 0 ≤ H) (ht : 0 < t) (h : H ≤ C₂ * t) :
    (C₀ * H ^ 2) ^ n ≤ (|C₀| * |C₂| ^ 2) ^ n * t ^ (2 * n) := by
  have e1 : H ≤ |C₂| * t := h.trans (mul_le_mul_of_nonneg_right (le_abs_self _) ht.le)
  calc (C₀ * H ^ 2) ^ n ≤ (|C₀| * H ^ 2) ^ n := by
        refine le_trans (le_abs_self _) ?_
        rw [abs_pow, abs_mul, abs_of_nonneg (pow_nonneg hH 2)]
    _ ≤ (|C₀| * (|C₂| * t) ^ 2) ^ n := by gcongr
    _ = (|C₀| * |C₂| ^ 2) ^ n * t ^ (2 * n) := by
        rw [mul_pow |C₂|, ← mul_assoc, mul_pow, pow_mul]

private theorem sum_cmp {ι : Type} {f g : ι → ℝ} {P : ι → Prop} {M M' S : ℝ} (hM : 0 ≤ M) (hM' : 0 ≤ M')
    (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i) (hs : Summable g) (hS : ∑' i, g i ≤ S) (h : ∀ i, f i ≤ M * g i)
    (h' : ∀ i, P i → f i ≤ M' * g i) :
    Summable f ∧ ∑' i, f i ≤ M * S ∧ ∑' i : {i // P i}, f i.1 ≤ M' * S := by
  have hfs : Summable f := Summable.of_nonneg_of_le hf h (hs.mul_left M)
  refine ⟨hfs, ?_, ?_⟩
  · calc ∑' i, f i ≤ ∑' i, M * g i := hfs.tsum_le_tsum h (hs.mul_left M)
      _ = M * ∑' i, g i := tsum_mul_left
      _ ≤ M * S := mul_le_mul_of_nonneg_left hS hM
  · have hq : Summable fun i : {i // P i} => M' * g i.1 := (hs.mul_left M').comp_injective Subtype.val_injective
    calc ∑' i : {i // P i}, f i.1 ≤ ∑' i : {i // P i}, M' * g i.1 :=
          (hfs.comp_injective Subtype.val_injective).tsum_le_tsum (fun i => h' i.1 i.2) hq
      _ ≤ ∑' i, M' * g i := Summable.tsum_subtype_le (fun i => M' * g i) {i | P i} (fun i => mul_nonneg hM' (hg i)) (hs.mul_left M')
      _ = M' * ∑' i, g i := tsum_mul_left
      _ ≤ M' * S := mul_le_mul_of_nonneg_left hS hM'

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.latSum :
    LatSum := by
  intro E _ _ _ D K C c s hK hC _ hc
  obtain ⟨ρ, hρ, hact, -⟩ := actCont ℚ E D
  obtain ⟨N, hN⟩ := wtSum ℚ
  obtain ⟨Y, C₂, hY, hred⟩ := UpperTheory.exists_compact_siegel_decomposition_height_le E c hc
  have hCmp : IsCompact ((fun p : G1 E × GL (Fin 2) (A E) => ρ (gl p.1 * p.2)⁻¹) '' (Y ×ˢ C)) :=
    (hY.prod hC).image (hρ.comp (((continuous_gl.comp continuous_fst).mul continuous_snd).inv))
  obtain ⟨K', hK', hlin⟩ := wtLin ℚ _ hCmp K hK
  obtain ⟨B₁, hB₁⟩ := hlin (N + s)
  obtain ⟨C₀, hC₀⟩ := wtAct ℚ E D
  obtain ⟨Cs, hCs⟩ := hN K' hK' c hc
  obtain ⟨L, hL, hq⟩ := UpperTheory.ab_le_mul_one_add_norm_of_finPart_mem_compact K' D.δ hK'
  refine ⟨N + s, 2 * (N + s), |B₁| * (|C₀| * |C₂| ^ 2) ^ (N + s) * |Cs| * (1 + L ^ s), fun a u b k hk ha hb => ?_⟩
  obtain ⟨γ, z, w, hw, hx, hHt⟩ := hred u b hb
  obtain ⟨e, he, heq⟩ := rat_equiv hact γ
  obtain ⟨hs, ht⟩ := hCs a ha
  have haa : 0 < ab a := ab_pos a
  have hbb : 0 < ab b := ab_pos b
  have hHt0 : 0 ≤ Ht z := by unfold Ht; positivity
  have hmem : ρ (gl w * k)⁻¹ ∈ (fun p : G1 E × GL (Fin 2) (A E) => ρ (gl p.1 * p.2)⁻¹) '' (Y ×ˢ C) :=
    ⟨(w, k), ⟨hw, hk⟩, rfl⟩
  have hterm := term_le (K := K) (K' := K') (n := N + s) (y := gl w * k) hact
    (x := gl (nU u * mD b) * k) (by rw [hx, mul_assoc]) (hB₁ _ hmem) (hC₀ K' (N + s) z) he a
  set T : ℝ := |B₁| * (|C₀| * |C₂| ^ 2) ^ (N + s) * ab b ^ (2 * (N + s)) with hT
  have hT0 : 0 ≤ T := by positivity
  have hle : ∀ ξ, (wt K (N + s) fun i => (a : A ℚ) * D.act (gl (nU u * mD b) * k)⁻¹ (rp ξ) i) ≤
      T * wt K' (N + s) (sc a (e ξ)) := fun ξ => by
    have hw0 := wt_nonneg' K' (N + s) (sc a (e ξ))
    refine (hterm ξ).trans ?_
    rw [hT, mul_assoc |B₁|, mul_assoc |B₁|]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (pow_bound _ hHt0 hbb hHt) hw0) (abs_nonneg _)
  have hgt : ∑' ξ, wt K' N (sc a (e ξ)) ≤ |Cs| := by
    rw [e.tsum_eq fun ξ => wt K' N (sc a ξ)]
    exact ht.trans (le_abs_self _)
  have hM' : 0 ≤ T * (L * (ab a)⁻¹) ^ s := by positivity
  obtain ⟨h1, h2, h3⟩ := sum_cmp (P := fun ξ => qr D.δ ξ ≠ 0) hT0 hM' (fun _ => wt_nonneg' _ _ _)
    (fun _ => wt_nonneg' _ _ _) (hs.comp_injective e.injective) hgt
    (fun ξ => (hle ξ).trans (mul_le_mul_of_nonneg_left (wt_add_le K' N s _) hT0))
    (fun ξ hξ => by
      have hne : qr D.δ (e ξ) ≠ 0 := by rw [heq]; exact hξ
      have h1 := wt_decay (K := K') N s (v := sc a (e ξ)) haa hL (hq a _ hne)
      calc _ ≤ T * wt K' (N + s) (sc a (e ξ)) := hle ξ
        _ ≤ T * ((L * (ab a)⁻¹) ^ s * wt K' N (sc a (e ξ))) := mul_le_mul_of_nonneg_left h1 hT0
        _ = _ := (mul_assoc _ _ _).symm)
  have hCs0 : 0 ≤ |Cs| := abs_nonneg _
  have hLs : 0 ≤ L ^ s := by positivity
  refine ⟨h1, h2.trans ?_, h3.trans ?_⟩
  · have hQ : 0 ≤ |B₁| * (|C₀| * |C₂| ^ 2) ^ (N + s) * |Cs| * ab b ^ (2 * (N + s)) := by positivity
    calc T * |Cs| = |B₁| * (|C₀| * |C₂| ^ 2) ^ (N + s) * |Cs| * ab b ^ (2 * (N + s)) * 1 := by rw [hT]; ring
      _ ≤ |B₁| * (|C₀| * |C₂| ^ 2) ^ (N + s) * |Cs| * ab b ^ (2 * (N + s)) * (1 + L ^ s) :=
          mul_le_mul_of_nonneg_left (by linarith) hQ
      _ = _ := by ring
  · have hQ : 0 ≤ |B₁| * (|C₀| * |C₂| ^ 2) ^ (N + s) * |Cs| * (ab a)⁻¹ ^ s * ab b ^ (2 * (N + s)) := by positivity
    calc T * (L * (ab a)⁻¹) ^ s * |Cs| =
          |B₁| * (|C₀| * |C₂| ^ 2) ^ (N + s) * |Cs| * (ab a)⁻¹ ^ s * ab b ^ (2 * (N + s)) * L ^ s := by
            rw [hT, mul_pow]; ring
      _ ≤ |B₁| * (|C₀| * |C₂| ^ 2) ^ (N + s) * |Cs| * (ab a)⁻¹ ^ s * ab b ^ (2 * (N + s)) * (1 + L ^ s) :=
          mul_le_mul_of_nonneg_left (by linarith) hQ
      _ = _ := by ring
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.V.Z.Bc
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.RankTwoDescent

private theorem neg_of_prod_eq {m m' : Multiset ℂ} (hc : m.card = 2) (hc' : m'.card = 2)
    (h : ∀ u : ℂ, (m.map (u + ·)).prod = (m'.map (-u + ·)).prod) : m' = m.map Neg.neg := by
  obtain ⟨a, b, rfl⟩ := Multiset.card_eq_two.1 hc
  obtain ⟨c, d, rfl⟩ := Multiset.card_eq_two.1 hc'
  have key : ∀ u : ℂ, (u + a) * (u + b) = (-u + c) * (-u + d) := fun u => by
    simpa [Multiset.insert_eq_cons] using h u
  have h0 := key 0
  have h1 := key 1
  have hs : a + b = -(c + d) := by linear_combination h1 - h0
  have hz : (c + a) * (c + b) = 0 := by
    have := key c
    simpa using this
  rcases mul_eq_zero.1 hz with e | e
  · have e1 : c = -a := by linear_combination e
    have e2 : d = -b := by linear_combination hs - e
    simp [e1, e2, Multiset.insert_eq_cons]
  · have e1 : c = -b := by linear_combination e
    have e2 : d = -a := by linear_combination hs - e
    simp only [e1, e2, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton]
    exact Multiset.cons_swap _ _ _

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.infPair :
    InfPair := by
  intro E _ _ _ V Q B hB hne τ m m' hc hm hm'
  obtain ⟨x, y, hxy⟩ : ∃ x y, B x y ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hne (LinearMap.ext fun x => LinearMap.ext fun y => hcon x y)
  let S := GlobalTheory.CapPair.adjPairs V Q.V B
  have h1 : ∀ i j z, (GlobalTheory.CuspRep.lieS E 2 i j (GlobalTheory.CuspRep.atEmb τ z),
      -MulOpposite.op (GlobalTheory.CuspRep.lieS E 2 i j (GlobalTheory.CuspRep.atEmb τ z))) ∈ S := by
    intro i j z φ ψ
    have h := hB.lie (toL (Matrix.single i j (GlobalTheory.CuspRep.atEmb τ z))) φ ψ
    rw [add_eq_zero_iff_eq_neg, ← map_neg] at h
    exact ⟨hB.st (.lie _) _ φ.2, neg_mem (hB.st' (.lie _) _ ψ.2), h⟩
  have h2 : ∀ i j, (GlobalTheory.CuspRep.Eop (a := 2) τ i j, -MulOpposite.op (GlobalTheory.CuspRep.Eop (a := 2) τ i j)) ∈ S := fun i j => by
    convert S.smul_mem (S.sub_mem (h1 i j 1) (S.smul_mem (h1 i j Complex.I) Complex.I)) (1 / 2) using 1
    refine Prod.ext rfl ?_
    simp only [GlobalTheory.CuspRep.Eop, MulOpposite.op_smul, MulOpposite.op_sub, Prod.smul_snd, Prod.snd_sub]
    module
  have h3 : ∀ w, Formalism.REAL.qdet (fun i j => (GlobalTheory.CuspRep.Eop (a := 2) τ i j, -MulOpposite.op (GlobalTheory.CuspRep.Eop (a := 2) τ i j))) w ∈ S := fun w => by
    refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
    refine S.add_mem ?_ (h2 _ _)
    split_ifs
    · exact S.algebraMap_mem _
    · exact S.zero_mem
  have h4 : ∀ u, (GlobalTheory.CuspRep.cap (a := 2) τ u, MulOpposite.op ((-1 : ℂ) ^ 2 • GlobalTheory.CuspRep.cap (a := 2) τ (-u) : Module.End ℂ (Sm E 2))) ∈ S := fun u => by
    convert h3 (u + (((2 : ℕ) : ℂ) - 1) / 2) using 1
    rw [GlobalTheory.CapPair.qdet_prod, GlobalTheory.CapPair.qdet_antipode (A := Module.End ℂ (Sm E 2)) (GlobalTheory.CuspRep.glRel_Eop (a := 2) τ),
      show ((2 : ℕ) : ℂ) - 1 - (u + (((2 : ℕ) : ℂ) - 1) / 2) = -u + (((2 : ℕ) : ℂ) - 1) / 2 by ring]
    rfl
  refine neg_of_prod_eq hc hm'.1 fun u => ?_
  obtain ⟨h, h', e'⟩ := h4 u x y
  have e1 : (⟨_, h⟩ : V) = (m.map (u + ·)).prod • x := Subtype.ext (hm u _ x.2)
  have e3 : (⟨_, h'⟩ : Q.V) = (m'.map (-u + ·)).prod • y := Subtype.ext (by
    change (-1 : ℂ) ^ 2 • GlobalTheory.CuspRep.cap (a := 2) τ (-u) y.1 = _ • y.1
    rw [hm'.2 _ _ y.2]
    simp)
  have e4 : B ((m.map (u + ·)).prod • x) y = B x ((m'.map (-u + ·)).prod • y) := by
    rw [← e1, ← e3]
    exact e'
  rw [map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul] at e4
  exact mul_right_cancel₀ hxy e4
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.V.Z.Bc
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.RankTwoDescent

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.meanLaws :
    MeanLaws := by
  intro E _ _ N Ψ hΨ
  have hgl : Continuous (gl : G1 E → GL (Fin 2) (A E)) := by fun_prop
  haveI : IsFiniteMeasure (N.μ.restrict N.D) := ⟨by simpa using volE E N⟩
  have hc : ∀ y, Continuous fun h : G1 E => Ψ (gl h * y) := fun y =>
    hΨ.cont.comp (hgl.mul continuous_const)
  have hL : ∀ y, UpperTheory.ConvolutionTheory.R2.Ff.LRat fun x => Ψ (x * y) := fun y γ g => by
    simpa only [mul_assoc] using hΨ.left γ (g * y)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨B, hB⟩ := hΨ.bdd {y} isCompact_singleton
    exact Integrable.of_bound (hc y).aestronglyMeasurable B
      (Eventually.of_forall fun h => hB h y rfl)
  · rw [continuous_iff_continuousAt]
    intro y
    obtain ⟨C, hCc, hCn⟩ := exists_compact_mem_nhds y
    obtain ⟨B, hB⟩ := hΨ.bdd C hCc

    refine continuousAt_of_dominated (bound := fun _ => B) ?_ ?_ (integrable_const B) ?_
    · exact Eventually.of_forall fun z => (hc z).aestronglyMeasurable
    · filter_upwards [hCn] with z hz
      exact Eventually.of_forall fun h => hB h z hz
    · exact Eventually.of_forall fun h =>
        (hΨ.cont.comp (continuous_const.mul continuous_id)).continuousAt
  · intro h y
    simpa only [mul_assoc] using ((invE E N).2 _ (hL y)).1 h
  · intro γ y
    simpa only [mul_assoc] using ((invE E N).2 _ (hL y)).2 γ
end
