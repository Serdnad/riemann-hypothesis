module

public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselIntegrability.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSecondOrder.SmoothClassInFiniteOrder
public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.Bundle001
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.LocalToGlobal.SiegelLatticeTheory.BesselDiscreteSeries.DecInfPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.Admissible
public import Formalism.SharpRestriction.CuspSpanNormBounds.KfinOfMemLowKSub
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle060
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.DecBoundOfCompact

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.BridgeCS3dClosed

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates Formalism.MainNotions.BridgeLemma₄


variable [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] in
theorem inputs_of (hDI : Formalism.FourierDecayAlt.ThreeDimData.DecInf) (hJ : PI.BesselMapUniq.BesselMapUniq) : Formalism.FourierDecayAlt.ThreeDimData.Inputs := by
  have hK := Formalism.L2.SG.LitS.kFinSmooth_pi Formalism.L2.SG.Pf.k_finite_smooth
  refine ⟨?_, hDI, hK, hJ⟩
  intro k r _ ε lam h H _ _ _ σ hlam hDS hgap hh P hP w₁ w₂ h₁ h₂
  have hSmooth (w : H) (hw : w ∈ PI.UpqRep.lowKSub ε lam (fun g => σ (P⁻¹ * g * P))) :
      w ∈ smoothVecs (k := k) (r := r) σ := by
    obtain ⟨V, hfd, hwV, hstable⟩ := DoubleDerivativeSmoothness.kfin_of_mem_lowKSub hw
    exact hK k r ε lam H σ hlam hDS w
      ⟨V, hfd, hwV, LowestKTypeMultiplicity.kstable_Hpk hP hstable⟩

  let a := Formalism.FourierDecayAlt.ThreeDimData.aOf r h
  let m := ⌈a⌉₊
  have hn : 1 ≤ 2 * r + k + 1 := by omega
  have hnReal : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by exact_mod_cast hn
  have hnCube : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 := one_le_pow₀ hnReal
  have hh0 : 0 ≤ h := le_trans (by positivity) hh
  have hsqrt : 1 ≤ Real.sqrt (2 * ((r : ℝ) + 1)) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    linarith [Nat.cast_nonneg (α := ℝ) r]
  have ha0 : 0 ≤ a := div_nonneg hh0 (by positivity)
  have ha8 : a ≤ h / 8 := by
    dsimp [a, Formalism.FourierDecayAlt.ThreeDimData.aOf]
    exact div_le_div_of_nonneg_left hh0 (by norm_num) (by linarith)
  have ham : a ≤ (m : ℝ) := Nat.le_ceil a
  have hm : ReciprocityTheory.ChartRestriction.DS.thrStar ε + (m : ℝ) < h := by
    have hmUpper : (m : ℝ) < a + 1 := Nat.ceil_lt_add_one ha0
    linarith [Formalism.L2.SG.BesselDiscreteSeries.thrStar_le hn ε]
  obtain ⟨C, Ws, -, hC⟩ :=
    ReciprocityTheory.ChartRestriction.DS.DecInf.decSm hlam hgap m hm hDS
  let B := C * (Ws.map fun W => ‖dsigW (k := k) (r := r) σ W w₁‖).sum *
    (Ws.map fun W => ‖dsigW (k := k) (r := r) σ W w₂‖).sum
  refine ⟨B, fun x hx => ?_⟩
  let g := Formalism.FourierDecayAlt.B.gN x
  have hg : 1 ≤ g := ((Formalism.FourierDecayAlt.P.norm_inverse_bound k r).2 x hx).2
  have hg0 : 0 < g := lt_of_lt_of_le zero_lt_one hg
  have hb : g ^ m * ‖inner ℂ w₂ (σ x w₁)‖ ≤ B :=
    hC w₁ (hSmooth w₁ h₁) w₂ (hSmooth w₂ h₂) x hx
  have hB : 0 ≤ B := le_trans (mul_nonneg (pow_nonneg hg0.le _) (norm_nonneg _)) hb
  have hpow : (g ^ m)⁻¹ ≤ g ^ (-a) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg hg0.le]
    exact Real.rpow_le_rpow_of_exponent_le hg (neg_le_neg ham)
  calc
    ‖inner ℂ w₂ (σ x w₁)‖ ≤ B * (g ^ m)⁻¹ := by
      rw [le_mul_inv_iff₀ (pow_pos hg0 _), mul_comm]
      exact hb
    _ ≤ B * g ^ (-a) := mul_le_mul_of_nonneg_left hpow hB

end Formalism.MainNotions.BridgeCS3dClosed
end
end

section

open Matrix
open scoped InnerProductSpace ContDiff

noncomputable section

namespace Formalism.L2.SG.Pf.CoefCC

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.L2.SG.Pf.CoefDecay

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem exists_exp_of_gapOK {ε : Fin (2 * r + k + 1) → Bool} {h : ℝ} (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h) {A : ℝ}
    (hA0 : 0 ≤ A) (hA : A ≤ h / 2) : ∃ m' : ℕ, ReciprocityTheory.ChartRestriction.DS.thrStar ε + m' < h ∧ A ≤ m' := by
  obtain ⟨-, h120, -, -⟩ := hok
  have hn : 1 ≤ 2 * r + k + 1 := by omega
  have ht := Formalism.L2.SG.BesselDiscreteSeries.thrStar_le hn ε
  have hn1 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by exact_mod_cast hn
  have hn3 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 := one_le_pow₀ hn1
  refine ⟨⌈A⌉₊, ?_, Nat.le_ceil A⟩
  have hc := Nat.ceil_lt_add_one hA0
  linarith

section congr

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem ev_congr {f₁ f₂ : B.Mat k r → E} (hf : ∀ y ∈ B.GV k r, f₁ y = f₂ y) :
    ∀ (ks : List Bool) (xs : List (B.Mat k r)), (∀ X ∈ xs, B.inLie k r X) →
      ∀ g ∈ B.GV k r, PI.ComplexConjugateDerivative.ev ks xs f₁ g = PI.ComplexConjugateDerivative.ev ks xs f₂ g
  | [], xs, _, g, hg => by cases xs <;> exact hf g hg
  | _ :: _, [], _, g, hg => hf g hg
  | b :: ks, X :: xs, hx, g, hg =>
    PI.ComplexConjugateDerivative.D_congr (b := b) (fun y hy => ev_congr hf ks xs (fun Y hY => hx Y (List.mem_cons_of_mem _ hY)) y hy) hg
      (hx X List.mem_cons_self)

theorem inCC_congr {A : ℝ} {m : ℕ} {f₁ f₂ : B.Mat k r → E} (hf : ∀ y ∈ B.GV k r, f₁ y = f₂ y)
    (h1 : B.InCC (k := k) (r := r) A m f₁) : B.InCC (k := k) (r := r) A m f₂ := by
  obtain ⟨c, hck, hb⟩ := h1
  refine ⟨c, fun g₀ hg₀ => ?_, fun u w hu hw hl g hg => ?_⟩
  · obtain ⟨U, f', hU, h0, hc, he⟩ := hck g₀ hg₀
    exact ⟨U, f', hU, h0, hc, fun y hy hyG => (hf y hyG).symm.trans (he y hy hyG)⟩
  · have e : B.dLR u w f₂ g = B.dLR u w f₁ g := by
      rw [PI.ComplexConjugateDerivative.dLR_eq_ev, PI.ComplexConjugateDerivative.dLR_eq_ev]
      exact (ev_congr hf _ (u ++ w) (fun X hX => by
        rcases List.mem_append.1 hX with h | h
        · exact (hu X h).1
        · exact (hw X h).1) g hg).symm
    rw [e]
    exact hb u w hu hw hl g hg

end congr

theorem coefM_translate_inCC {σ : B.Mat k r → (H →L[ℂ] H)} (hσ : Formalism.MainNotions.S.IsURepOn (B.GV k r) σ) {A : ℝ}
    (hdec : ∀ a ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) σ, ∀ b ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) σ,
      ∃ C : ℝ, ∀ g ∈ B.GV k r, B.gN g ^ A * ‖⟪a, σ g b⟫_ℂ‖ ≤ C)
    {v v' : H} (hv : v ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) σ)
    (hv' : v' ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) σ) {a b : B.Mat k r} (ha : a ∈ B.GV k r)
    (hb : b ∈ B.GV k r) (ξ : Wp) (ξ' : Wq) (m : ℕ) :
    B.InCC (k := k) (r := r) A m (fun g => Formalism.MainNotions.S.Pv.BetaCut.coefM σ v v' ξ ξ' (a * g * b)) := by
  have hai : a⁻¹ ∈ B.GV k r := Formalism.MainNotions.LowestKTypeMultiplicity.UH_inv ha
  have hdet : IsUnit a.det := Formalism.MainNotions.LowestKTypeMultiplicity.UH_det ha
  have haa : a⁻¹ * a = 1 := Matrix.nonsing_inv_mul a hdet
  refine inCC_congr (f₁ := Formalism.MainNotions.S.Pv.BetaCut.coefM σ (σ a⁻¹ v) (σ b v') ξ ξ') (fun g hg => ?_)
    (coefM_inCC_of_dec hσ hdec (Formalism.MainNotions.LowestKTypeMultiplicity.smooth_orbit hσ hv hai)
      (Formalism.MainNotions.LowestKTypeMultiplicity.smooth_orbit hσ hv' hb) ξ ξ' m)
  rw [coefM_eq, coefM_eq]
  show ⟪σ a⁻¹ v, σ g (σ b v')⟫_ℂ • rk1 ξ ξ' = ⟪v, σ (a * g * b) v'⟫_ℂ • rk1 ξ ξ'
  congr 1
  let L : H →ₗᵢ[ℂ] H := ⟨(σ a⁻¹ : H →ₗ[ℂ] H), fun x => hσ.2.1 _ hai x⟩
  have hgb : g * b ∈ B.GV k r := Formalism.MainNotions.LowestKTypeMultiplicity.UH_mul hg hb
  have e1 : σ (a * g * b) v' = σ a (σ g (σ b v')) := by
    simp only [Matrix.mul_assoc, hσ.1.2 a ha _ hgb, hσ.1.2 g hg b hb,
      ContinuousLinearMap.comp_apply]
  have e2 : σ a⁻¹ (σ a (σ g (σ b v'))) = σ g (σ b v') := by
    have := hσ.1.2 _ hai _ ha
    rw [haa, hσ.1.1] at this
    have h3 := congrArg (fun T : H →L[ℂ] H => T (σ g (σ b v'))) this
    simpa using h3.symm
  rw [e1, ← L.inner_map_map v (σ a (σ g (σ b v')))]
  show ⟪σ a⁻¹ v, σ g (σ b v')⟫_ℂ = ⟪σ a⁻¹ v, σ a⁻¹ (σ a (σ g (σ b v')))⟫_ℂ
  rw [e2]

theorem coefM_smul (σ : B.Mat k r → (H →L[ℂ] H)) (v v' : H) (ξ : Wp) (ξ' : Wq) (c : ℂ) :
    c • Formalism.MainNotions.S.Pv.BetaCut.coefM σ v v' ξ ξ' = Formalism.MainNotions.S.Pv.BetaCut.coefM σ v v' (c • ξ) ξ' := by
  funext g
  ext x
  simp only [Pi.smul_apply, Formalism.MainNotions.S.Pv.BetaCut.coefM, ContinuousLinearMap.smulRight_apply, _root_.smul_apply]
  rw [smul_comm c, smul_comm c]

theorem dec_of_DS {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    (hlam : Formalism.QuantumDeterminants.IsHCParam lam) {h : ℝ} (hgap : Formalism.QuantumDeterminants.GapAtLeast ε lam h) (m' : ℕ)
    (hm' : ReciprocityTheory.ChartRestriction.DS.thrStar ε + m' < h) {A : ℝ} (hA : A ≤ m') [CompleteSpace H]
    {σ : B.Mat k r → (H →L[ℂ] H)} (hσ : Formalism.MainNotions.S.IsDSHpk k r ε lam σ) :
    ∀ a ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) σ, ∀ b ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) σ,
      ∃ C : ℝ, ∀ g ∈ B.GV k r, B.gN g ^ A * ‖⟪a, σ g b⟫_ℂ‖ ≤ C := by
  obtain ⟨C, Ws, -, hC⟩ := ReciprocityTheory.ChartRestriction.DS.DecInf.decSm hlam hgap m' hm' hσ
  intro a ha b hb
  refine ⟨C * (Ws.map fun w => ‖Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w b‖).sum *
      (Ws.map fun w => ‖Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w a‖).sum, fun g hg => ?_⟩
  have h1 := PI.ComplexConjugateDerivative.one_le_gN hg
  calc B.gN g ^ A * ‖⟪a, σ g b⟫_ℂ‖ ≤ B.gN g ^ (m' : ℝ) * ‖⟪a, σ g b⟫_ℂ‖ :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le h1 hA) (norm_nonneg _)
    _ = B.gN g ^ m' * ‖⟪a, σ g b⟫_ℂ‖ := by rw [Real.rpow_natCast]
    _ ≤ _ := hC b hb a ha g hg

theorem smul_coefM_translate_inCC_kfin_gapOK {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    (hlam : Formalism.QuantumDeterminants.IsHCParam lam) {h : ℝ} (hgap : Formalism.QuantumDeterminants.GapAtLeast ε lam h)
    (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h) {A : ℝ} (hA0 : 0 ≤ A) (hA : A ≤ h / 2) [CompleteSpace H]
    {σ : B.Mat k r → (H →L[ℂ] H)} (hσ : PI.UpqRep.IsDSHpk k r ε lam σ) {v v' : H}
    (hv : PI.UpqRep.IsKFinHpk (k := k) (r := r) σ v) (hv' : PI.UpqRep.IsKFinHpk (k := k) (r := r) σ v')
    {a b : B.Mat k r} (ha : a ∈ B.GV k r) (hb : b ∈ B.GV k r) (c : ℂ) (ξ : Wp) (ξ' : Wq) (m : ℕ) :
    B.InCC (k := k) (r := r) A m (fun g => (c • Formalism.MainNotions.S.Pv.BetaCut.coefM σ v v' ξ ξ') (a * g * b)) := by
  obtain ⟨m', hm', hAm⟩ := exists_exp_of_gapOK (ε := ε) hok hA0 hA
  have hks := Formalism.L2.SG.LitS.kFinSmooth_pi Formalism.L2.SG.Pf.k_finite_smooth
  rw [coefM_smul]
  exact coefM_translate_inCC (Formalism.MainNotions.LowestKTypeMultiplicity.urep_of_DS hσ) (dec_of_DS hlam hgap m' hm' hAm hσ)
    (hks k r ε lam H σ (by exact hlam) hσ v hv) (hks k r ε lam H σ (by exact hlam) hσ v' hv') ha hb (c • ξ) ξ' m

end Formalism.L2.SG.Pf.CoefCC
end
end
