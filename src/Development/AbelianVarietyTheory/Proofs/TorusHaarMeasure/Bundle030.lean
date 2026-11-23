module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustFStatementPfE
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfH
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.BoundedSectionAlgebra

@[expose] public section

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem kaUnfold_of_unfold_of_kappa :
    (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ FF, IsFundSet X x0 FF → ∀ ψ : Frame X.Ψ r → ℝ≥0∞, Measurable ψ → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ψ (rmul x b) = ψ x) → ∫⁻ z, ψ (cpt X x0 z) ∂muF X x0 = ∫⁻ z in FF, ∑' γ : X.Γ, ψ (lact γ.1 (cpt X x0 z)) ∂muF X x0) → (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → PropDisc X → ∀ bb : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb → ∃ κ : Frame X.Ψ r → ℝ, Measurable κ ∧ (∀ x ∈ X.dom, 0 < κ x ∧ κ x ≤ 1) ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, κ (rmul x b) = κ x) ∧ (∀ z ∈ OmF X x0, κ (cpt X x0 z) = kaF X x0 bb z) ∧ (∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x ∈ X.dom, ∑' γ : X.Γ, ENNReal.ofReal (Real.sqrt (κ (lact γ.1 x))) ≤ C) ∧ ∃ ρ C : ℝ, 0 < ρ ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → κ (cpt X x z) ≤ C * κ x) → (KaUnfoldStatement (E := E)) := by
  intro hU hK r X x0 ho hP FF hFF bb hbb
  obtain ⟨κ, hκm, hκ1, hκB, hκka, ⟨C, hC, hsum⟩, -⟩ := hK r X x0 ho hP bb hbb
  refine ⟨C, hC, fun φ hφm hφB hφΓ => ?_⟩
  have h1 : ∫⁻ z, ENNReal.ofReal (kaF X x0 bb z) * φ (cpt X x0 z) ∂muF X x0 =
      ∫⁻ z, ENNReal.ofReal (κ (cpt X x0 z)) * φ (cpt X x0 z) ∂muF X x0 :=
    lintegral_congr_ae ((OntoH.ae_mem_Om X x0).mono fun z hz => by simp only [hκka z hz])
  have h2 := hU r X x0 ho FF hFF (fun x => ENNReal.ofReal (κ x) * φ x)
    (hκm.ennreal_ofReal.mul hφm) (fun x hx b hb => by simp only [hκB x hx b hb, hφB x hx b hb])
  rw [h1, h2, ← lintegral_const_mul' _ _ hC.ne]
  refine setLIntegral_mono' hFF.1 fun z hz => ?_
  have hx : cpt X x0 z ∈ X.dom := hFF.2.1 hz
  calc ∑' γ : X.Γ, ENNReal.ofReal (κ (lact γ.1 (cpt X x0 z))) * φ (lact γ.1 (cpt X x0 z))
      ≤ ∑' γ : X.Γ, ENNReal.ofReal (Real.sqrt (κ (lact γ.1 (cpt X x0 z)))) * φ (cpt X x0 z) := by
        refine ENNReal.tsum_le_tsum fun γ => ?_
        rw [hφΓ γ.1 γ.2 _ hx]
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
        obtain ⟨h0, h1⟩ := hκ1 _ (OntoS.dom_lact X γ.2 hx)
        rw [Real.le_sqrt h0.le h0.le]
        nlinarith
    _ = (∑' γ : X.Γ, ENNReal.ofReal (Real.sqrt (κ (lact γ.1 (cpt X x0 z))))) * φ (cpt X x0 z) :=
        ENNReal.tsum_mul_right
    _ ≤ C * φ (cpt X x0 z) := mul_le_mul' (hsum _ hx) le_rfl

end GlobalTheory
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.Up.DivCorePf

open ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

section

variable {r : ℕ} (X : Data E r)

theorem chi_ne_zero (la : Wt X.Ψ r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) : X.χ la γ ≠ 0 := by
  obtain ⟨n, hn, h⟩ := X.χ_fin la
  intro h0
  have := h γ hγ
  rw [h0, zero_pow hn.ne'] at this
  exact zero_ne_one this

theorem isSec_one : X.IsSec 0 (fun _ => (1 : ℂ)) := by
  refine ⟨differentiableOn_const _, fun x _ b _ => by simp [bchar], fun γ hγ x _ => ?_⟩
  have h := X.χ_add 0 0 γ hγ
  rw [add_zero] at h
  rw [mul_one]
  exact mul_left_cancel₀ (chi_ne_zero X 0 hγ) (by rw [mul_one]; exact h)

variable {X}

theorem isSec_mul {la la' : Wt X.Ψ r} {P Q : Frame X.Ψ r → ℂ} (hP : X.IsSec la P)
    (hQ : X.IsSec la' Q) : X.IsSec (la + la') (fun x => P x * Q x) := by
  refine ⟨hP.1.mul hQ.1, fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩
  · simp only [hP.2.1 x hx b hb, hQ.2.1 x hx b hb, bchar_add X hb]
    ring
  · simp only [hP.2.2 γ hγ x hx, hQ.2.2 γ hγ x hx, X.χ_add la la' γ hγ]
    ring

theorem isSec_pow {L : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ} (hP : X.IsSec L P) (m : ℕ) :
    X.IsSec (m • L) (fun x => P x ^ m) := by
  induction m with
  | zero => simpa using isSec_one X
  | succ m ih => simpa only [succ_nsmul, pow_succ] using isSec_mul ih hP

theorem exists_extension (hExt : ExtFStatement (E := E)) {x0 : Frame X.Ψ r} (ho : IsOrth X x0)
    {la : Wt X.Ψ r} {W : Frame X.Ψ r → ℝ≥0∞} (hWL : WLower X la W) {bb : ℝ} (hbb : 0 ≤ bb)
    {F : V (nd X) → ℂ} (hF : DifferentiableOn ℂ F (OmF X x0)) (hI : InAt X x0 W bb F) :
    ∃ P : Frame X.Ψ r → ℂ, IsBEq X la P ∧ ∀ z ∈ OmF X x0, P (cpt X x0 z) = F z := by
  obtain ⟨c, hc, hWL'⟩ := hWL
  have hka1 : ∀ z ∈ OmF X x0, kaF X x0 bb z ≤ 1 := fun z hz => by
    unfold kaF
    rw [Real.exp_le_one_iff]
    have := mul_nonneg hbb (ExF.rhF_nonneg X x0 ho hz)
    linarith
  refine hExt r X x0 ho la F hF fun Cs _ _ => ?_
  have hpt : ∀ᵐ z ∂muF X x0, ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-phla X la (cpt X x0 z))) ≤
      ENNReal.ofReal (1 / c) * (ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x0 bb z) * W (cpt X x0 z)) := by
    refine (OntoH.ae_mem_Om X x0).mono fun z hz => ?_
    have hk : 0 < kaF X x0 bb z := Real.exp_pos _
    have e : ‖F z‖ ^ 2 * Real.exp (-phla X la (cpt X x0 z)) =
        1 / c * (‖F z‖ ^ 2 * (c * Real.exp (-phla X la (cpt X x0 z)))) := by field_simp
    rw [e, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
    gcongr
    · exact le_div_self (by positivity) hk (hka1 z hz)
    · exact hWL' _ hz
  refine ((setLIntegral_le_lintegral _ _).trans (lintegral_mono_ae hpt)).trans_lt ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hI

theorem poin_sum_mul {ι : Type*} (S : Finset ι) {la la' : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ}
    {g Q : ι → Frame X.Ψ r → ℂ} (hg : ∀ i ∈ S, X.IsSec la' (g i))
    (hP : ∀ y ∈ X.dom, P y = ∑ i ∈ S, g i y * Q i y) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (hQ : ∀ i ∈ S, Summable fun γ : X.Γ => ‖(X.χ la γ.1)⁻¹ * Q i (lact γ.1 x)‖) :
    poin X (la + la') P x = ∑ i ∈ S, g i x * poin X la (Q i) x := by
  unfold poin
  have e : ∀ γ : X.Γ, (X.χ (la + la') γ.1)⁻¹ * P (lact γ.1 x) =
      ∑ i ∈ S, g i x * ((X.χ la γ.1)⁻¹ * Q i (lact γ.1 x)) := by
    intro γ
    rw [hP _ (OntoS.dom_lact X γ.2 hx), Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have h1 := chi_ne_zero X la γ.2
    have h2 := chi_ne_zero X la' γ.2
    rw [(hg i hi).2.2 γ.1 γ.2 x hx, X.χ_add la la' γ.1 γ.2]
    field_simp
  rw [tsum_congr e, Summable.tsum_finsetSum fun i hi => ((hQ i hi).of_norm).mul_left (g i x)]
  exact Finset.sum_congr rfl fun i _ => tsum_mul_left

end

end GlobalTheory.Up.DivCorePf
end
