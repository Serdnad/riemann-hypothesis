module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle050
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle051
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle013
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LastBlockDecay
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormOfMemRootSetOne
public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSettingBis
public import Formalism.HermitianCurvature.StatementNF
public import Formalism.HermitianCurvature.Bundle008
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Lemma
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
public import Mathlib.Algebra.Order.Chebyshev
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MeasureTheory
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSH.SFG

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def pt {k ρ m : ℕ} (e : ρ + 1 = m) (t : ℂ) (γ : B.Mat k ρ) (xx : U.RC k 1 ρ × U.RC k 1 ρ) : B.Mat k m :=
  (rn1 e xx.1)⁻¹ * mc e t γ * rn1 e xx.2

def GfStep : Prop :=
  ∀ (k ρ m : ℕ) (e : ρ + 1 = m) (z z' : Fin (2 * ρ + k + 1) → ℂ), inWb k ρ z → inWb k ρ z' →
    ∀ (t : ℂ), t ≠ 0 → ∀ (γ : B.Mat k ρ)
    (xx : U.RC k 1 ρ × U.RC k 1 ρ),
    Gf k m (D.castV e (D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ z)))
        (D.castV e (D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ z'))) (pt e t γ xx) =
      ‖t‖ ^ 2 * Gf k ρ z z' γ

def RadProper : Prop :=
  ∀ (k ρ m : ℕ) (e : ρ + 1 = m) (δ R : ℝ), 0 < δ →
    ∃ (Kx : Set (U.RC k 1 ρ × U.RC k 1 ρ)) (C : Set (B.Mat k ρ)), IsCompact Kx ∧ IsCompact C ∧
      ∀ (t : ℂ) (γ : B.Mat k ρ) (xx : U.RC k 1 ρ × U.RC k 1 ρ), δ ≤ ‖t‖ → B.gN (pt e t γ xx) ≤ R →
        xx ∈ Kx ∧ γ ∈ C

def ParamSmooth : Prop :=
  ∀ (Pm X W : Type) [NormedAddCommGroup Pm] [NormedSpace ℝ Pm] [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (h : Pm → X → W) (s : Set Pm) (K : Set X),
    IsOpen s → IsCompact K → (∀ p ∈ s, ∀ x, x ∉ K → h p x = 0) →
    ContDiffOn ℝ ∞ (fun q : Pm × X => h q.1 q.2) (s ×ˢ Set.univ) →
    ContDiffOn ℝ ∞ (fun p => ∫ x, h p x ∂μ) s

def PtSmooth : Prop :=
  ∀ (k ρ m : ℕ) (e : ρ + 1 = m),
    ContDiffOn ℝ ∞ (fun q : (ℂ × B.Mat k ρ) × (U.RC k 1 ρ × U.RC k 1 ρ) => pt e q.1.1 q.1.2 q.2)
      ({p : ℂ × B.Mat k ρ | p.1 ≠ 0} ×ˢ Set.univ) ∧
    ∀ z : Fin (2 * m + k + 1) → ℂ, ContDiff ℝ ∞ (fun x : U.RC k 1 ρ => psi k m z cStd (rn1 e x))

def PtGV : Prop :=
  ∀ (k ρ m : ℕ) (e : ρ + 1 = m) (t : ℂ), t ≠ 0 → ∀ γ ∈ B.GV k ρ, ∀ xx : U.RC k 1 ρ × U.RC k 1 ρ,
    pt e t γ xx ∈ B.GV k m

def CkExt : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (F : B.Mat k r → E),
    B.CkOn (⊤ : ℕ∞) (B.GV k r) F → HasCompactSupport F →
    ∃ Ft : B.Mat k r → E, ContDiff ℝ ∞ Ft ∧ HasCompactSupport Ft ∧ ∀ g ∈ B.GV k r, Ft g = F g

end Formalism.FourierDecayAlt.P.CutSH.SFG
end
end

section

namespace Formalism.FourierDecayAlt.P.PBK

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

section abar

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def abar (s : ℕ) (ε : ℂ) (bt : ℂ → H) (D : ℂ) : ℝ := ∑ z ∈ G.rootSet s (ε * D), ‖bt z‖

theorem abar_nonneg (s : ℕ) (ε : ℂ) (bt : ℂ → H) (D : ℂ) : 0 ≤ abar s ε bt D := Finset.sum_nonneg fun _ _ => norm_nonneg _

private lemma norm_psi_lemma (β w : ℂ) : ‖G.psi β w‖ = 1 := by
  simp [G.psi, Complex.norm_exp]

theorem norm_mainD_le (s : ℕ) (β ε : ℂ) (bt : ℂ → H) (x D : ℂ) :
    ‖mainD s β ε bt x D‖ ≤ abar s ε bt D := by
  unfold mainD abar
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun z _ => ?_)
  rw [norm_smul, norm_psi_lemma, one_mul]

theorem mainD_ae_eq {s : ℕ} (hs : s ≠ 0) (β : ℂ) {ε : ℂ} (hε : ε ≠ 0) (bt : ℂ → H) (x : ℂ) :
    mainD s β ε bt x =ᵐ[volume] fun D => ∑ k ∈ Finset.range s,
      G.psi β ((s : ℂ) * NthRootMeasurability.R s k (ε * D) * x) • bt (NthRootMeasurability.R s k (ε * D)) := by
  have h0 : ∀ᵐ D : ℂ ∂volume, D ≠ 0 := by
    rw [ae_iff]; simp
  filter_upwards [h0] with D hD
  unfold mainD
  rw [sum_rootSet_eq_range hs (mul_ne_zero hε hD)]

theorem abar_ae_eq {s : ℕ} (hs : s ≠ 0) {ε : ℂ} (hε : ε ≠ 0) (bt : ℂ → H) :
    abar s ε bt =ᵐ[volume] fun D => ∑ k ∈ Finset.range s, ‖bt (NthRootMeasurability.R s k (ε * D))‖ := by
  have h0 : ∀ᵐ D : ℂ ∂volume, D ≠ 0 := by
    rw [ae_iff]; simp
  filter_upwards [h0] with D hD
  unfold abar
  rw [sum_rootSet_eq_range hs (mul_ne_zero hε hD)]

private lemma measurable_R_lemma (s k : ℕ) : Measurable (NthRootMeasurability.R s k) := by
  unfold NthRootMeasurability.R
  exact measurable_const.mul (measurable_id.pow_const _)

private lemma continuous_psi_lemma_2 (β : ℂ) : Continuous (G.psi β) := by
  unfold G.psi
  fun_prop

theorem aestronglyMeasurable_mainD {s : ℕ} (hs : s ≠ 0) (β : ℂ) {ε : ℂ} (hε : ε ≠ 0) {bt : ℂ → H}
    (hbt : StronglyMeasurable bt) (x : ℂ) : AEStronglyMeasurable (mainD s β ε bt x) volume := by
  refine AEStronglyMeasurable.congr (StronglyMeasurable.aestronglyMeasurable ?_)
    (mainD_ae_eq hs β hε bt x).symm
  have hk : ∀ k ∈ Finset.range s, StronglyMeasurable (fun D : ℂ =>
      G.psi β ((s : ℂ) * NthRootMeasurability.R s k (ε * D) * x) • bt (NthRootMeasurability.R s k (ε * D))) := by
    intro k _
    have hR : Measurable fun D : ℂ => NthRootMeasurability.R s k (ε * D) :=
      (measurable_R_lemma s k).comp (measurable_const.mul measurable_id)
    have hp : Measurable fun D : ℂ => G.psi β ((s : ℂ) * NthRootMeasurability.R s k (ε * D) * x) :=
      (continuous_psi_lemma_2 β).measurable.comp ((measurable_const.mul hR).mul measurable_const)
    exact hp.stronglyMeasurable.smul (hbt.comp_measurable hR)
  have := Finset.stronglyMeasurable_sum (Finset.range s) hk
  convert this using 1 <;> ext D <;> simp

theorem aestronglyMeasurable_abar {s : ℕ} (hs : s ≠ 0) {ε : ℂ} (hε : ε ≠ 0) {bt : ℂ → H}
    (hbt : StronglyMeasurable bt) : AEStronglyMeasurable (abar s ε bt) volume := by
  refine AEStronglyMeasurable.congr (StronglyMeasurable.aestronglyMeasurable ?_)
    (abar_ae_eq hs hε bt).symm
  have hk : ∀ k ∈ Finset.range s, StronglyMeasurable (fun D : ℂ => ‖bt (NthRootMeasurability.R s k (ε * D))‖) := by
    intro k _
    have hR : Measurable fun D : ℂ => NthRootMeasurability.R s k (ε * D) :=
      (measurable_R_lemma s k).comp (measurable_const.mul measurable_id)
    exact (hbt.comp_measurable hR).norm
  have := Finset.stronglyMeasurable_sum (Finset.range s) hk
  convert this using 1 <;> ext D <;> simp

theorem card_rootSet_le (s : ℕ) (a : ℂ) : (G.rootSet s a).card ≤ s := by
  unfold G.rootSet
  exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots s a)

theorem jac_norm_bz {s : ℕ} {ε : ℂ} (hε : ‖ε‖ = 1) (bt : ℂ → H) (z : ℂ) :
    ‖ε⁻¹ * ((s : ℂ) * z ^ (s - 1))‖ ^ 2 • ‖bt z‖ ^ 2 = ‖bz s bt z‖ ^ 2 := by
  simp only [bz, norm_smul, norm_mul, norm_inv, hε, inv_one, one_mul, norm_pow,
    Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs, smul_eq_mul, abs_norm]
  rw [abs_of_nonneg (by positivity)]
  ring

theorem memLp_abar {s : ℕ} (hs : s ≠ 0) {ε : ℂ} (hε : ‖ε‖ = 1) {bt : ℂ → H} (hbt : StronglyMeasurable bt)
    (hb : MemLp (bz s bt) 2 volume) :
    MemLp (abar s ε bt) 2 volume ∧ ∫ D, abar s ε bt D ^ 2 ≤ s * ∫ z, ‖bz s bt z‖ ^ 2 := by
  have hε0 : ε ≠ 0 := by rintro rfl; simp at hε
  have hb2 : Integrable (fun z => ‖bz s bt z‖ ^ 2) := (memLp_two_iff_integrable_sq_norm hb.aestronglyMeasurable).1 hb
  have hF : Integrable (fun z => ‖ε⁻¹ * ((s : ℂ) * z ^ (s - 1))‖ ^ 2 • ‖bt z‖ ^ 2) := by
    simp_rw [jac_norm_bz hε bt]; exact hb2
  obtain ⟨hGi, hGeq⟩ := integral_sum_rootSet s hs ε hε0 (fun z => ‖bt z‖ ^ 2) hF
  have hpt : ∀ D, abar s ε bt D ^ 2 ≤ s * ∑ z ∈ G.rootSet s (ε * D), ‖bt z‖ ^ 2 := by
    intro D
    refine (sq_sum_le_card_mul_sum_sq).trans ?_
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_rootSet_le s _)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hm := aestronglyMeasurable_abar hs hε0 hbt
  have hsq : Integrable (fun D => abar s ε bt D ^ 2) := by
    refine Integrable.mono' (hGi.const_mul s) (hm.pow 2) (Eventually.of_forall fun D => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpt D
  refine ⟨(memLp_two_iff_integrable_sq hm).2 hsq, ?_⟩
  calc ∫ D, abar s ε bt D ^ 2 ≤ ∫ D, (s : ℝ) * ∑ z ∈ G.rootSet s (ε * D), ‖bt z‖ ^ 2 :=
        integral_mono hsq (hGi.const_mul s) hpt
    _ = s * ∫ z, ‖bz s bt z‖ ^ 2 := by
        rw [integral_const_mul, hGeq]
        simp_rw [jac_norm_bz hε bt]

theorem memLp_mainD {s : ℕ} (hs : s ≠ 0) (β : ℂ) {ε : ℂ} (hε : ‖ε‖ = 1) {bt : ℂ → H}
    (hbt : StronglyMeasurable bt) (hb : MemLp (bz s bt) 2 volume) (x : ℂ) :
    MemLp (mainD s β ε bt x) 2 volume := by
  have hε0 : ε ≠ 0 := by
    intro h; rw [h, norm_zero] at hε; exact zero_ne_one hε
  refine (memLp_abar hs hε hbt hb).1.of_le (aestronglyMeasurable_mainD hs β hε0 hbt x)
    (ae_of_all _ fun D => ?_)
  rw [Real.norm_of_nonneg (abar_nonneg s ε bt D)]
  exact norm_mainD_le s β ε bt x D

end abar

section moving

theorem dil_dominator {α : Type} {l : Filter α} (ab : ℂ → ℝ) (hab : MemLp ab 2 volume) (lam : α → ℂ)
    (hlam : Tendsto lam l (𝓝 1)) :
    (∀ a D, ‖lam a‖ * ab (lam a * D) ≤ ab D + |‖lam a‖ * ab (lam a * D) - ab D|) ∧
    (∀ᶠ a in l, MemLp (fun D => |‖lam a‖ * ab (lam a * D) - ab D|) 2 volume) ∧
    Tendsto (fun a => ∫ D, |‖lam a‖ * ab (lam a * D) - ab D| ^ 2) l (𝓝 0) := by
  refine ⟨fun a D => by linarith [le_abs_self (‖lam a‖ * ab (lam a * D) - ab D)], ?_, ?_⟩
  · filter_upwards [hlam.eventually_ne one_ne_zero] with a ha
    exact (((memLp_comp_mul hab (lam a) ha).const_mul ‖lam a‖).sub hab).abs
  · have h := (tendsto_dil_real ab hab).comp hlam
    refine h.congr fun a => ?_
    simp only [Function.comp_apply, sq_abs]

end moving

section cut

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem mainD_indicator {s : ℕ} (hs : s ≠ 0) (β : ℂ) {ε : ℂ} (hε : ε ≠ 0) (bt : ℂ → H) (Q : Set ℂ)
    (x D : ℂ) :
    mainD s β ε ({z | ε⁻¹ * z ^ s ∈ Q}.indicator bt) x D = Q.indicator (mainD s β ε bt x) D := by
  have hs0 : 0 < s := Nat.pos_of_ne_zero hs
  have hroot : ∀ z ∈ G.rootSet s (ε * D), ε⁻¹ * z ^ s = D := by
    intro z hz
    have hz' : z ^ s = ε * D := by
      simpa [G.rootSet, Polynomial.mem_nthRoots hs0] using hz
    rw [hz', ← mul_assoc, inv_mul_cancel₀ hε, one_mul]
  unfold mainD
  by_cases hD : D ∈ Q
  · rw [Set.indicator_of_mem hD]
    refine Finset.sum_congr rfl fun z hz => ?_
    rw [Set.indicator_of_mem]
    show ε⁻¹ * z ^ s ∈ Q
    rw [hroot z hz]; exact hD
  · rw [Set.indicator_of_notMem hD]
    refine Finset.sum_eq_zero fun z hz => ?_
    rw [Set.indicator_of_notMem, smul_zero]
    show ε⁻¹ * z ^ s ∉ Q
    rw [hroot z hz]; exact hD

theorem bz_indicator (s : ℕ) (bt : ℂ → H) (Qz : Set ℂ) :
    bz s (Qz.indicator bt) = Qz.indicator (bz s bt) := by
  funext z
  by_cases hz : z ∈ Qz
  · simp [bz, Set.indicator_of_mem hz]
  · simp [bz, Set.indicator_of_notMem hz]

end cut

end

end Formalism.FourierDecayAlt.P.PBK
end

section

namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

theorem ptEntry_append_start (rest : C.LPt) : ∀ (H : C.LPt) (a b : ℕ),
    D.ptEntry (H ++ rest) (D.ptSize H + a) b = if D.ptSize H ≤ b then D.ptEntry rest a (b - D.ptSize H) else 0 := by
  intro H
  induction H with
  | nil => simp [D.ptSize]
  | cons block H' ih =>
    obtain ⟨s, t⟩ := block
    intro a b
    have hsz : D.ptSize ((s, t) :: H') = s + D.ptSize H' := by simp [D.ptSize]
    rw [hsz]
    show D.ptEntry ((s, t) :: (H' ++ rest)) (s + D.ptSize H' + a) b = _
    simp only [D.ptEntry]
    rw [if_neg (by omega)]
    by_cases hb : s ≤ b
    · rw [if_pos ⟨by omega, hb⟩, show s + D.ptSize H' + a - s = D.ptSize H' + a by omega,
        ih a (b - s)]
      by_cases h2 : D.ptSize H' ≤ b - s
      · rw [if_pos h2, if_pos (by omega), show b - s - D.ptSize H' = b - (s + D.ptSize H') by omega]
      · rw [if_neg h2, if_neg (by omega)]
    · rw [if_neg (by omega), if_neg (by omega)]

theorem det_big (H : C.LPt) (s : ℕ) (t : ℂ) (r : ℕ) (hs : 2 ≤ s) (hr : D.ptSize H + s = r + 1) :
    (D.ptMatN (H ++ [(s, t)]) r).det = 0 := by
  apply Matrix.det_eq_zero_of_row_eq_zero (⟨D.ptSize H, by omega⟩ : Fin r)
  intro j
  show D.ptEntry (H ++ [(s, t)]) (D.ptSize H) j = 0
  have h := ptEntry_append_start [(s, t)] H 0 j
  rw [add_zero] at h
  rw [h]
  split_ifs with hj
  · simp only [D.ptEntry]
    rw [if_pos ⟨by omega, by omega⟩, if_neg (by omega)]
  · rfl

theorem ptG_big (TT : ℝ) (H : C.LPt) (s : ℕ) (t : ℂ) (r : ℕ) (hs : 2 ≤ s) (hr : D.ptSize H + s = r + 1) :
    D.ptG TT r (H ++ [(s, t)]) = Complex.normSq (D.ptMatN (H ++ [(s, t)]) (r + 1)).det := by
  unfold D.ptG
  rw [det_big H s t r hs hr]
  simp

theorem wPt_big (TT : ℝ) (H : C.LPt) (s : ℕ) (t : ℂ) (r : ℕ) (hs : 2 ≤ s) (hr : D.ptSize H + s = r + 1)
    (hG : 0 < D.ptG TT r (H ++ [(s, t)])) : Top.wPt TT r (H ++ [(s, t)]) = 1 := by
  unfold Top.wPt
  rw [ptG_big TT H s t r hs hr] at hG ⊢
  exact div_self hG.ne'

section top

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}

theorem hsInner_zero_right' (A : Wq →L[ℂ] Wp) : B.hsInner A 0 = 0 := by
  unfold B.hsInner B.hsVec
  have : (WithLp.toLp 2 fun _ : Fin (Module.finrank ℂ Wq) => (0 : Wp)) = 0 := rfl
  simp only [ContinuousLinearMap.zero_apply, this, inner_zero_left]

theorem vecV_of_G (Bs : B.RealPlaceData P.k P.r Wp Wq) (ν' : Fin (2 * P.r + P.k + 1) → ℂ) (m₀ : B.Mat P.k P.r)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Q : C.LPt)
    (hG : ¬ 0 < D.ptG (Tz P.k P.r Bs.z * Tz P.k P.r Bs.z') P.r Q) : D.vecV Bs ν' m₀ F Q = 0 := by
  unfold D.vecV
  rw [dite_eq_right (fun h => hG h.2)]

theorem topOf_big (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter)
    (H H' : C.LPt) (s : ℕ) (t t' : ℂ) (hs : 2 ≤ s) (hH : D.ptSize H + s = P.r + 1) (hH' : D.ptSize H' + s = P.r + 1) :
    Top.topOf P p.l0 p.T p.ν' p.m₀ p.Θ p.TP F w (H ++ [(s, t)]) (H' ++ [(s, t')]) =
      ∑ e : Wd.Ix (Fin w.length), ∑ ρ : M.Ty P,
        ((Real.sqrt (Top.cW P p.l0 w e ρ).re * Real.sqrt (Top.cW P p.l0 w e ρ).re : ℝ) : ℂ) *
          B.hsInner ((p.TP.E ρ).comp (D.vecV p.T.base p.ν' p.m₀ (p.Θ.Θ w e F) (H ++ [(s, t)])))
            ((p.TP.E ρ).comp (D.vecV p.T.base p.ν' p.m₀ (p.Θ.Θ w e F) (H' ++ [(s, t')]))) := by
  unfold Top.topOf
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun ρ _ => ?_
  set TT := Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' with hTT
  by_cases h1 : 0 < D.ptG TT P.r (H ++ [(s, t)])
  · by_cases h2 : 0 < D.ptG TT P.r (H' ++ [(s, t')])
    · unfold Top.dH
      rw [wPt_big TT H s t P.r hs hH h1, wPt_big TT H' s t' P.r hs hH' h2, one_pow, one_mul]
    · rw [vecV_of_G _ _ _ _ _ h2, ContinuousLinearMap.comp_zero, hsInner_zero_right', mul_zero, mul_zero]
  · rw [vecV_of_G _ _ _ _ _ h1, ContinuousLinearMap.comp_zero, Formalism.FourierDecayAlt.P.PBD.hsInner_zero_left]
    simp

end top

end

end Formalism.FourierDecayAlt.P.PBL
end

section

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants MeasureTheory

noncomputable section

section kb

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def trJKB (p : KB.Pl P Wp Wq) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (J : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) :
    M.Ty P → MA.SmQ P.r P.TT :=
  fun ρ => MA.toSm P fun q =>
    ((Real.sqrt (MA.wq P.k q.1 P.TT) : ℝ) : ℂ) * inner ℂ (B.hsVec (e ρ q.1.2)) (B.hsVec (J (B.gq p.T.base q.1)))

def IsFrameKB (p : KB.Pl P Wp Wq) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) : Prop :=
  (∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (e ρ) {ζ : ℂ | P.TT < Complex.normSq ζ}) ∧
  ∀ ζ : ℂ, P.TT < Complex.normSq ζ →
    (∀ ρ, e ρ ζ ∈ NF.Fib P.k P.r p.T.base.z p.T.base.z' p.T.base.μsec p.T.base.π p.T.base.π' ζ) ∧
    (∀ ρ ρ', inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec (e ρ' ζ)) = if ρ = ρ' then (1 : ℂ) else 0) ∧
    ∀ X ∈ NF.Fib P.k P.r p.T.base.z p.T.base.z' p.T.base.μsec p.T.base.π p.T.base.π' ζ,
      X = ∑ ρ, inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec X) • e ρ ζ

end kb

def NFBddPtw : Prop :=
  ∀ (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r), 0 < P.TT → MA.IsModelLevel P (MA.DQ P) L →
    ∀ b ∈ Submonoid.closure (MA.bddSet P L), ∃ C : ℝ, ∀ (u : M.Ty P → MA.SmQ P.r P.TT) (q : MA.Qp P.r P.TT),
      ∑ ρ, ‖MA.evQ P (MA.actA P b u ρ) q‖ ^ 2 ≤ C * ∑ ρ, ‖MA.evQ P (u ρ) q‖ ^ 2

def NFTrNormKB : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)), IsFrameKB p e → ∃ C : ℝ, ∀ (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (c : Fin (P.r + 1) → ℂ) (q : MA.Qp P.r P.TT), q.1 = ((fun l => c l.castSucc), c (Fin.last P.r)) →
      D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) → 0 < TBB.Gp p (TBB.bigPt P.r c) →
      ∑ ρ, ‖MA.evQ P (trJKB p e (B.JF p.T.base H) ρ) q‖ ^ 2 ≤
        C * (∏ l : Fin P.r, Complex.normSq (c l.castSucc)) * TBB.Ew p (fun _ => 1) H (P.r + 1) [] (TBB.bigPt P.r c)

end

end Formalism.FourierDecayAlt.P.CutBP
end
