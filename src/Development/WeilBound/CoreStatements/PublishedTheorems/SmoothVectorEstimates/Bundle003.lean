module

public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerVanishingImpliesZero
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

namespace AveragingProjection

section Avg

variable {G : Type} [AddCommGroup G] [TopologicalSpace G]

theorem avg_add (Γ : AddSubgroup G) {Φ Ψ : G → ℂ} (hΦ : Continuous Φ) (hΨ : Continuous Ψ) {B : ℝ}
    (bΦ : ∀ x, ‖Φ x‖ ≤ B) (bΨ : ∀ x, ‖Ψ x‖ ≤ B) :
    avg Γ (fun x => Φ x + Ψ x) = avg Γ Φ + avg Γ Ψ := by
  let _ : MeasurableSpace G := borel G
  have _ : BorelSpace G := ⟨rfl⟩
  simp only [avg]
  split_ifs with h
  · have _ : IsFiniteMeasure (h.choose.1.restrict h.choose.2) :=
      isFiniteMeasure_restrict.2 (by rw [h.choose_spec.2.2]; exact ENNReal.one_ne_top)
    exact integral_add (Integrable.of_bound hΦ.aestronglyMeasurable B (ae_of_all _ bΦ))
      (Integrable.of_bound hΨ.aestronglyMeasurable B (ae_of_all _ bΨ))
  · simp

theorem avg_zero (Γ : AddSubgroup G) : avg Γ (fun _ => (0 : ℂ)) = 0 := by
  simpa using avg_const_mul Γ 0 (fun _ => (0 : ℂ))

theorem norm_avg_sub_le (Γ : AddSubgroup G) {Φ Ψ : G → ℂ} (hΦ : Continuous Φ) (hΨ : Continuous Ψ) {B : ℝ}
    (bΦ : ∀ x, ‖Φ x‖ ≤ B) (bΨ : ∀ x, ‖Ψ x‖ ≤ B) {C : ℝ} (hC : 0 ≤ C) (hd : ∀ x, ‖Φ x - Ψ x‖ ≤ C) :
    ‖avg Γ Φ - avg Γ Ψ‖ ≤ C := by
  let _ : MeasurableSpace G := borel G
  have _ : BorelSpace G := ⟨rfl⟩
  simp only [avg]
  split_ifs with h
  · have e1 : h.choose.1 h.choose.2 = 1 := h.choose_spec.2.2
    have _ : IsFiniteMeasure (h.choose.1.restrict h.choose.2) :=
      isFiniteMeasure_restrict.2 (by rw [e1]; exact ENNReal.one_ne_top)
    rw [← integral_sub (Integrable.of_bound hΦ.aestronglyMeasurable B (ae_of_all _ bΦ))
      (Integrable.of_bound hΨ.aestronglyMeasurable B (ae_of_all _ bΨ))]
    calc _ ≤ C * h.choose.1.real h.choose.2 :=
          norm_setIntegral_le_of_norm_le_const (by rw [e1]; exact ENNReal.one_lt_top) fun x _ => hd x
      _ = C := by simp [Measure.real, e1]
  · simpa using hC

theorem continuous_avg {X : Type} [TopologicalSpace X] (Γ : AddSubgroup G) {u : G → X} (hu : Continuous u) :
    Continuous fun φ : X →ᵇ ℂ => avg Γ (fun x => φ (u x)) := by
  refine (LipschitzWith.of_dist_le_mul (K := 1) fun φ ψ => ?_).continuous
  rw [dist_eq_norm, NNReal.coe_one, one_mul]
  exact norm_avg_sub_le Γ (φ.continuous.comp hu) (ψ.continuous.comp hu) (B := max ‖φ‖ ‖ψ‖)
    (fun x => (φ.norm_coe_le_norm _).trans (le_max_left _ _))
    (fun x => (ψ.norm_coe_le_norm _).trans (le_max_right _ _)) dist_nonneg
    (fun x => by rw [← dist_eq_norm]; exact BoundedContinuousFunction.dist_coe_le_dist (f := φ) (g := ψ) (u x))

end Avg

variable {E : Type} [Field E] [NumberField E] {a : ℕ} {ψ : AddChar (Ad E) ℂ}

def P (ψ : AddChar (Ad E) ℂ) (φ : XB E a) : Prop :=
  Good ψ (a - 1) φ ∧ ∀ γ g, φ (ratGL E a γ * g) = φ g

theorem P_zero : P ψ (0 : XB E a) := by
  refine ⟨⟨(0 : XB E a).continuous, fun γ _ g => rfl, fun k _ y g => by simp, fun r _ _ g => ?_⟩, fun γ g => rfl⟩
  simp only [BoundedContinuousFunction.coe_zero, Pi.zero_apply]
  exact avg_zero _

theorem P_add {φ φ' : XB E a} (h : P ψ φ) (h' : P ψ φ') : P ψ (φ + φ') := by
  refine ⟨⟨(φ + φ').continuous, fun γ hγ g => ?_, fun k hk y g => ?_, fun r hr hr' g => ?_⟩, fun γ g => ?_⟩
  · simp only [BoundedContinuousFunction.coe_add, Pi.add_apply, h.1.left γ hγ g, h'.1.left γ hγ g]
  · simp only [BoundedContinuousFunction.coe_add, Pi.add_apply, h.1.law k hk y g, h'.1.law k hk y g, mul_add]
  · simp only [BoundedContinuousFunction.coe_add, Pi.add_apply]
    rw [avg_add _ (Φ := fun x => φ (blkU x * g)) (Ψ := fun x => φ' (blkU x * g)) (φ.continuous.comp ((continuous_posU _).mul continuous_const))
      (φ'.continuous.comp ((continuous_posU _).mul continuous_const)) (B := max ‖φ‖ ‖φ'‖)
      (fun x => (φ.norm_coe_le_norm _).trans (le_max_left _ _))
      (fun x => (φ'.norm_coe_le_norm _).trans (le_max_right _ _)),
      h.1.van r hr hr' g, h'.1.van r hr hr' g, add_zero]
  · simp only [BoundedContinuousFunction.coe_add, Pi.add_apply, h.2 γ g, h'.2 γ g]

theorem P_smul (c : ℂ) {φ : XB E a} (h : P ψ φ) : P ψ (c • φ) := by
  refine ⟨⟨(c • φ).continuous, fun γ hγ g => ?_, fun k hk y g => ?_, fun r hr hr' g => ?_⟩, fun γ g => ?_⟩
  · simp only [BoundedContinuousFunction.coe_smul, Pi.smul_apply, h.1.left γ hγ g]
  · simp only [BoundedContinuousFunction.coe_smul, Pi.smul_apply, smul_eq_mul, h.1.law k hk y g]
    ring
  · simp only [BoundedContinuousFunction.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw [avg_const_mul, h.1.van r hr hr' g, mul_zero]
  · simp only [BoundedContinuousFunction.coe_smul, Pi.smul_apply, h.2 γ g]

theorem P_rt (k : GA E a) {φ : XB E a} (h : P ψ φ) : P ψ (Rt E a k φ) := by
  refine ⟨⟨(Rt E a k φ).continuous, fun γ hγ g => ?_, fun j hj y g => ?_, fun r hr hr' g => ?_⟩, fun γ g => ?_⟩
  · simp only [Rt_apply, mul_assoc]; exact h.1.left γ hγ (g * k)
  · simp only [Rt_apply, mul_assoc]; exact h.1.law j hj y (g * k)
  · simp only [Rt_apply, mul_assoc]; exact h.1.van r hr hr' (g * k)
  · simp only [Rt_apply, mul_assoc]; exact h.2 γ (g * k)

theorem isClosed_P : IsClosed {φ : XB E a | P ψ φ} := by
  have key : {φ : XB E a | P ψ φ} =
      (⋂ (γ : GL (Fin a) E), ⋂ (g : GA E a), {φ : XB E a | φ (ratGL E a γ * g) = φ g}) ∩
      ((⋂ (k : ℕ), ⋂ (_ : a - 1 < k), ⋂ (y : UnipotentBlockColumnIndex a k k → Ad E), ⋂ (g : GA E a),
          {φ : XB E a | φ (blkU y * g) = ψ (dot (eLast a k) y) * φ g}) ∩
        (⋂ (r : ℕ), ⋂ (_ : 0 < r), ⋂ (_ : r ≤ a - 1), ⋂ (g : GA E a),
          {φ : XB E a | avg (ratV E (UnipotentBlockColumnIndex a r (a - 1))) (fun x => φ (blkU x * g)) = 0})) := by
    ext φ
    simp only [P, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · rintro ⟨hG, hl⟩
      exact ⟨hl, hG.law, hG.van⟩
    · rintro ⟨hl, hlaw, hvan⟩
      exact ⟨⟨φ.continuous, fun γ _ g => hl γ g, hlaw, hvan⟩, hl⟩
  rw [key]
  refine (isClosed_iInter fun γ => isClosed_iInter fun g => ?_).inter
    ((isClosed_iInter fun k => isClosed_iInter fun _ => isClosed_iInter fun y => isClosed_iInter fun g => ?_).inter
      (isClosed_iInter fun r => isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun g => ?_))
  · exact isClosed_eq (continuous_eval_const _) (continuous_eval_const _)
  · exact isClosed_eq (continuous_eval_const _) (continuous_const.mul (continuous_eval_const _))
  · exact isClosed_eq (continuous_avg _ ((continuous_posU _).mul continuous_const)) continuous_const

end AveragingProjection

open AveragingProjection in
theorem averaging_projection_linear : G2a := by
  intro E _ _ _ a ψ _
  refine ⟨{ carrier := {φ | P ψ φ}, add_mem' := P_add, zero_mem' := P_zero, smul_mem' := P_smul },
    isClosed_P, fun g φ h => P_rt g h, fun φ => Iff.rfl⟩

end PositivityTheory.jumpWindows

end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

namespace UnipotentCharacter

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def chi (ψ : AddChar (Ad E) ℂ) (w : Pl E) : AddChar (w.adicCompletion E) ℂ where
  toFun y := ψ (sFin E (sLoc E w y))
  map_zero_eq_one' := by simp only [map_zero, AddChar.map_zero_eq_one]
  map_add_eq_mul' x y := by simp only [map_add (f := _), AddChar.map_add_eq_mul]

theorem chi_apply (ψ : AddChar (Ad E) ℂ) (w : Pl E) (y : w.adicCompletion E) :
    chi ψ w y = ψ (sFin E (sLoc E w y)) := rfl

theorem chi_cont {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) (w : Pl E) : Continuous (chi ψ w) :=
  hψ.cont.comp ((continuous_const.prodMk continuous_id : Continuous fun x : Af E =>
    ((0, x) : InfiniteAdeleRing E × Af E)).comp (CuspSub.continuous_sLoc w))

theorem lastE_loc (w : Pl E) {k : ℕ} (y : UnipotentBlockColumnIndex a k k → w.adicCompletion E) :
    lastE k (fun t => sFin E (sLoc E w (y t))) = sFin E (sLoc E w (lastE k y)) := by
  unfold lastE

  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  split_ifs <;> simp

theorem sum_of {X : Type} [AddCommMonoid X] [Module ℂ X] (P : X → Prop) (h0 : P 0)
    (hadd : ∀ x y, P x → P y → P (x + y)) (hsm : ∀ (c : ℂ) x, P x → P (c • x)) {ι : Type}
    (T : Finset ι) (c : ι → ℂ) (f : ι → X) (hf : ∀ t, P (f t)) : P (∑ t ∈ T, c t • f t) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using h0
  | insert t T ht ih => rw [Finset.sum_insert ht]; exact hadd _ _ (hsm _ _ (hf t)) ih

end UnipotentCharacter

open UnipotentCharacter in
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in
theorem whittaker_expansion_cuspidal : S2 → S9 → MirabolicColumnBlock → G0 → G5 → G5b → G7 := by
  intro hS2 hS9 hS10 hG0 hG5 hG5b E _ _ _ a ψ hψ S Y Y' hY hY' n m w hw hmw hSt
  obtain ⟨φ, hφY, φ', hφY', hsm, hsm', hlev, hlev', h1, hWh⟩ := hSt
  obtain ⟨-, -, i3, i4, i5, -, -, i8, -, i10, -⟩ := hG0 E a
  obtain ⟨g5a, g5r, -, g5c⟩ := hG5 E a ψ hψ
  obtain ⟨b1, b2, b3, b4, b5⟩ := hG5b E a S
  obtain ⟨s10dec, -, -, s10blk1, -⟩ := hS10 (w.adicCompletion E) a (m w + 1)
  have hpoly : PolyBd (repI E a) := ⟨1, 0, zero_le_one, fun g x => by
    rw [pow_zero, mul_one, one_mul]
    exact le_of_eq (norm_Rt (infGL E a g) x)⟩
  obtain ⟨s0, sadd, ssmul, -, -, -⟩ := hS2 (InfinitePlace E) a (XB E a) (repI E a) hpoly
  let U : Set (GL (Fin a) (w.adicCompletion E)) := {u | repW a w u φ = φ} ∩ {u | repW a w u φ' = φ'}
  have hU : U ∈ 𝓝 (1 : GL (Fin a) (w.adicCompletion E)) := Filter.inter_mem (hlev w hw) (hlev' w hw)
  have hne : ∃ x, chi ψ w x ≠ 1 := by
    obtain ⟨y, hy⟩ := hψ.loc w
    exact ⟨y, hy⟩
  obtain ⟨T, c, η, r, hη1, hr1, hrMir, -, -, hmain⟩ :=
    hS9 (w.adicCompletion E) a (m w) hmw (chi ψ w) (chi_cont hψ w) hne (XB E a) (repW a w) U hU
  have inS : ∀ u, InS S (fl a w u : GA E a) := fun u v hv => i5 w v u (fun e => hv (e ▸ hw))
  have stab : ∀ Z : Submodule ℂ (XB E a), YOK ψ S Z → ∀ u, ∀ x ∈ Z, repW a w u x ∈ Z :=
    fun Z hZ u x hx => hZ.stable _ (inS u) x hx
  have memZ : ∀ Z : Submodule ℂ (XB E a), YOK ψ S Z → ∀ x ∈ Z, ∑ t ∈ T, c t • repW a w t x ∈ Z :=
    fun Z hZ x hx => Z.sum_mem fun t _ => Z.smul_mem _ (stab Z hZ t x hx)
  have smZ : ∀ x : XB E a, SmV (repI E a) x → SmV (repI E a) (∑ t ∈ T, c t • repW a w t x) :=
    fun x hx => sum_of _ s0 sadd ssmul T c _ fun t => b1 _ x hx
  have levZ : ∀ x : XB E a, Lev S x → Lev S (∑ t ∈ T, c t • repW a w t x) :=
    fun x hx => sum_of _ b5 b4 b3 T c _ fun t => b2 _ x hx

  have key : ∀ Z : Submodule ℂ (XB E a), YOK ψ S Z → ∀ x ∈ Z, (∀ u ∈ U, repW a w u x = x) →
      ∀ g' : GA E a, cLoc w g' = 1 → ∀ h, GlobalTheory (m w + 1) h →
      Wh ψ (∑ t ∈ T, c t • repW a w t x) (g' * fl a w h) = η h * Wh ψ x (g' * fl a w (r h)) := by
    intro Z hZ x hx hxU g' hg' h hh
    obtain ⟨Λ, hΛ⟩ := g5a g'
    have hcond : ∀ z ∈ Z, ∀ y : UnipotentBlockColumnIndex a (m w + 1) (m w + 1) → w.adicCompletion E,
        (Λ : XB E a →ₗ[ℂ] ℂ) (repW a w (blkU y) z) = chi ψ w (lastE (m w + 1) y) * (Λ : XB E a →ₗ[ℂ] ℂ) z := by
      intro z hz y
      show Λ _ = _ * Λ _
      rw [hΛ _ (hZ.good _ (stab Z hZ _ z hz)),
        hΛ _ (hZ.good _ hz), repW_apply, g5r, i8 w g' hg', i10,
        (g5c z (hZ.good _ hz)).2.2 (m w + 1) (Nat.succ_pos _), lastE_loc, chi_apply]
    have := hmain x hxU Z (stab Z hZ) hx (Λ : XB E a →ₗ[ℂ] ℂ) hcond h hh
    change Λ _ = η h * Λ _ at this
    rw [hΛ _ (hZ.good _ (stab Z hZ _ _ (memZ Z hZ x hx))), hΛ _ (hZ.good _ (stab Z hZ _ _ hx)),
      repW_apply, repW_apply, g5r, g5r] at this
    exact this
  refine ⟨_, memZ Y hY φ hφY, _, memZ Y' hY' φ' hφY', smZ φ hsm, smZ φ' hsm', levZ φ hlev, levZ φ' hlev', ?_, ?_⟩
  · have := key Y hY φ hφY (fun u hu => hu.1) 1 (map_one _) 1 s10blk1
    rw [hr1] at this
    simp only [map_one, mul_one] at this
    rw [this]
    exact mul_ne_zero hη1 h1
  · intro g hg
    obtain ⟨hgI, hgL⟩ := hg
    have hgw : Mir (m w + 1) (cLoc w g) := by simpa using hgL w
    obtain ⟨y, h, hh, hdec⟩ := s10dec _ hgw
    set g' : GA E a := g * (fl a w (cLoc w g))⁻¹ with hg'def
    have hg' : cLoc w g' = 1 := by rw [hg'def, map_mul, map_inv, i4, mul_inv_cancel]
    have red : ∀ Z : Submodule ℂ (XB E a), YOK ψ S Z → ∀ x ∈ Z, (∀ u ∈ U, repW a w u x = x) →
        Wh ψ (∑ t ∈ T, c t • repW a w t x) g =
          ψ (lastE (m w + 1) fun t => sFin E (sLoc E w (y t))) * (η h * Wh ψ x (g' * fl a w (r h))) := by
      intro Z hZ x hx hxU
      have e : g = blkU (fun t => sFin E (sLoc E w (y t))) * (g' * fl a w h) := by
        rw [← i10, ← mul_assoc, ← i8 w g' hg', mul_assoc, ← map_mul, ← hdec, hg'def, inv_mul_cancel_right]
      rw [e, (g5c _ (hZ.good _ (memZ Z hZ x hx))).2.2 (m w + 1) (Nat.succ_pos _), key Z hZ x hx hxU g' hg' h hh]
    rw [red Y hY φ hφY (fun u hu => hu.1), red Y' hY' φ' hφY' (fun u hu => hu.2)]
    by_cases hη : η h = 0
    · rw [hη]; simp
    congr 2
    refine hWh _ ⟨?_, fun v => ?_⟩
    · rw [map_mul, hg'def, map_mul, map_inv, i3, i3, inv_one, mul_one, mul_one]
      exact hgI
    · rcases eq_or_ne v w with rfl | hv
      · rw [map_mul, hg', i4, one_mul]
        exact hrMir h hh hη
      · rw [map_mul, hg'def, map_mul, map_inv, i5 w v _ hv, i5 w v _ hv, inv_one, mul_one, mul_one]
        simpa [hv] using hgL v

end PositivityTheory.jumpWindows

end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

namespace InfiniteFiniteFactorization

open Classical

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem stepInf (h6 : G6) {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) {S : Finset (Pl E)}
    {Y Y' : Submodule ℂ (XB E a)} (hY : YOK ψ S Y) (hY' : YOK ψ S Y') (m : Pl E → ℕ)
    (h : St ψ S Y Y' 0 m) : ∀ n, n ≤ a - 1 → St ψ S Y Y' n m := by
  intro n
  induction n with
  | zero => intro _; exact h
  | succ n ih => intro hn; exact h6 E a ψ hψ S Y Y' hY hY' n m (by omega) (ih (by omega))

theorem stepFin (h7 : G7) {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) {S : Finset (Pl E)}
    {Y Y' : Submodule ℂ (XB E a)} (hY : YOK ψ S Y) (hY' : YOK ψ S Y') (w : Pl E) (hw : w ∈ S)
    (n : ℕ) (m : Pl E → ℕ) (hm : m w = 0) (h : St ψ S Y Y' n m) :
    ∀ k, k ≤ a - 1 → St ψ S Y Y' n (Function.update m w k) := by
  intro k
  induction k with
  | zero => intro _; rw [Function.update_eq_self_iff.mpr hm.symm]; exact h
  | succ k ih =>
    intro hk
    have h' := h7 E a ψ hψ S Y Y' hY hY' n (Function.update m w k) w hw
      (by simp only [Function.update_self]; omega) (ih (by omega))
    simpa only [Function.update_self, Function.update_idem] using h'

end InfiniteFiniteFactorization

open InfiniteFiniteFactorization in
theorem whittaker_factorization_places : G6 → G7 → FourierInductionSteps := by
  classical
  intro h6 h7 E _ _ _ a ψ hψ S Y Y' hY hY' h0
  have h1 := stepInf h6 hψ hY hY' (fun _ => 0) h0 (a - 1) le_rfl
  have key : ∀ T : Finset (Pl E), T ⊆ S →
      St ψ S Y Y' (a - 1) (fun w => if w ∈ T then a - 1 else 0) := by
    intro T
    refine Finset.induction_on T ?_ ?_
    · intro _
      simpa using h1
    · intro x T hx ih hT
      have h := stepFin h7 hψ hY hY' x (hT (Finset.mem_insert_self x T)) (a - 1)
        (fun w => if w ∈ T then a - 1 else 0) (by simp [hx])
        (ih (subset_trans (Finset.subset_insert x T) hT)) (a - 1) le_rfl
      convert h using 1
      funext w
      by_cases hw : w = x
      · subst hw; simp
      · simp [hw]
  exact key S subset_rfl

end PositivityTheory.jumpWindows

end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

namespace CornerGLContinuity

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem glmap_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T)
    (x : GL (Fin a) R) :
    GeneralLinearGroup.map (g.comp f) x = GeneralLinearGroup.map g (GeneralLinearGroup.map f x) := by
  ext i j; rfl

theorem cornerGL_blkU {R S : Type} [CommRing R] [CommRing S] (s : R →ₙ+* S) (k : ℕ) (y : UnipotentBlockColumnIndex a k k → R) :
    cornerGL a s (blkU y) = blkU fun t => s (y t) := by
  apply Units.ext
  ext i j
  change (1 : Matrix (Fin a) (Fin a) S) i j - s ((1 : Matrix (Fin a) (Fin a) R) i j) +
    s ((1 + posM Subtype.val y) i j) = (1 + posM Subtype.val fun t => s (y t)) i j

  simp only [posM, Matrix.add_apply, Matrix.sum_apply, map_add (f := _), map_sum, Matrix.single_apply,
  apply_ite s, map_zero]
  abel

theorem cLoc_eq (w : Pl E) (x : GA E a) :
    cLoc w x = GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) x) :=
  glmap_comp _ _ x

theorem gf_ext {g h : GL (Fin a) (Af E)}
    (H : ∀ w, GeneralLinearGroup.map (pLoc E w) g = GeneralLinearGroup.map (pLoc E w) h) : g = h := by
  refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext _ fun w => ?_)
  exact congrArg (fun x : GL (Fin a) (w.adicCompletion E) => x i j) (H w)

theorem locGL_mul_comm {v : Pl E} (h : GL (Fin a) (v.adicCompletion E)) {k : GL (Fin a) (Af E)}
    (hk : GeneralLinearGroup.map (pLoc E v) k = 1) : locGL E a v h * k = k * locGL E a v h := by
  refine gf_ext fun w => ?_
  rw [map_mul, map_mul]
  by_cases hw : w = v
  · subst hw
    rw [hk, mul_one, one_mul]
  · rw [pLoc_locGL_of_ne hw, mul_one, one_mul]

open Classical in
theorem map_pLoc_prod (g : GA E a) (v : Pl E) : ∀ l : List (Pl E), l.Nodup →
    GeneralLinearGroup.map (pLoc E v) (l.map fun w => locGL E a w (cLoc w g)).prod =
      if v ∈ l then cLoc v g else 1
  | [], _ => by simp
  | w :: l, h => by
    rw [List.map_cons, List.prod_cons, map_mul, map_pLoc_prod g v l (List.nodup_cons.1 h).2]
    by_cases hv : v = w
    · subst hv
      rw [pLoc_locGL, if_neg (List.nodup_cons.1 h).1, mul_one]
      simp
    · rw [pLoc_locGL_of_ne hv, one_mul]
      simp [hv]

theorem continuous_glmap {R S : Type} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
    [IsTopologicalRing R] [IsTopologicalRing S] (p : R →+* S) (hp : Continuous p) :
    Continuous (GeneralLinearGroup.map (n := Fin a) p) := by
  refine Continuous.units_map _ ?_
  exact continuous_pi fun i => continuous_pi fun j => hp.comp ((continuous_apply j).comp (continuous_apply i))

theorem continuous_cornerGL' {R S : Type} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
    [IsTopologicalRing R] [IsTopologicalRing S] (s : R →ₙ+* S) (hs : Continuous s) :
    Continuous (cornerGL a s) := by
  refine Continuous.units_map _ ?_
  change Continuous fun x : Matrix (Fin a) (Fin a) R => 1 - matN a s 1 + matN a s x
  refine continuous_const.add ?_
  exact continuous_pi fun i => continuous_pi fun j => hs.comp ((continuous_apply j).comp (continuous_apply i))

end CornerGLContinuity

open CornerGLContinuity in
theorem standard_stabiliser_bound : G0 := by
  intro E _ _ _ a
  have hpInf : Continuous (pInf E) :=
    (continuous_pi fun w =>
      (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
        (continuous_apply w)).comp continuous_fst
  have hpLoc : ∀ w : Pl E, Continuous (pLoc E w) := fun w =>
    RestrictedProduct.continuous_eval (R := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
      (A := fun v => (v.adicCompletionIntegers E : Set (v.adicCompletion E))) w
  have hfin : Continuous (finGL E a) :=
    continuous_cornerGL' _ (continuous_const.prodMk continuous_id :
      Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))
  have hinf : Continuous (infGL E a) :=
    continuous_cornerGL' _ ((continuous_infEq E).prodMk continuous_const :
      Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))
  refine ⟨fun y => pInf_infGL y, fun w y => ?_, fun w u => pInf_finGL _, fun w u => ?_,
    fun w v u hvw => ?_, fun g h h1 h2 => ?_, fun g hg y => ?_, fun w g hg u => ?_,
    fun k y => cornerGL_blkU _ k y, fun w k y => ?_, fun S g => ?_, ?_, fun w => ?_, fun w => ?_, hinf⟩
  · rw [cLoc_eq, pFin_infGL, map_one]
  · rw [cLoc_eq, fl, MonoidHom.comp_apply, pFin_finGL, pLoc_locGL]
  · rw [cLoc_eq, fl, MonoidHom.comp_apply, pFin_finGL, pLoc_locGL_of_ne hvw]
  · exact ga_ext h1 (gf_ext fun w => by rw [← cLoc_eq, ← cLoc_eq]; exact h2 w)
  · have hg' : GeneralLinearGroup.map (pInf E) g = 1 := hg
    exact ga_ext (by rw [map_mul, map_mul, hg', pInf_infGL, one_mul, mul_one])
      (by rw [map_mul, map_mul, pFin_infGL, one_mul, mul_one])
  · have hg' : GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) g) = 1 := by
      rw [← cLoc_eq]; exact hg
    exact ga_ext (by rw [map_mul, map_mul, fl, MonoidHom.comp_apply, pInf_finGL, one_mul, mul_one])
      (by rw [map_mul, map_mul, fl, MonoidHom.comp_apply, pFin_finGL]; exact (locGL_mul_comm u hg').symm)
  · rw [fl, MonoidHom.comp_apply, locGL, cornerGL_blkU, finGL, cornerGL_blkU]
  · refine ⟨infGL E a (cInf g) * finGL E a (S.toList.map fun w => locGL E a w (cLoc w g)).prod, ?_, ?_, ?_⟩
    · change GeneralLinearGroup.map (pInf E) _ = _
      rw [map_mul, pInf_infGL, pInf_finGL, mul_one]
    · intro w hw
      rw [cLoc_eq, map_mul, map_mul, pFin_infGL, pFin_finGL, map_one, one_mul,
        map_pLoc_prod g w _ S.nodup_toList, if_pos (Finset.mem_toList.2 hw)]
    · intro w hw
      rw [cLoc_eq, map_mul, map_mul, pFin_infGL, pFin_finGL, map_one, one_mul,
        map_pLoc_prod g w _ S.nodup_toList, if_neg (fun h => hw (Finset.mem_toList.1 h))]
  · exact continuous_glmap _ hpInf
  · exact continuous_glmap _ ((hpLoc w).comp continuous_snd)
  · exact hfin.comp (continuous_cornerGL' _ (CuspSub.continuous_sLoc w))

end PositivityTheory.jumpWindows

end
end
