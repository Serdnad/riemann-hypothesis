module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle387
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle426
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle401
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle344
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle403
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
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle005
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix

theorem _root_.GlobalTheory.T.lintegral_prod_chartCoordinates_eq_prod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (h : (Low r → ℂ) → ℝ≥0∞), Measurable h → ∫⁻ z, ∏ τ, h (zOf X z τ) = ∏ _τ : X.Ψ, ∫⁻ w, h w := by
  first | exact @GlobalTheory.IntBall.lintegral_prod_zOf | exact GlobalTheory.IntBall.lintegral_prod_zOf | (intros; apply GlobalTheory.IntBall.lintegral_prod_zOf <;> assumption)
end

section

open MeasureTheory Matrix ValuativeRel

noncomputable section
namespace GlobalTheory.HeisUnit

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mul_mem_integer_iff_of_valuation_eq_one {u : kˣ} (hu : valuation k (u : k) = 1) (y : k) :
    (u : k) * y ∈ 𝒪[k] ↔ y ∈ 𝒪[k] := by
  simp only [Valuation.mem_integer_iff, map_mul, hu, one_mul]

theorem intInd_diagAt_mul {n d : ℕ} {u : kˣ} (hu : valuation k (u : k) = 1) (i0 : Fin n)
    (Y : Matrix (Fin n) (Fin d) k) : intInd (k := k) n d ((diagAt u i0).valᵀ * Y) = intInd (k := k) n d Y := by
  have e : ∀ i j, ((diagAt u i0).valᵀ * Y) i j ∈ 𝒪[k] ↔ Y i j ∈ 𝒪[k] := by
    intro i j
    rw [diagAt_val, diagonal_transpose, diagonal_mul]
    by_cases hi : i = i0
    · rw [if_pos hi]; exact mul_mem_integer_iff_of_valuation_eq_one hu _
    · rw [if_neg hi, one_mul]
  have hs : ((diagAt u i0).valᵀ * Y) ∈ {Y : Matrix (Fin n) (Fin d) k | ∀ i j, Y i j ∈ 𝒪[k]} ↔
      Y ∈ {Y : Matrix (Fin n) (Fin d) k | ∀ i j, Y i j ∈ 𝒪[k]} := by
    simp only [Set.mem_setOf_eq]
    exact forall_congr' fun i => forall_congr' fun j => e i j
  unfold intInd
  by_cases h : Y ∈ {Y : Matrix (Fin n) (Fin d) k | ∀ i j, Y i j ∈ 𝒪[k]}
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hs.mpr h)]; rfl
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (mt hs.mp h)]

theorem norm_char_unit_eq_one : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ},
    ∀ (ι : ((Fin n × Fin d → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ)),
    Set.InjOn ι (GlobalTheory.WeilM.SB (Fin n × Fin d → k) : Set _) →
    ∀ (S : GL (Fin n) k → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ),
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, S g φ ∈ GlobalTheory.WeilM.SB _) →
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∫⁻ y, ‖S g φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ) →
    ∀ χ : kˣ →* ℂˣ, (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ι (S g φ) = fun Y => (χ (Matrix.GeneralLinearGroup.det g) : ℂ) * ι φ (g.valᵀ * Y)) →
    ∀ φ0 ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k), ι φ0 = GlobalTheory.HeisUnit.intInd (k := k) n d →
    (∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∫⁻ y, ‖φ0 y‖ₑ ^ 2 ∂μ ≠ 0 ∧ ∫⁻ y, ‖φ0 y‖ₑ ^ 2 ∂μ ≠ ⊤) →
    ∀ (_i0 : Fin n) (u : kˣ), valuation k (u : k) = 1 → ‖(χ u : ℂ)‖ = 1 := by
  intro k _ _ _ _ n d ι hinj S hS hiso χ hι φ0 hφ0 hι0 hfin i0 u hu
  set g := diagAt u i0 with hg
  have hmem : (χ u : ℂ) • φ0 ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k) := Submodule.smul_mem _ _ hφ0
  have heq : S g φ0 = (χ u : ℂ) • φ0 := by
    refine hinj (hS g φ0 hφ0) hmem ?_
    rw [hι g φ0 hφ0, map_smul, hι0, det_diagAt]
    funext Y
    rw [intInd_diagAt_mul hu i0 Y]
    rfl
  letI : MeasurableSpace (Fin n × Fin d → k) := borel _
  haveI : BorelSpace (Fin n × Fin d → k) := ⟨rfl⟩
  have hμ : Measure.IsAddHaarMeasure (Measure.addHaar : Measure (Fin n × Fin d → k)) := inferInstance
  have h := hiso g φ0 hφ0 Measure.addHaar hμ
  rw [heq] at h
  exact GlobalTheory.WeilM.norm_eq_one_of_lintegral_eq h (hfin _ hμ).1 (hfin _ hμ).2

end GlobalTheory.HeisUnit
end
end

section

open MeasureTheory Matrix ValuativeRel


theorem _root_.GlobalTheory.T.norm_character_unit_eq_one_heisenberg : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ},
    ∀ (ι : ((Fin n × Fin d → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ)),
    Set.InjOn ι (GlobalTheory.WeilM.SB (Fin n × Fin d → k) : Set _) →
    ∀ (S : GL (Fin n) k → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ),
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, S g φ ∈ GlobalTheory.WeilM.SB _) →
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∫⁻ y, ‖S g φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ) →
    ∀ χ : kˣ →* ℂˣ, (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ι (S g φ) = fun Y => (χ (Matrix.GeneralLinearGroup.det g) : ℂ) * ι φ (g.valᵀ * Y)) →
    ∀ φ0 ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k), ι φ0 = GlobalTheory.HeisUnit.intInd (k := k) n d →
    (∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∫⁻ y, ‖φ0 y‖ₑ ^ 2 ∂μ ≠ 0 ∧ ∫⁻ y, ‖φ0 y‖ₑ ^ 2 ∂μ ≠ ⊤) →
    ∀ (_i0 : Fin n) (u : kˣ), valuation k (u : k) = 1 → ‖(χ u : ℂ)‖ = 1 := by
  intro k _ _ _ _ n d ι hinj S hS hiso χ hι φ0 hφ0 hι0 hfin i0 u hu
  let g := GlobalTheory.HeisUnit.diagAt u i0
  have hdet : Matrix.GeneralLinearGroup.det g = u := GlobalTheory.HeisUnit.det_diagAt u i0
  have hInd (Y : Matrix (Fin n) (Fin d) k) :
      GlobalTheory.HeisUnit.intInd (k := k) n d (g.valᵀ * Y) =
        GlobalTheory.HeisUnit.intInd (k := k) n d Y := by
    have hEntry (i : Fin n) (j : Fin d) : (g.valᵀ * Y) i j ∈ 𝒪[k] ↔ Y i j ∈ 𝒪[k] := by
      change ((GlobalTheory.HeisUnit.diagAt u i0).valᵀ * Y) i j ∈ 𝒪[k] ↔ Y i j ∈ 𝒪[k]
      rw [GlobalTheory.HeisUnit.diagAt_val, diagonal_transpose, diagonal_mul]
      by_cases hi : i = i0
      · rw [if_pos hi]
        simp only [Valuation.mem_integer_iff, map_mul, hu, one_mul]
      · rw [if_neg hi, one_mul]
    let L : Set (Matrix (Fin n) (Fin d) k) := {Z | ∀ i j, Z i j ∈ 𝒪[k]}
    have hL : g.valᵀ * Y ∈ L ↔ Y ∈ L :=
      forall_congr' fun i => forall_congr' fun j => hEntry i j
    change L.indicator 1 (g.valᵀ * Y) = L.indicator 1 Y
    by_cases hY : Y ∈ L
    · rw [Set.indicator_of_mem (hL.mpr hY), Set.indicator_of_mem hY]
      rfl
    · rw [Set.indicator_of_notMem (mt hL.mp hY), Set.indicator_of_notMem hY]
  have hmem : (χ u : ℂ) • φ0 ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k) :=
    Submodule.smul_mem _ _ hφ0
  have heq : S g φ0 = (χ u : ℂ) • φ0 := by
    refine hinj (hS g φ0 hφ0) hmem ?_
    rw [hι g φ0 hφ0, map_smul, hι0, hdet]
    funext Y
    rw [hInd Y]
    rfl
  letI : MeasurableSpace (Fin n × Fin d → k) := borel _
  haveI : BorelSpace (Fin n × Fin d → k) := ⟨rfl⟩
  have hμ : Measure.IsAddHaarMeasure (Measure.addHaar : Measure (Fin n × Fin d → k)) :=
    inferInstance
  have h := hiso g φ0 hφ0 Measure.addHaar hμ
  rw [heq] at h
  exact GlobalTheory.WeilM.norm_eq_one_of_lintegral_eq h (hfin _ hμ).1 (hfin _ hμ).2
end

section

noncomputable section

open Matrix MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.WeilM

namespace GlobalTheory.RankFibre

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem stdSum_rfl' (a b : ℕ) : stdSum (rfl : a + b = a + b) = finSumFinEquiv := by
  ext x; simp [stdSum]

theorem X0_mul_invT_parab (a b : ℕ) (p : parab k (blocks a b)) :
    (X0 (k := k) (finSumFinEquiv (m := a) (n := b)) * (invT (p : GL (Fin (a + b)) k)).val :
      Matrix (Fin a) (Fin (a + b)) k) =
      ((invT (leviProj k (blocks a b) p false)).val : Matrix (Fin a) (Fin a) k) *
        X0 (k := k) (finSumFinEquiv (m := a) (n := b)) := by
  have hA : (invT (leviProj k (blocks a b) p false)).val
      = ((leviProj k (blocks a b) p⁻¹ false : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)ᵀ := by
    rw [invT_val, map_inv]; rfl
  refine Matrix.ext fun i j => ?_
  rw [frameMatrixFirstColumnBlock_mul_apply, invT_val, hA]
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective j
  rcases s with j | j
  · have := leviProj_apply k (blocks a b) p⁻¹ false j i
    simp [stdSum_rfl'] at this
    simp [Matrix.mul_apply, X0, this]
  · have hne : ∀ (i : Fin a), Fin.castAdd b i ≠ Fin.natAdd a j := fun i h => by
      have := congrArg Fin.val h; simp at this; omega
    have := (mem_parab_two k).1 (p⁻¹).2 j i
    simp [stdSum_rfl'] at this
    simp [Matrix.mul_apply, X0, this, hne]

variable [MeasurableSpace k] [BorelSpace k]

theorem fibre_mem_indSpace (a b : ℕ) (ν β : kˣ →* ℂˣ) (Φ : Matrix (Fin a) (Fin (a + b)) k → ℂ) :
    fibre ν β a b Φ ∈ indSpace (parab k (blocks a b)) (ofChar (parChar ν β a b)) := by
  letI : MeasurableSpace (GL (Fin a) k) := Units.instMeasurableSpace
  haveI : BorelSpace (GL (Fin a) k) := GlobalTheory.SplitFlip.borel_GL
  intro p x
  rw [ofChar_apply]
  set A : GL (Fin a) k := leviProj k (blocks a b) p false with hAdef
  set D := leviProj k (blocks a b) p true with hDdef
  set Ψ := omA ν β 1 x Φ with hΨ
  set z : ℂ := ((a + b : ℕ) : ℂ) / 2 with hz
  let X : Matrix (Fin a) (Fin (a + b)) k := X0 (k := k) finSumFinEquiv
  set F : GL (Fin a) k → ℂ := fun g => Ψ (g.val * X) * (ν (gdet g) : ℂ) *
    apow (gdet g) z with hF
  set c : ℂ := (β (gdet (p : GL (Fin (a + b)) k)) : ℂ) * apow (gdet (p : GL (Fin (a + b)) k)) (-(a : ℂ) / 2) *
    ν (gdet A) * apow (gdet A) z with hc
  have h1 : omA ν β 1 ((p : GL (Fin (a + b)) k) * x) Φ = omA ν β 1 ↑p Ψ := by rw [hΨ, ← omA_mul, one_mul]
  have h2 : ∀ Y, omA ν β 1 (↑p : GL (Fin (a + b)) k) Ψ Y =
      (β (gdet (p : GL (Fin (a + b)) k)) : ℂ) * apow (gdet (p : GL (Fin (a + b)) k)) (-(a : ℂ) / 2) *
        Ψ (Y * (invT (p : GL (Fin (a + b)) k)).val) := by
    intro Y
    simp [omA]
  have hm : ∀ g : GL (Fin a) k,
      (g.val * X) * (invT (p : GL (Fin (a + b)) k)).val = (g * invT A).val * X := by
    intro g
    rw [Matrix.mul_assoc, X0_mul_invT_parab, ← Matrix.mul_assoc, ← Units.val_mul]
  have key : ∀ g : GL (Fin a) k, omA ν β 1 ((p : GL (Fin (a + b)) k) * x) Φ (g.val * X) * (ν (gdet g) : ℂ) *
      apow (gdet g) z = c * F (g * invT A) := by
    intro g
    rw [h1, h2, hm g]
    simp only [hF, hc, gdet_mul, gdet_invT, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, apow_mul,
      apow_inv, apow_neg]
    have n1 : (ν (gdet A) : ℂ) ≠ 0 := Units.ne_zero _
    have n2 : apow (gdet A) z ≠ 0 := apow_ne_zero _ _
    field_simp
  have hdet : gdet (p : GL (Fin (a + b)) k) = gdet A * gdet D := by
    have := det_parab k (blocks a b) p
    rw [Fintype.prod_bool] at this
    exact this.trans (mul_comm _ _)
  have hL : leviProj k (blocks a b) p = leviTwo k (Fin a) (Fin b) (A, D) := by
    funext t; cases t <;> rfl
  have hab : ∀ (s : ℂ) (y : kˣ), ((absPow k s y : ℂˣ) : ℂ) = apow y s := fun _ _ => rfl
  have hchar : ((parChar ν β a b p : ℂˣ) : ℂ) = c := by
    simp only [parChar, MonoidHom.comp_apply, MonoidHom.mul_apply, Units.val_mul, hL,
      MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulEquiv.symm_apply_apply, deltaHalf_two,
      MonoidHom.coe_fst, MonoidHom.coe_snd, detChar_apply, hab, Fintype.card_fin]
    have e : apow (gdet A) z * apow (gdet A) (-(a : ℂ) / 2) = apow (gdet A) ((b : ℂ) / 2) := by
      rw [← apow_add, hz]; congr 1; push_cast; ring
    rw [hc, hdet, map_mul, Units.val_mul, apow_mul]
    rw [← e]
    ring
  rw [hchar]
  have I1 : fibre ν β a b Φ ((p : GL (Fin (a + b)) k) * x) =
      ∫ g, c * F (g * invT A) ∂(haarVol (GlobalTheory.SplitWeil.KO k (Fin a))) :=
    integral_congr_ae (Filter.Eventually.of_forall key)
  have I2 : fibre ν β a b Φ x = ∫ g, F g ∂(haarVol (GlobalTheory.SplitWeil.KO k (Fin a))) := rfl
  haveI : MeasurableMul (GL (Fin a) k) :=
    ⟨fun g => (continuous_const.mul continuous_id).measurable,
      fun g => (continuous_id.mul continuous_const).measurable⟩
  rw [I1, I2, integral_const_mul, MeasureTheory.integral_mul_right_eq_self
    (μ := haarVol (GlobalTheory.SplitWeil.KO k (Fin a))) F (invT A)]

end GlobalTheory.RankFibre
end
end

section

open MeasureTheory Matrix ValuativeRel

open GlobalTheory GlobalTheory.HeisUnit in

theorem _root_.GlobalTheory.T.normSq_uniformizer_character_mul_residueCard_pow_eq_one : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ},
    ∀ (ι : ((Fin n × Fin d → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ)),
    Set.InjOn ι (GlobalTheory.WeilM.SB (Fin n × Fin d → k) : Set _) →
    ∀ (Tr : Matrix (Fin n) (Fin d) k → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ),
    (∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB _, Tr C φ ∈ GlobalTheory.WeilM.SB _ ∧ ι (Tr C φ) = fun Y => ι φ (Y + C)) →
    (∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ' ∈ GlobalTheory.WeilM.SB _,
        ∫ y, Tr C φ y * (starRingEnd ℂ) (Tr C φ' y) ∂μ = ∫ y, φ y * (starRingEnd ℂ) (φ' y) ∂μ) →
    ∀ (S : GL (Fin n) k → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ),
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, S g φ ∈ GlobalTheory.WeilM.SB _) →
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∫⁻ y, ‖S g φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ) →
    ∀ χ : kˣ →* ℂˣ, (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ι (S g φ) = fun Y => (χ (Matrix.GeneralLinearGroup.det g) : ℂ) * ι φ (g.valᵀ * Y)) →
    ∀ φ0 ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k), ι φ0 = GlobalTheory.HeisUnit.intInd k n d → φ0 ≠ 0 →
    ∀ (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (i0 : Fin n),
    (∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∀ T T' : Fin d → GlobalTheory.SplitFlip.Res (k := k) 1, T ≠ T' →
      ∫ y, Tr (GlobalTheory.HeisUnit.cosetRep ϖ i0 T) φ0 y * (starRingEnd ℂ) (Tr (GlobalTheory.HeisUnit.cosetRep ϖ i0 T') φ0 y) ∂μ = 0) →
    ‖(χ ϖ : ℂ)‖ ^ 2 * (GlobalTheory.SplitWeil.resCard k : ℝ) ^ d = 1 := by
  intro k _ _ _ _ n d ι hinj Tr hTr hTrIso S hS hSiso χ hχ φ0 hφ0 hι0 hne ϖ hϖ i0 horth
  classical
  set F := ∑ T : Fin d → SplitFlip.Res (k := k) 1, Tr (cosetRep ϖ i0 T) φ0 with hF
  have hFSB : F ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k) := Submodule.sum_mem _ fun T _ => (hTr _ φ0 hφ0).1
  have hSg : S (diagAt ϖ i0) φ0 = (χ ϖ : ℂ) • F := by
    apply hinj (hS _ φ0 hφ0) (Submodule.smul_mem _ _ hFSB)

    rw [hχ _ φ0 hφ0, map_smul, map_sum, det_diagAt, hι0]
    funext Y
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, (hTr _ φ0 hφ0).2, hι0]
    have hIntInd (M : Matrix (Fin n) (Fin d) k) :
        intInd k n d M = if ∀ i j, M i j ∈ 𝒪[k] then 1 else 0 := by
      simp only [intInd, Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply]
    have hSubMem (y : k) (t : SplitFlip.Res (k := k) 1) :
        y - (ϖ : k)⁻¹ * ((Quotient.out t : 𝒪[k]) : k) ∈ 𝒪[k] ↔
          ∃ h : (ϖ : k) * y ∈ 𝒪[k], t = Ideal.Quotient.mk _ ⟨(ϖ : k) * y, h⟩ := by
      have ht : t = Ideal.Quotient.mk _ (Quotient.out t) := (Quotient.out_eq t).symm
      set a := Quotient.out t
      have hϖ0 : (ϖ : k) ≠ 0 := ϖ.ne_zero
      constructor
      · intro hc
        have hy : (ϖ : k) * y = ϖ * (y - (ϖ : k)⁻¹ * a) + a := by field_simp; ring
        have hmem : (ϖ : k) * y ∈ 𝒪[k] := hy ▸ add_mem (mul_mem hϖ.mem hc) a.2
        refine ⟨hmem, ?_⟩
        rw [ht, Ideal.Quotient.eq, pow_one, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton']
        refine ⟨-⟨_, hc⟩, Subtype.ext ?_⟩
        push_cast
        field_simp
        ring
      · rintro ⟨h, e⟩
        have e' := ht.symm.trans e
        rw [Ideal.Quotient.eq, pow_one, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at e'
        obtain ⟨c, hc⟩ := e'
        have hc' : (c : k) * ϖ = a - ϖ * y := by simpa using congrArg Subtype.val hc
        have hinv : (ϖ : k)⁻¹ * ϖ = 1 := inv_mul_cancel₀ hϖ0
        have : y - (ϖ : k)⁻¹ * a = -(c : k) := by
          linear_combination (ϖ : k)⁻¹ * hc' - (y + c) * hinv
        rw [this]
        exact neg_mem c.2
    have hDiag :
        intInd k n d ((diagAt ϖ i0).valᵀ * Y) =
          ∑ T : Fin d → SplitFlip.Res (k := k) 1, intInd k n d (Y + cosetRep ϖ i0 T) := by
      have hL : ∀ i j, ((diagAt ϖ i0).valᵀ * Y) i j = (if i = i0 then (ϖ : k) else 1) * Y i j := by
        intro i j
        rw [diagAt_val, diagonal_transpose, diagonal_mul]
      have hR : ∀ (T : Fin d → SplitFlip.Res (k := k) 1) i j, (Y + cosetRep ϖ i0 T) i j =
          if i = i0 then Y i j - (ϖ : k)⁻¹ * ((Quotient.out (T j) : 𝒪[k]) : k) else Y i j := by
        intro T i j
        simp only [cosetRep, Matrix.add_apply, Matrix.of_apply]
        split_ifs <;> ring
      by_cases hQR : (∀ i j, i ≠ i0 → Y i j ∈ 𝒪[k]) ∧ ∀ j, (ϖ : k) * Y i0 j ∈ 𝒪[k]
      · obtain ⟨hQ, hRR⟩ := hQR
        let T0 : Fin d → SplitFlip.Res (k := k) 1 := fun j => Ideal.Quotient.mk _ ⟨_, hRR j⟩
        have hl : intInd k n d ((diagAt ϖ i0).valᵀ * Y) = 1 := by
          rw [hIntInd, ite_eq_left]
          intro i j
          rw [hL]
          split_ifs with h
          · subst h; exact hRR j
          · rw [one_mul]; exact hQ i j h
        have hs : ∀ T, intInd k n d (Y + cosetRep ϖ i0 T) = if T = T0 then 1 else 0 := by
          intro T
          rw [hIntInd]
          by_cases hT : T = T0
          · rw [ite_eq_left hT, ite_eq_left]
            intro i j
            rw [hR]
            split_ifs with h
            · subst h; exact (hSubMem _ _).2 ⟨hRR j, by rw [hT]⟩
            · exact hQ i j h
          · rw [ite_eq_right hT, ite_eq_right]
            intro hm
            apply hT
            funext j
            have := hm i0 j
            rw [hR, ite_eq_left rfl] at this
            obtain ⟨_, e⟩ := (hSubMem _ _).1 this
            exact e
        rw [hl, Finset.sum_congr rfl (fun T _ => hs T), Finset.sum_ite_eq']
        simp
      · have hl : intInd k n d ((diagAt ϖ i0).valᵀ * Y) = 0 := by
          rw [hIntInd, ite_eq_right]
          intro hm
          refine hQR ⟨fun i j h => ?_, fun j => ?_⟩
          · have := hm i j; rwa [hL, ite_eq_right h, one_mul] at this
          · have := hm i0 j; rwa [hL, ite_eq_left rfl] at this
        rw [hl]
        symm
        apply Finset.sum_eq_zero
        intro T _
        rw [hIntInd, ite_eq_right]
        intro hm
        refine hQR ⟨fun i j h => ?_, fun j => ?_⟩
        · have := hm i j; rwa [hR, ite_eq_right h] at this
        · have := hm i0 j
          rw [hR, ite_eq_left rfl] at this
          exact ((hSubMem _ _).1 this).1
    rw [hDiag]

  let _ : MeasurableSpace (Fin n × Fin d → k) := borel _
  have _ : BorelSpace (Fin n × Fin d → k) := ⟨rfl⟩
  let μ : Measure (Fin n × Fin d → k) := Measure.addHaar
  have hμ : μ.IsAddHaarMeasure := inferInstance
  have hiso := hSiso (diagAt ϖ i0) φ0 hφ0 μ hμ
  rw [hSg] at hiso
  simp only [Pi.smul_apply, smul_eq_mul, eNorm_mul, mul_pow] at hiso
  rw [lintegral_const_mul' _ _ (by simp [eNorm_eq_nnNorm])] at hiso
  obtain ⟨hFtop, hFint, -, hFi⟩ := GlobalTheory.T.schwartzBruhat_lintegral_sq_ne_top μ hμ F hFSB
  obtain ⟨h0top, h0int, h0ne, -⟩ := GlobalTheory.T.schwartzBruhat_lintegral_sq_ne_top μ hμ φ0 hφ0
  have hN0 : (∫⁻ y, ‖φ0 y‖ₑ ^ 2 ∂μ).toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨h0ne hne, h0top⟩
  have hint : ∀ T T' : Fin d → SplitFlip.Res (k := k) 1, Integrable (fun y => Tr (cosetRep ϖ i0 T) φ0 y *
      (starRingEnd ℂ) (Tr (cosetRep ϖ i0 T') φ0 y)) μ := fun T T' =>
    (GlobalTheory.T.schwartzBruhat_lintegral_sq_ne_top μ hμ _ (hTr _ φ0 hφ0).1).2.2.2 _ (hTr _ φ0 hφ0).1
  have hsum : ∫ y, F y * (starRingEnd ℂ) (F y) ∂μ =
      (Fintype.card (Fin d → SplitFlip.Res (k := k) 1) : ℂ) * ∫ y, φ0 y * (starRingEnd ℂ) (φ0 y) ∂μ := by
    have hpt : ∀ y, F y * (starRingEnd ℂ) (F y) = ∑ T : Fin d → SplitFlip.Res (k := k) 1, ∑ T' : Fin d → SplitFlip.Res (k := k) 1,
        Tr (cosetRep ϖ i0 T) φ0 y * (starRingEnd ℂ) (Tr (cosetRep ϖ i0 T') φ0 y) := by
      intro y

      rw [hF, Finset.sum_apply, map_sum, Finset.sum_mul_sum]
    simp_rw [hpt]
    rw [integral_finsetSum _ fun T _ => integrable_finsetSum _ fun T' _ => hint T T']
    simp_rw [integral_finsetSum _ fun T' _ => hint _ T']
    rw [Finset.card_univ.symm, ← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [Finset.sum_eq_single T (fun T' _ hT' => horth μ hμ T T' (Ne.symm hT')) (fun h => absurd (Finset.mem_univ _) h)]
    exact hTrIso μ hμ _ φ0 hφ0 φ0 hφ0
  rw [hFint, h0int] at hsum
  have hLF : (∫⁻ y, ‖F y‖ₑ ^ 2 ∂μ).toReal =
      (Fintype.card (Fin d → SplitFlip.Res (k := k) 1) : ℝ) * (∫⁻ y, ‖φ0 y‖ₑ ^ 2 ∂μ).toReal := by
    exact_mod_cast hsum
  have hiso' := congrArg ENNReal.toReal hiso
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, toReal_eNorm, hLF] at hiso'
  have hcard : (Fintype.card (Fin d → SplitFlip.Res (k := k) 1) : ℝ) = (GlobalTheory.SplitWeil.resCard k : ℝ) ^ d := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_eq_nat_card]
    have : Nat.card (SplitFlip.Res (k := k) 1) = GlobalTheory.SplitWeil.resCard k :=
      Nat.card_congr (Ideal.quotEquivOfEq (pow_one 𝓂[k])).toEquiv
    rw [this]; push_cast; ring
  rw [hcard] at hiso'
  apply mul_right_cancel₀ hN0
  linear_combination hiso'
end

section

open ValuativeRel Matrix

namespace GlobalTheory.RankCoinv

theorem omA_diag_boxFn_succ :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) (ν β : kˣ →* ℂˣ) (i₀ : A) (C : Matrix A D k), (∀ j, C i₀ j = 0) → ∀ m n : ℕ, GlobalTheory.SplitFlip.omA ν β (GlobalTheory.SplitFlip.diagGL (Function.update 1 i₀ ϖ)) 1 (GlobalTheory.RankCoinv.boxFn ϖ C (Function.update (fun _ => m) i₀ n)) = ((((ν ϖ)⁻¹ : ℂˣ) : ℂ) * GlobalTheory.SplitFlip.apow ϖ (-(Fintype.card D : ℂ) / 2)) • GlobalTheory.RankCoinv.boxFn ϖ C (Function.update (fun _ => m) i₀ (n + 1)) := by
  intro k _ _ _ _ A D _ _ _ _ ϖ ν β i₀ C hC m n
  have hdet : GlobalTheory.SplitFlip.gdet (GlobalTheory.SplitFlip.diagGL (Function.update (1 : A → kˣ) i₀ ϖ)) = ϖ := by
    rw [GlobalTheory.SplitFlip.gdet, GlobalTheory.SplitFlip.det_diagGL, Finset.prod_update_of_mem (Finset.mem_univ _)]
    simp
  have hinv : ((GlobalTheory.SplitFlip.diagGL (Function.update (1 : A → kˣ) i₀ ϖ))⁻¹).val =
      diagonal fun i => (((Function.update (1 : A → kˣ) i₀ ϖ i)⁻¹ : kˣ) : k) := rfl
  have h0 : 0 < valuation k (ϖ : k) := zero_lt_iff.2 (by simp)
  have key : ∀ X : Matrix A D k,
      (diagonal (fun i => (((Function.update (1 : A → kˣ) i₀ ϖ i)⁻¹ : kˣ) : k)) * X) ∈
        box ϖ C (Function.update (fun _ => m) i₀ n) ↔ X ∈ box ϖ C (Function.update (fun _ => m) i₀ (n + 1)) := by
    intro X
    simp only [box, Set.mem_setOf_eq, diagonal_mul]
    refine forall_congr' fun i => forall_congr' fun j => ?_
    by_cases hi : i = i₀
    · subst hi
      simp only [Function.update_self, hC, sub_zero, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
        pow_succ, Units.val_mul, map_mul, map_inv₀, map_pow]
      rw [inv_mul_le_iff₀ h0, mul_comm (valuation k (ϖ : k))]
    · simp [Function.update_of_ne hi]
  funext X
  rw [GlobalTheory.RankCoinv.omA_one_apply, hdet, Pi.smul_apply, smul_eq_mul, hinv]
  congr 1
  unfold boxFn
  by_cases hX : X ∈ box ϖ C (Function.update (fun _ => m) i₀ (n + 1))
  · rw [Set.indicator_of_mem ((key X).2 hX), Set.indicator_of_mem hX]
    rfl
  · rw [Set.indicator_of_notMem (fun h => hX ((key X).1 h)), Set.indicator_of_notMem hX]

end GlobalTheory.RankCoinv
end
