module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle016
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalizationQuotientSeparatedDvd
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Bundle004
public import Formalism.SharpRestriction.LevelLetterCocycles.LemmasUnramifiedOfRingCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.MapEvalPsPi
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.XAddOneMonic
public import Formalism.SharpRestriction.LevelLetterCocycles.AnnihilatorLevelsUnramifiedStatement
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.EvROnePow
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Bundle005
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.SmulSAddLeft
public import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.CmpOfMemX
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.ExpPowSubOne
import Formalism.SharpRestriction.LevelLetterCocycles.SaturationUnramifiedOfRingCondition
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.PowerSeries.Inverse
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Formalism.MainNotions.N.Pv.LocalLengthBound.Ser

section Phi

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)
    {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O]
    [Algebra Zl Ai] {RW : Type} [CommRing RW] [Algebra O RW] {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW}
    {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA} {ιdR : Ai →+* BdR} {p1 : Ai} {tS zS : BdR}

theorem phi_exp (hs : W.s = 1) (C : CmpTie W E ιdR p1 tS zS)
    {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} (h4W : Formalism.MainNotions.DeltaInvariantLattices.P4W W Pt)
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (i : ZMod n) {ζ : LL} (hζ : IsPrimitiveRoot ζ PD.p)
    (y : W.DD T) (hy : y ∈ W.N T) (hyl : (letE (i - 1) : LetA O n) • y = y) :
    ∃ d : ℤ → T.V ⊗[Qp] BdR, Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsExp W T i ζ (W.φD T y) d ∧ (∀ k : ℤ, k < 0 → d k = 0) ∧
      d 0 = ιV PD (LL := LL) (V := T.V) (φVB PD (LL := LL) (V := T.V) (W.cmp T ⟨y, hy⟩)) := by
  have hp := p_ne_zero_LL W
  obtain ⟨u, hu0, hq⟩ := MC.lev_q_eq W i hζ hp
  have hQ : W.lev i ζ W.Q = PowerSeries.X * u := by rw [MC.Q_eq_q W hs]; exact hq
  obtain ⟨m, hm⟩ := W.N_φ T y hy
  have hm' : W.Q ^ m • W.φD T y ∈ W.N T := hm
  set y' : ↥(W.N T) := ⟨y, hy⟩ with hy'

  have hcX : PowerSeries.constantCoeff (W.lev (i - 1) 1 W.X) = 0 := by
    have e : W.X = letπ := by simp [LocWach.X, hs]
    rw [e, MC.cc_lev_pi W (i - 1) 1 ⟨0, by rw [pow_zero]; exact IsPrimitiveRoot.one⟩, sub_self]
  have hneg : ∀ k : ℤ, k < 0 → C.levB T (i - 1) 1 y' k = 0 := by
    intro k hk
    have h0 := (((h4W T hT).1 (i - 1) 1 ⟨0, by simp⟩ hcX).1 y' k).2 hk
    rw [C.levN_eq] at h0
    exact Formalism.MainNotions.UnusedSlot80.LevR.ιV_inj (PD := PD) (V := T.V) (h0.trans (map_zero _).symm)
  have hζp : ζ ^ PD.p = 1 := hζ.pow_eq_one
  have hφrule : ∀ k : ℤ, W.levN T i ζ ⟨W.Q ^ m • W.φD T y, hm'⟩ k =
      ιV PD (LL := LL) (V := T.V) (∑ᶠ j : ℕ, PowerSeries.coeff j (W.lev i ζ (W.Q ^ m)) •
        (((PD.p : LL) ^ (k - (j : ℤ))) •
          φVB PD (LL := LL) (V := T.V) (C.levB T (i - 1) 1 y' (k - (j : ℤ))))) := by
    intro k
    rw [C.levN_eq, C.levB_φ T hT i ζ ⟨1, by rwa [pow_one]⟩ y' m hm' k, hζp]
  have hcoef : ∀ j : ℕ, j < m → PowerSeries.coeff j (W.lev i ζ (W.Q ^ m)) = 0 := by
    intro j hj
    rw [map_pow, hQ, mul_pow, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
  have hterm0 : ∀ (k : ℤ) (j : ℕ), (j < m ∨ k < (j : ℤ)) →
      PowerSeries.coeff j (W.lev i ζ (W.Q ^ m)) • (((PD.p : LL) ^ (k - (j : ℤ))) •
        φVB PD (LL := LL) (V := T.V) (C.levB T (i - 1) 1 y' (k - (j : ℤ)))) = 0 := by
    intro k j h
    rcases h with h | h
    · rw [hcoef j h, zero_smul]
    · rw [hneg _ (by omega), map_zero, smul_zero, smul_zero]
  set e : ℤ → T.V ⊗[Qp] BdR := W.levN T i ζ ⟨W.Q ^ m • W.φD T y, hm'⟩ with he
  have he_low : ∀ k : ℤ, k < m → e k = 0 := by
    intro k hk
    rw [hφrule, finsum_eq_zero_of_forall_eq_zero, map_zero]
    intro j
    by_cases hj : j < m
    · exact hterm0 k j (Or.inl hj)
    · exact hterm0 k j (Or.inr (by omega))
  have he_m : e m = (PowerSeries.constantCoeff u) ^ m •
      ιV PD (LL := LL) (V := T.V) (φVB PD (LL := LL) (V := T.V) (C.levB T (i - 1) 1 y' 0)) := by
    rw [hφrule, finsum_eq_single _ m (fun j hj => ?_)]
    · rw [map_pow, hQ, mul_pow, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, sub_self, zpow_zero, one_smul,
        map_smul]
    · rcases Nat.lt_or_gt_of_ne hj with h | h
      · exact hterm0 _ j (Or.inl h)
      · exact hterm0 _ j (Or.inr (by exact_mod_cast h))

  set e' : ℤ → T.V ⊗[Qp] BdR := fun k => e (k + m) with he'
  have hLBe' : LB 0 e' := fun k hk => he_low _ (by omega)
  have huK : PowerSeries.constantCoeff (u ^ m) ≠ 0 := by rw [map_pow]; exact pow_ne_zero _ hu0
  set d : ℤ → T.V ⊗[Qp] BdR := smulS (u ^ m)⁻¹ e' with hd
  have hLBd : LB 0 d := LB_smulS hLBe' _
  have hde : smulS ((PowerSeries.X * u) ^ m) d = e := by
    rw [mul_pow, smulS_mul hLBd, hd, ← smulS_mul hLBe', PowerSeries.mul_inv_cancel _ huK,
      smulS_one hLBe', smulS_X_pow hLBe']
    funext k
    simp [he']
  refine ⟨d, ⟨⟨0, hLBd⟩, W.Q ^ m, hm', ?_, fun k => ?_⟩, fun k hk => hLBd k hk, ?_⟩
  · rw [map_pow, hQ]
    exact pow_ne_zero _ (mul_ne_zero PowerSeries.X_ne_zero
      (fun h0 => hu0 (by rw [h0, map_zero])))
  · rw [map_pow, hQ, conv_eq, hde]
  ·
    have h1 : d 0 = PowerSeries.constantCoeff ((u ^ m)⁻¹) • e' 0 := by
      rw [hd, smulS_eq_sum hLBe' _ 0 1 (by norm_num)]
      simp
    rw [h1]
    simp only [he']
    rw [zero_add, he_m, smul_smul, PowerSeries.constantCoeff_inv, map_pow, inv_mul_cancel₀
      (pow_ne_zero _ hu0), one_smul]
    congr 2
    rw [← C.cmp_eq T hT (i - 1) y']
    congr 1
    exact Subtype.ext hyl

end Phi

end Formalism.MainNotions.N.Pv.LocalLengthBound
end
end

section

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound.LB

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80 Formalism.MainNotions.N.Ln03

section Con

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR} (W : LocWach PD LL O v n)
    [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [hpF : Fact PD.p.Prime]
    (hlm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O)
    (F : Type) [Field F] [Algebra O F]

theorem rs_root (s : ℕ) (ζ : Rs F PD.p s) :
    Polynomial.aeval ((ζ : F) - 1) (Zp (O := O) PD.p (s + 1)) = 0 :=
  root_Zp PD.p (s + 1) (by rw [add_sub_cancel]; exact rs_pow_N F PD.p s ζ)

def evAt (a : ZMod n) (s : ℕ) (ζ : Rs F PD.p s) : LetA O n →+* F :=
  (evR PD.p (s + 1) hlm (rs_root F s ζ)).toRingHom.comp
    (Pi.evalRingHom (fun _ : ZMod n => PowerSeries O) a)

theorem evAt_apply (a : ZMod n) (s : ℕ) (ζ : Rs F PD.p s) (x : LetA O n) :
    evAt hlm F a s ζ x = evR PD.p (s + 1) hlm (rs_root F s ζ) (x a) := rfl

theorem ev_qp (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) [CharZero F] (s : ℕ) {y : F}
    (hy : Polynomial.aeval y (Zp (O := O) PD.p (s + 1)) = 0) :
    (evR PD.p (s + 1) hlm hy (W.π₀₁ + ((PD.p : ℕ) : PowerSeries O)) = 0) ↔
      (y ≠ 0 ∧ (1 + y) ^ PD.p = 1) := by
  obtain ⟨w, hw⟩ := hR.2.2.2.2.1
  rw [Formalism.MainNotions.N.Pv.LocalLengthBound.eat_qp] at hw
  have hq0 : W.q₀ = (w : LetA O n) 0 * (W.π₀₁ + ((PD.p : ℕ) : PowerSeries O)) := by
    have := congrFun hw 0
    simpa [LocWach.q, Formalism.MainNotions.LiftingTheory.qp, LocWach.π₀] using this
  have hwu : evR PD.p (s + 1) hlm hy ((w : LetA O n) 0) ≠ 0 := by
    have hu : IsUnit ((w : LetA O n) 0) := (w.isUnit.map (Pi.evalMonoidHom (fun _ => PowerSeries O) 0))
    exact (hu.map (evR PD.p (s + 1) hlm hy)).ne_zero

  have hXq : PowerSeries.X * W.q₀ = (1 + PowerSeries.X) ^ PD.p - 1 := by
    rw [← W.φ₀_X, Formalism.MainNotions.UnusedSlot80.LG.φ₀_X_eq W]
  have hev : y * evR PD.p (s + 1) hlm hy W.q₀ = (1 + y) ^ PD.p - 1 := by
    have := congrArg (evR PD.p (s + 1) hlm hy) hXq
    rwa [map_mul, evR_X, map_sub, evR_onePow, map_one] at this
  have hsplit : evR PD.p (s + 1) hlm hy W.q₀ = evR PD.p (s + 1) hlm hy ((w : LetA O n) 0) *
      evR PD.p (s + 1) hlm hy (W.π₀₁ + ((PD.p : ℕ) : PowerSeries O)) := by
    rw [hq0, map_mul]
  constructor
  · intro h0
    have hq : evR PD.p (s + 1) hlm hy W.q₀ = 0 := by rw [hsplit, h0, mul_zero]
    refine ⟨fun hy0 => ?_, ?_⟩
    ·
      have hcc := evR_eq_cc PD.p (s + 1) hlm hy hy0 W.q₀
      have hc : PowerSeries.constantCoeff W.q₀ = ((PD.p : ℕ) : O) := by
        have := congrArg (PowerSeries.coeff 1) hXq
        rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply] at this
        rw [this]
        have e : ((1 + PowerSeries.X) ^ PD.p - 1 : PowerSeries O) =
            (((1 + Polynomial.X) ^ PD.p - 1 : Polynomial O) : PowerSeries O) := by
          simp [Polynomial.coe_pow]
        rw [e, Polynomial.coeff_coe, Polynomial.coeff_sub, Polynomial.coeff_one, add_comm,
          Polynomial.coeff_X_add_one_pow]
        simp
      rw [hq, hc, map_natCast] at hcc
      exact (Nat.cast_ne_zero.2 (hpF.out.ne_zero)) hcc.symm
    · have := hev
      rw [hq, mul_zero] at this
      exact (sub_eq_zero.1 this.symm)
  · rintro ⟨hy0, hyp⟩
    have hq : evR PD.p (s + 1) hlm hy W.q₀ = 0 := by
      have := hev
      rw [hyp, sub_self] at this
      exact (mul_eq_zero.1 this).resolve_left hy0
    rw [hsplit] at hq
    exact (mul_eq_zero.1 hq).resolve_left hwu

end Con

end Formalism.MainNotions.N.Pv.LocalLengthBound.LB
end
end

section

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries Formalism.MainNotions.N.Pv.LocalLengthBound.Ser TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

section Gam

variable (W : LocWach PD LL O v n)

theorem cc_φ₀ (f : PowerSeries O) : constantCoeff (W.φ₀ f) = constantCoeff f := by
  have e := PowerSeries.eq_X_mul_shift_add_const f
  have hC : ∀ r : O, W.φ₀ (C r) = C r := fun r => by
    have := W.φ₀.commutes r
    rwa [show (algebraMap O (PowerSeries O) r) = C r from rfl] at this
  conv_lhs => rw [e]
  rw [map_add (f := _), map_mul, W.φ₀_X, hC]
  simp

theorem gam_q [IsDomain O] (g : W.Gam) :
    ∃ v : LetA O n, W.γA g W.q = W.q * v ∧ IsUnit v := by
  obtain ⟨V, hV⟩ := PowerSeries.X_dvd_iff.mpr (W.γ₀_X g).1
  have hcV : constantCoeff V = (W.χΓ g : O) := by
    have := (W.γ₀_X g).2
    rw [hV, PowerSeries.coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply] at this
    exact this
  have hVu : IsUnit V := by
    rw [PowerSeries.isUnit_iff_constantCoeff, hcV]; exact Units.isUnit _
  have hφVu : IsUnit (W.φ₀ V) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, cc_φ₀, hcV]; exact Units.isUnit _
  have key : W.q₀ * W.φ₀ V = V * W.γ₀ g W.q₀ := by
    have h := W.γ₀_comm g PowerSeries.X
    rw [hV, map_mul, W.φ₀_X, map_mul, hV] at h
    have h2 : PowerSeries.X * (W.q₀ * W.φ₀ V) = PowerSeries.X * (V * W.γ₀ g W.q₀) := by
      rw [← mul_assoc, ← mul_assoc]; exact h
    exact mul_left_cancel₀ PowerSeries.X_ne_zero h2
  obtain ⟨Vu, hVu'⟩ := hVu
  refine ⟨fun _ => W.φ₀ V * ((Vu⁻¹ : (PowerSeries O)ˣ) : PowerSeries O), ?_, ?_⟩
  · funext i
    show W.γ₀ g W.q₀ = W.q₀ * (W.φ₀ V * ((Vu⁻¹ : (PowerSeries O)ˣ) : PowerSeries O))
    rw [← mul_assoc, key, ← hVu', mul_comm (Vu : PowerSeries O), mul_assoc, Units.mul_inv, mul_one]
  · refine Pi.isUnit_iff.2 fun _ => hφVu.mul (Units.isUnit _)

end Gam

section ArithmeticCylinders

theorem cc_rescale {LL' : Type} [Field LL'] (χ : LL') (u : PowerSeries LL') :
    constantCoeff (PowerSeries.rescale χ u) = constantCoeff u := by
  rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply,
    PowerSeries.coeff_rescale, pow_zero, one_mul]

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem gamma_levels_expansion [IsDomain O] (hs : W.s = 1) (c : ZMod n) (ζ : LL)
    (hLv : ∀ (x : ↥(W.N T)) (k : ℤ), W.levN T c ζ x k ∈ Formalism.MainNotions.WachCoordinates.FilLev W T c 0 (-k))
    (χ : LL) (hχ0 : χ ≠ 0)
    (hγN : ∀ (x : W.DD T) (hx : x ∈ W.N T) (hγx : W.γ T x ∈ W.N T) (k : ℤ),
      W.levN T c ζ ⟨W.γ T x, hγx⟩ k = χ ^ k • W.levN T c ζ ⟨x, hx⟩ k)
    (hγA : ∀ f : LetA O n, W.lev c ζ (W.γA W.gam f) = PowerSeries.rescale χ (W.lev c ζ f))
    (u : PowerSeries LL) (hu : W.lev c ζ W.q = X * u) (hu0 : constantCoeff u ≠ 0)
    {K : ℕ} {w : W.DD T} (hwN : W.Q ^ K • w ∈ W.N T) (hγw : W.γ T w - w ∈ W.N T) :
    ∃ d : ℤ → T.V ⊗[Qp] BdR, (∃ m, LB m d) ∧
      W.levN T c ζ ⟨W.Q ^ K • w, hwN⟩ = smulS ((X * u) ^ K) d ∧
      ∀ i : ℤ, (χ ^ i - 1) • d i ∈ Formalism.MainNotions.WachCoordinates.FilLev W T c 0 (-i) := by
  have hQ : W.Q = W.q := Q_eq_q W hs
  set x : ↥(W.N T) := ⟨W.Q ^ K • w, hwN⟩ with hxdef
  obtain ⟨m₀, hm₀⟩ := W.levN_supp T c ζ x
  obtain ⟨d, hdLB, hde⟩ := div_exists (m := m₀) hm₀ u hu0 K
  refine ⟨d, ⟨_, hdLB⟩, hde.symm, ?_⟩

  obtain ⟨vv, hvv, hvu⟩ := gam_q W W.gam
  obtain ⟨vU, hvU⟩ := hvu
  set v' : LetA O n := ((vU⁻¹ : (LetA O n)ˣ) : LetA O n)

  have hlv : W.lev c ζ vv = PowerSeries.C χ * PowerSeries.rescale χ u * u⁻¹ := by
    have h1 := hγA W.q
    rw [hvv, map_mul, hu, map_mul, PowerSeries.rescale_X] at h1
    have h2 : X * (u * W.lev c ζ vv) = X * (PowerSeries.C χ * PowerSeries.rescale χ u) := by
      rw [← mul_assoc, h1]; ring
    have h3 := mul_left_cancel₀ PowerSeries.X_ne_zero h2
    rw [← h3, mul_comm u, mul_assoc, PowerSeries.mul_inv_cancel _ hu0, mul_one]
  have hv'vv : v' * vv = 1 := by rw [← hvU]; exact Units.inv_mul vU
  have hlv' : W.lev c ζ v' = PowerSeries.C χ⁻¹ * u * (PowerSeries.rescale χ u)⁻¹ := by
    have hr0 : constantCoeff (PowerSeries.rescale χ u) ≠ 0 := by
      rw [cc_rescale]; exact hu0
    have h1 : W.lev c ζ vv * W.lev c ζ v' = 1 := by
      rw [← map_mul, mul_comm, hv'vv, map_one]
    rw [hlv] at h1
    have hAA : (PowerSeries.C χ⁻¹ * u * (PowerSeries.rescale χ u)⁻¹) *
        (PowerSeries.C χ * PowerSeries.rescale χ u * u⁻¹) = 1 := by
      calc (PowerSeries.C χ⁻¹ * u * (PowerSeries.rescale χ u)⁻¹) *
            (PowerSeries.C χ * PowerSeries.rescale χ u * u⁻¹)
          = (PowerSeries.C χ⁻¹ * PowerSeries.C χ) * (u * u⁻¹) *
            ((PowerSeries.rescale χ u)⁻¹ * PowerSeries.rescale χ u) := by ring
        _ = 1 := by
          rw [← map_mul, inv_mul_cancel₀ hχ0, map_one, PowerSeries.mul_inv_cancel _ hu0,
            PowerSeries.inv_mul_cancel _ hr0]
          ring
    calc W.lev c ζ v' = ((PowerSeries.C χ⁻¹ * u * (PowerSeries.rescale χ u)⁻¹) *
          (PowerSeries.C χ * PowerSeries.rescale χ u * u⁻¹)) * W.lev c ζ v' := by rw [hAA, one_mul]
      _ = (PowerSeries.C χ⁻¹ * u * (PowerSeries.rescale χ u)⁻¹) *
          (PowerSeries.C χ * PowerSeries.rescale χ u * u⁻¹ * W.lev c ζ v') := by ring
      _ = _ := by rw [h1, mul_one]

  have hγx : W.γ T (W.Q ^ K • w) ∈ W.N T := W.N_Γ T W.gam _ hwN
  have hγw' : W.Q ^ K • W.γ T w = v' ^ K • W.γ T (W.Q ^ K • w) := by
    have e1 : W.γ T (W.Q ^ K • w) = W.γA W.gam (W.Q ^ K) • W.γ T w :=
      Formalism.MainNotions.UnusedSlot80.SatW.γD_smulA' W T W.gam _ w
    rw [e1, map_pow, hQ, hvv, smul_smul]
    congr 1
    calc W.q ^ K = (v' * vv) ^ K * W.q ^ K := by rw [hv'vv, one_pow, one_mul]
      _ = v' ^ K * (W.q * vv) ^ K := by ring
  have hQγN : W.Q ^ K • W.γ T w ∈ W.N T := by
    rw [hγw']; exact (W.N T).smul_mem _ hγx
  have hlevγ : W.levN T c ζ ⟨W.Q ^ K • W.γ T w, hQγN⟩ = smulS ((X * u) ^ K) (resc χ d) := by
    have e2 : (⟨W.Q ^ K • W.γ T w, hQγN⟩ : ↥(W.N T)) = v' ^ K • ⟨W.γ T (W.Q ^ K • w), hγx⟩ :=
      Subtype.ext hγw'
    have hLBγ : LB m₀ (W.levN T c ζ ⟨W.γ T (W.Q ^ K • w), hγx⟩) := fun k hk => by
      rw [hγN _ hwN hγx k, hm₀ k hk, smul_zero]
    rw [e2]
    have e3 : W.levN T c ζ (v' ^ K • ⟨W.γ T (W.Q ^ K • w), hγx⟩) =
        smulS (W.lev c ζ (v' ^ K)) (W.levN T c ζ ⟨W.γ T (W.Q ^ K • w), hγx⟩) :=
      funext fun k => W.levN_smul T c ζ _ _ k
    have e4 : W.levN T c ζ ⟨W.γ T (W.Q ^ K • w), hγx⟩ = resc χ (W.levN T c ζ x) :=
      funext fun k => hγN _ hwN hγx k
    rw [e3, e4, ← hde, ← smulS_rescale hdLB χ hχ0, ← smulS_mul (LB_resc hdLB χ), map_pow, hlv']
    congr 1
    rw [map_pow, map_mul, PowerSeries.rescale_X, ← mul_pow]
    congr 1
    have hr0 : constantCoeff (PowerSeries.rescale χ u) ≠ 0 := by
      rw [cc_rescale]; exact hu0
    have hC : PowerSeries.C χ⁻¹ * PowerSeries.C χ = (1 : PowerSeries LL) := by
      rw [← map_mul, inv_mul_cancel₀ hχ0, map_one]
    calc PowerSeries.C χ⁻¹ * u * (PowerSeries.rescale χ u)⁻¹ *
          (PowerSeries.C χ * X * PowerSeries.rescale χ u)
        = (PowerSeries.C χ⁻¹ * PowerSeries.C χ) *
          (PowerSeries.rescale χ u * (PowerSeries.rescale χ u)⁻¹) * (X * u) := by ring
      _ = X * u := by rw [hC, PowerSeries.mul_inv_cancel _ hr0]; ring

  have hdiffN : W.Q ^ K • (W.γ T w - w) ∈ W.N T := (W.N T).smul_mem _ hγw
  have hg : W.levN T c ζ ⟨W.Q ^ K • (W.γ T w - w), hdiffN⟩ =
      smulS ((X * u) ^ K) (W.levN T c ζ ⟨W.γ T w - w, hγw⟩) := by
    have e5 : (⟨W.Q ^ K • (W.γ T w - w), hdiffN⟩ : ↥(W.N T)) = W.Q ^ K • ⟨W.γ T w - w, hγw⟩ := rfl
    rw [e5]
    have := funext fun k => W.levN_smul T c ζ (W.Q ^ K) ⟨W.γ T w - w, hγw⟩ k
    rw [this, map_pow, hQ, hu]
    rfl
  have hsplit : (⟨W.Q ^ K • (W.γ T w - w), hdiffN⟩ : ↥(W.N T)) =
      ⟨W.Q ^ K • W.γ T w, hQγN⟩ - x := Subtype.ext (by simp [hxdef, smul_sub])
  rw [hsplit, map_sub, hlevγ] at hg
  obtain ⟨m₁, hm₁⟩ := W.levN_supp T c ζ ⟨W.γ T w - w, hγw⟩
  have hLBr := LB_resc hdLB χ
  have heq : resc χ d - d = W.levN T c ζ ⟨W.γ T w - w, hγw⟩ := by
    have hx' : W.levN T c ζ x = smulS ((X * u) ^ K) d := hde.symm
    rw [hx', ← smulS_sub hLBr hdLB] at hg
    exact div_unique (m := min (m₀ - K) m₁) (LB_mono (LB_sub hLBr hdLB) (min_le_left _ _))
      (LB_mono hm₁ (min_le_right _ _)) u hu0 K hg
  intro i
  have h := hLv ⟨W.γ T w - w, hγw⟩ i
  rw [← heq] at h
  simpa [resc, sub_smul] using h

end ArithmeticCylinders

end Formalism.MainNotions.N.Pv.LocalLengthBound
end
end
