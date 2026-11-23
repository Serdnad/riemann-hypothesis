module

public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle006
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle007
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.TsumThree
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.DivAddLogbLeEightMulErrorScale
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.LemGBInImgIff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle013
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Formalism.WeaklyAdmissibleFiltrations.Statement

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

section

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthOneTwo

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

theorem lifts_lE (W : LocWach PD LL O v n) (A : ArcP n) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (c : ZMod n) {d : ℕ} (b : Fin d → W.DD T₂) (sol : Fin d → ℕ → Fin d → LL) (k₀ : Fin d)
    {f : W.EE} {k e : ℕ} (h : LiftsAt W A F c b sol k₀ (lE W k * f) e) :
    LiftsAt W A F c b sol k₀ f (k + e) := by
  unfold LiftsAt at h ⊢
  obtain ⟨w₁, z, h1, h2, h3, h4, h5⟩ := h
  refine ⟨w₁, z, h1, h2, h3, h4, ?_⟩
  have hl : lE W e * (lE W k * f) = lE W (k + e) * f := by
    unfold lE
    ring
  rw [hl] at h5
  exact h5

end Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthOneTwo
end
end

section

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

theorem numeric_bound_two_a_le_b1 (l : ℕ) (hl : 11 ≤ l) (b wm S η b₁ H : ℕ) (hb : 1 ≤ b) (hη : 20 * η ≤ b) (hS : 20 * S ≤ b)
    (hwm : 20 * wm ≤ b) (hb₁ : b ≤ b₁) (hH : H ≤ b + 2 * η + S)
    (hsm : 40 * Formalism.MainNotions.N.FrobeniusPowerSeries.Sg l (b + η + S) wm S η ≤ (b : ℝ) / 4) (a : ℝ)
    (ha : a ≤ (H : ℝ) * (2 * l - 1) / ((l : ℝ) - 1) ^ 2 + cW l H + 1) :
    2 * a + η + 1 ≤ (b₁ : ℝ) := by
  have hl' : (11 : ℝ) ≤ l := by exact_mod_cast hl
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hηR : 20 * (η : ℝ) ≤ b := by exact_mod_cast hη
  have hSR : 20 * (S : ℝ) ≤ b := by exact_mod_cast hS
  have hb₁R : (b : ℝ) ≤ b₁ := by exact_mod_cast hb₁
  have hHR : (H : ℝ) ≤ b + 2 * η + S := by exact_mod_cast hH
  have hcW := cW_le l hl (b + η + S) η H (by omega) (by omega)
  have hlog0 : 0 ≤ Real.logb l (2 * ((b + η + S : ℕ) : ℝ)) :=
    Real.logb_nonneg (by linarith) (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) η, Nat.cast_nonneg (α := ℝ) S])
  have hSg : Real.logb l (2 * ((b + η + S : ℕ) : ℝ)) + 1 ≤ Sg l (b + η + S) wm S η := by
    unfold Sg
    have h1 : 0 ≤ ((b + η + S : ℕ) : ℝ) / (l : ℝ) ^ 2 := by positivity
    have h2 : 0 ≤ ((wm : ℝ) + S + η) / l := by positivity
    linarith
  have hfrac : (H : ℝ) * (2 * l - 1) / ((l : ℝ) - 1) ^ 2 ≤ (H : ℝ) * (21 / 100) := by
    rw [div_le_iff₀ (by nlinarith)]
    have h3 : (2 * (l : ℝ) - 1) ≤ 21 / 100 * ((l : ℝ) - 1) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.2 hl') (by linarith : (0 : ℝ) ≤ l - 1)]
    nlinarith [Nat.cast_nonneg (α := ℝ) H]
  have hη0 := Nat.cast_nonneg (α := ℝ) η
  have hS0 := Nat.cast_nonneg (α := ℝ) S
  linarith

theorem numeric_bound_exponent_eg (l : ℕ) (hl : 11 ≤ l) (b wm S η b₁ H : ℕ) (hb : 1 ≤ b) (hη : 20 * η ≤ b) (hS : 20 * S ≤ b)
    (hwm : 20 * wm ≤ b) (hb₁ : b ≤ b₁) (hb₁' : b₁ ≤ b + η) (hH : H ≤ b + 2 * η + S) (A : ℕ)
    (ha : (A : ℝ) ≤ (H : ℝ) * (2 * l - 1) / ((l : ℝ) - 1) ^ 2 + cW l H + 1) :
    (EG l A S η b₁ : ℝ) ≤ 8 * Formalism.MainNotions.N.FrobeniusPowerSeries.Sg l (b + η + S) wm S η := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (by omega : 1 < l)
  have hl0 : (0 : ℝ) < l - 1 := by linarith
  have hcW : (0 : ℝ) ≤ (cW l H : ℝ) := Nat.cast_nonneg _
  have hHl : (0 : ℝ) ≤ (H : ℝ) * (2 * l - 1) / ((l : ℝ) - 1) ^ 2 := by
    apply div_nonneg _ (sq_nonneg _)
    exact mul_nonneg (Nat.cast_nonneg _) (by linarith)
  have ha' : max (A : ℝ) 1 ≤ (H : ℝ) * (2 * l - 1) / ((l : ℝ) - 1) ^ 2 + cW l H + 1 :=
    max_le ha (by linarith)
  have h5 := div_add_logb_le_eight_mul_errorScale l hl b wm S η b₁ H hb hη hS hwm hb₁ hb₁' hH (max (A : ℝ) 1) (le_max_right _ _) ha'
  have hmono : ((3 * (A : ℝ) + S + 2 * η : ℝ) - 2) / ((l : ℝ) - 1) ≤
      (3 * max (A : ℝ) 1 + S + 2 * η - 2) / ((l : ℝ) - 1) := by
    apply div_le_div_of_nonneg_right _ hl0.le
    linarith [le_max_left (A : ℝ) 1]
  have hSg : 0 ≤ Sg l (b + η + S) wm S η := by
    unfold Sg
    have h0 : 0 ≤ Real.logb l (2 * ((b + η + S : ℕ) : ℝ)) :=
      Real.logb_nonneg hl1 (by
        push_cast
        have : (1 : ℝ) ≤ b := by exact_mod_cast hb
        linarith [Nat.cast_nonneg (α := ℝ) η, Nat.cast_nonneg (α := ℝ) S])
    have h1 : 0 ≤ ((b + η + S : ℕ) : ℝ) / (l : ℝ) ^ 2 := by positivity
    have h2 : 0 ≤ ((wm : ℝ) + S + η) / l := by positivity
    linarith
  unfold EG
  by_cases hY : 0 ≤ ((3 * (A : ℝ) + S + 2 * η : ℝ) - 2) / ((l : ℝ) - 1) + Real.logb l ((b₁ : ℝ) + η - 1)
  · exact (Nat.floor_le hY).trans (by linarith)
  · rw [Nat.floor_of_nonpos (not_le.1 hY).le, Nat.cast_zero]
    linarith

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

section

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Polynomial

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable (W : LocWach PD LL O v n)

private theorem π₀_cancel (hπ : IsUnit (algebraMap (LetA O n) W.EE W.π₀)) {T : LocLat G Qp LL O}
    {a b : W.DD T} (h : W.π₀ • a = W.π₀ • b) : a = b := by
  obtain ⟨u, hu⟩ := hπ
  have ha : W.π₀ • a = (u : W.EE) • a := by rw [hu, algebraMap_smul]
  have hb : W.π₀ • b = (u : W.EE) • b := by rw [hu, algebraMap_smul]
  calc a = (↑u⁻¹ : W.EE) • ((u : W.EE) • a) := by rw [smul_smul, Units.inv_mul, one_smul]
    _ = (↑u⁻¹ : W.EE) • ((u : W.EE) • b) := by rw [← ha, h, hb]
    _ = b := by rw [smul_smul, Units.inv_mul, one_smul]

theorem dop_eq (hπ : IsUnit (algebraMap (LetA O n) W.EE W.π₀)) (T : LocLat G Qp LL O)
    (dop : W.DD T →ₗ[O] W.DD T) (hd : ∀ y, W.π₀ • dop y = W.γ T y - y) {x y : W.DD T}
    (h : W.γ T x - x = W.π₀ • y) : dop x = y :=
  π₀_cancel W hπ ((hd x).trans h)

theorem dop_pres (hπ : IsUnit (algebraMap (LetA O n) W.EE W.π₀)) (T : LocLat G Qp LL O) (i : ZMod n)
    (dop : W.DD T →ₗ[O] W.DD T) (hd : ∀ y, W.π₀ • dop y = W.γ T y - y)
    (hgN : ∀ x, Formalism.MainNotions.LiftingTheory.InNΔi W T i x → ∃ y, Formalism.MainNotions.LiftingTheory.InNΔi W T i y ∧ W.γ T x - x = W.π₀ • y)
    {x : W.DD T} (hx : Formalism.MainNotions.LiftingTheory.InNΔi W T i x) : Formalism.MainNotions.LiftingTheory.InNΔi W T i (dop x) := by
  obtain ⟨y, hy, hxy⟩ := hgN x hx
  rw [dop_eq W hπ T dop hd hxy]
  exact hy

theorem dop_map (hπ : IsUnit (algebraMap (LetA O n) W.EE W.π₀)) {T₁ T₂ : LocLat G Qp LL O}
    (F : LatHom T₁.L T₂.L)
    (dop₁ : W.DD T₁ →ₗ[O] W.DD T₁) (hd₁ : ∀ y, W.π₀ • dop₁ y = W.γ T₁ y - y)
    (dop₂ : W.DD T₂ →ₗ[O] W.DD T₂) (hd₂ : ∀ y, W.π₀ • dop₂ y = W.γ T₂ y - y) (y : W.DD T₁) :
    W.map F (dop₁ y) = dop₂ (W.map F y) := by
  apply π₀_cancel W hπ
  have hs : ∀ z : W.DD T₁, W.π₀ • W.map F z = W.map F (W.π₀ • z) := fun z => by
    rw [← algebraMap_smul W.EE W.π₀ (W.map F z), ← map_smul, algebraMap_smul]
  rw [hs, hd₁, hd₂, map_sub]
  congr 1
  exact W.map_γ F W.gam y

theorem aeval_dop_map (hπ : IsUnit (algebraMap (LetA O n) W.EE W.π₀)) {T₁ T₂ : LocLat G Qp LL O}
    (F : LatHom T₁.L T₂.L)
    (dop₁ : W.DD T₁ →ₗ[O] W.DD T₁) (hd₁ : ∀ y, W.π₀ • dop₁ y = W.γ T₁ y - y)
    (dop₂ : W.DD T₂ →ₗ[O] W.DD T₂) (hd₂ : ∀ y, W.π₀ • dop₂ y = W.γ T₂ y - y) (p : O[X]) (y : W.DD T₁) :
    W.map F (aeval dop₁ p y) = aeval dop₂ p (W.map F y) := by
  have hO : ∀ (c : O) (v : W.DD T₁), W.map F (c • v) = c • W.map F v := by
    intro c v
    rw [← algebraMap_smul (LetA O n) c v, ← algebraMap_smul W.EE (algebraMap O (LetA O n) c) v, map_smul,
      algebraMap_smul, algebraMap_smul]
  have hc : ∀ k : ℕ, ∀ y : W.DD T₁, W.map F ((dop₁ ^ k) y) = (dop₂ ^ k) (W.map F y) := by
    intro k
    induction k with
    | zero => intro y; simp
    | succ k ih =>
      intro y
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, dop_map W hπ F dop₁ hd₁ dop₂ hd₂, ih]

  rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range, LinearMap.sum_apply, LinearMap.sum_apply,
  map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [LinearMap.smul_apply, LinearMap.smul_apply, hO, hc]

theorem dop_inImg (hπ : IsUnit (algebraMap (LetA O n) W.EE W.π₀)) {T₁ T₂ : LocLat G Qp LL O}
    (F : LatHom T₁.L T₂.L) (i : ZMod n)
    (dop₁ : W.DD T₁ →ₗ[O] W.DD T₁) (hd₁ : ∀ y, W.π₀ • dop₁ y = W.γ T₁ y - y)
    (dop₂ : W.DD T₂ →ₗ[O] W.DD T₂) (hd₂ : ∀ y, W.π₀ • dop₂ y = W.γ T₂ y - y)
    (hgN₁ : ∀ x, Formalism.MainNotions.LiftingTheory.InNΔi W T₁ i x → ∃ y, Formalism.MainNotions.LiftingTheory.InNΔi W T₁ i y ∧ W.γ T₁ x - x = W.π₀ • y)
    {z : W.DD T₂} (hz : InImg W F i z) : InImg W F i (dop₂ z) := by
  unfold InImg at hz ⊢
  obtain ⟨x₁, hx₁, rfl⟩ := hz
  exact ⟨dop₁ x₁, dop_pres W hπ T₁ i dop₁ hd₁ hgN₁ hx₁, dop_map W hπ F dop₁ hd₁ dop₂ hd₂ x₁⟩

private theorem nΔi_add' {T : LocLat G Qp LL O} {i : ZMod n} {x y : W.DD T}
    (hx : Formalism.MainNotions.LiftingTheory.InNΔi W T i x) (hy : Formalism.MainNotions.LiftingTheory.InNΔi W T i y) :
    Formalism.MainNotions.LiftingTheory.InNΔi W T i (x + y) := by
  unfold Formalism.MainNotions.LiftingTheory.InNΔi at *
  exact ⟨(W.NΔ T).add_mem hx.1 hy.1, (W.Nl T i).add_mem hx.2 hy.2⟩

private theorem nΔi_smulO' {T : LocLat G Qp LL O} {i : ZMod n} (c : O) {x : W.DD T}
    (hx : Formalism.MainNotions.LiftingTheory.InNΔi W T i x) : Formalism.MainNotions.LiftingTheory.InNΔi W T i (c • x) := by
  unfold Formalism.MainNotions.LiftingTheory.InNΔi at *
  refine ⟨(W.NΔ T).smul_mem c hx.1, ?_⟩
  rw [← algebraMap_smul (LetA O n) c x]
  exact (W.Nl T i).smul_mem _ hx.2

private theorem nΔi_aeval (hπ : IsUnit (algebraMap (LetA O n) W.EE W.π₀)) (T : LocLat G Qp LL O)
    (i : ZMod n) (dop : W.DD T →ₗ[O] W.DD T) (hd : ∀ y, W.π₀ • dop y = W.γ T y - y)
    (hgN : ∀ x, Formalism.MainNotions.LiftingTheory.InNΔi W T i x → ∃ y, Formalism.MainNotions.LiftingTheory.InNΔi W T i y ∧ W.γ T x - x = W.π₀ • y)
    (p : O[X]) {x : W.DD T} (hx : Formalism.MainNotions.LiftingTheory.InNΔi W T i x) :
    Formalism.MainNotions.LiftingTheory.InNΔi W T i (aeval dop p x) := by
  have hpow : ∀ k : ℕ, ∀ x, Formalism.MainNotions.LiftingTheory.InNΔi W T i x → Formalism.MainNotions.LiftingTheory.InNΔi W T i ((dop ^ k) x) := by
    intro k
    induction k with
    | zero => intro x hx; rw [pow_zero, Module.End.one_apply]; exact hx
    | succ k ih =>
      intro x hx
      rw [pow_succ', Module.End.mul_apply]
      exact dop_pres W hπ T i dop hd hgN (ih x hx)
  rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply]
  refine Finset.sum_induction _ (Formalism.MainNotions.LiftingTheory.InNΔi W T i) (fun a b ha hb => nΔi_add' W ha hb) ?_ ?_
  · unfold Formalism.MainNotions.LiftingTheory.InNΔi
    exact ⟨(W.NΔ T).zero_mem, (W.Nl T i).zero_mem⟩
  · intro k _
    rw [LinearMap.smul_apply]
    exact nΔi_smulO' W _ (hpow k x hx)

theorem aeval_inImg (hπ : IsUnit (algebraMap (LetA O n) W.EE W.π₀)) {T₁ T₂ : LocLat G Qp LL O}
    (F : LatHom T₁.L T₂.L) (i : ZMod n)
    (dop₁ : W.DD T₁ →ₗ[O] W.DD T₁) (hd₁ : ∀ y, W.π₀ • dop₁ y = W.γ T₁ y - y)
    (dop₂ : W.DD T₂ →ₗ[O] W.DD T₂) (hd₂ : ∀ y, W.π₀ • dop₂ y = W.γ T₂ y - y)
    (hgN₁ : ∀ x, Formalism.MainNotions.LiftingTheory.InNΔi W T₁ i x → ∃ y, Formalism.MainNotions.LiftingTheory.InNΔi W T₁ i y ∧ W.γ T₁ x - x = W.π₀ • y)
    (p : O[X]) {z : W.DD T₂} (hz : InImg W F i z) : InImg W F i (aeval dop₂ p z) := by
  unfold InImg at hz ⊢
  obtain ⟨x₁, hx₁, rfl⟩ := hz
  exact ⟨aeval dop₁ p x₁, nΔi_aeval W hπ T₁ i dop₁ hd₁ hgN₁ p hx₁,
    aeval_dop_map W hπ F dop₁ hd₁ dop₂ hd₂ p x₁⟩

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end
