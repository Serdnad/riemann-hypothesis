module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.HermitianCurvature.StatementU
public import Mathlib.Analysis.Complex.RealDeriv

@[expose] public section

section

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace PI.UnitaryCorollaryDerivatives

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
open Formalism.FourierDecayAlt.P.BetaSesquilinearity

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def hhF (k j ρ a b : ℕ) (g : B.Mat k (j + ρ)) : ℂ := (DjU k j ρ g)⁻¹ ^ a * (star (DjU k j ρ g))⁻¹ ^ b

theorem cB_alg (a b : ℕ) (c D : ℂ) (t : ℝ) :
    (Complex.exp ((t : ℂ) * c) * D)⁻¹ ^ a * (star (Complex.exp ((t : ℂ) * c) * D))⁻¹ ^ b =
      Complex.exp ((t : ℂ) * -((a : ℂ) * c + (b : ℂ) * conj c)) * (D⁻¹ ^ a * (star D)⁻¹ ^ b) := by
  have e1 : star (Complex.exp ((t : ℂ) * c)) = Complex.exp ((t : ℂ) * conj c) := by
    rw [Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_ofReal]
  rw [star_mul', e1, mul_inv, mul_inv, mul_pow, mul_pow, ← Complex.exp_neg, ← Complex.exp_neg,
    ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  have : Complex.exp ((t : ℂ) * -((a : ℂ) * c + (b : ℂ) * conj c)) =
      Complex.exp ((a : ℂ) * -((t : ℂ) * c)) * Complex.exp ((b : ℂ) * -((t : ℂ) * conj c)) := by
    rw [← Complex.exp_add]; ring_nf
  rw [this]; ring

theorem cB_lamnorm (a b : ℕ) (c : ℂ) {j : ℕ} {m : ℝ} (hc : ‖c‖ ≤ (j : ℝ) * m) :
    ‖-((a : ℂ) * c + (b : ℂ) * conj c)‖ ≤ ((a + b : ℕ) : ℝ) * j * m := by
  rw [norm_neg]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_natCast, Complex.norm_conj]
  push_cast
  have ha : (0 : ℝ) ≤ a := by positivity
  have hb : (0 : ℝ) ≤ b := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hc ha, mul_le_mul_of_nonneg_left hc hb]

theorem cB_curve (hC : DjCurve) (k j ρ a b : ℕ) :
    ∃ lam : Bool × B.Mat k (j + ρ) → ℂ, ∀ x : Bool × B.Mat k (j + ρ), inLieP k j ρ x.2 →
      ‖lam x‖ ≤ ((a + b : ℕ) : ℝ) * j * mx x.2 ∧
      ∀ (g : B.Mat k (j + ρ)) (t : ℝ), hhF k j ρ a b (crv x g t) = Complex.exp ((t : ℂ) * lam x) * hhF k j ρ a b g := by
  have key : ∀ x : Bool × B.Mat k (j + ρ), ∃ μ : ℂ, inLieP k j ρ x.2 →
      ‖μ‖ ≤ ((a + b : ℕ) : ℝ) * j * mx x.2 ∧
      ∀ (g : B.Mat k (j + ρ)) (t : ℝ), hhF k j ρ a b (crv x g t) = Complex.exp ((t : ℂ) * μ) * hhF k j ρ a b g := by
    rintro ⟨bb, Y⟩
    by_cases hY : inLieP k j ρ Y
    · obtain ⟨c₁, c₂, h₁, h₂, hcur⟩ := hC k j ρ Y hY
      cases bb
      · refine ⟨-((a : ℂ) * c₁ + (b : ℂ) * conj c₁), fun _ => ⟨cB_lamnorm a b c₁ h₁, fun g t => ?_⟩⟩
        rw [show crv (false, Y) g t = g * NormedSpace.exp ((t : ℂ) • Y) from rfl]
        unfold hhF
        rw [(hcur g t).1, cB_alg]
      · refine ⟨-((a : ℂ) * c₂ + (b : ℂ) * conj c₂), fun _ => ⟨cB_lamnorm a b c₂ h₂, fun g t => ?_⟩⟩
        rw [show crv (true, Y) g t = NormedSpace.exp (-((t : ℂ) • Y)) * g from rfl]
        unfold hhF
        rw [(hcur g t).2, cB_alg]
    · exact ⟨0, fun h => absurd h hY⟩
  choose lam hlam using key
  exact ⟨lam, hlam⟩

theorem cB_smooth {k j ρ : ℕ} (hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (DjU k j ρ)) {P : B.Mat k (j + ρ) → ℂ}
    (hP : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) P) (a b : ℕ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g => P g * (DjU k j ρ g)⁻¹ ^ a * (star (DjU k j ρ g))⁻¹ ^ b)
      {g | DjU k j ρ g ≠ 0} := by
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g => (DjU k j ρ g)⁻¹) {g | DjU k j ρ g ≠ 0} :=
    hD.contDiffOn.inv (fun g hg => hg)
  have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g => star (DjU k j ρ g)) := by
    have := Complex.conjCLE.contDiff.comp hD
    simpa [Function.comp_def, Complex.star_def] using this
  have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g => (star (DjU k j ρ g))⁻¹) {g | DjU k j ρ g ≠ 0} :=
    hs.contDiffOn.inv (fun g hg => by simpa using hg)
  exact (hP.contDiffOn.mul (h1.pow a)).mul (h2.pow b)

theorem cB_mx_le {α : Type*} [Fintype α] {X : Matrix α α ℂ} (hX : ∀ a b, ‖X a b‖ ≤ 1) : mx X ≤ 1 := by
  unfold mx
  exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun a => (pi_norm_le_iff_of_nonneg zero_le_one).2 fun b => hX a b

theorem cB_unitLie {k j ρ : ℕ} {u : List (B.Mat k (j + ρ))} (hu : unitP k j ρ u) :
    ∀ X ∈ u, B.unitLie k (j + ρ) X := fun X hX => ⟨(hu X hX).1.1, (hu X hX).2⟩

theorem cB_wP {k j ρ : ℕ} {u v : List (B.Mat k (j + ρ))} (hu : unitP k j ρ u) (hv : unitP k j ρ v) :
    ∀ x ∈ wL u ++ wR v, inLieP k j ρ x.2 ∧ ∀ a b, ‖x.2 a b‖ ≤ 1 := by
  intro x hx
  simp only [wL, wR, List.mem_append, List.mem_map] at hx
  rcases hx with ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩
  · exact hu X hX
  · exact hv X hX

theorem cB_bound (hP : PolyB) (hC : DjCurve) {k j ρ κ : ℕ} {P : B.Mat k (j + ρ) → ℂ} (hPd : IsPolyDeg κ P)
    (a b n : ℕ) {δ : ℝ} (hδ : 0 < δ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : List (B.Mat k (j + ρ)), unitP k j ρ u →
      unitP k j ρ v → u.length + v.length ≤ n → ∀ g ∈ B.GV k (j + ρ), δ ≤ ‖DjU k j ρ g‖ →
        ‖Dw (wL u ++ wR v) (fun g => P g * (DjU k j ρ g)⁻¹ ^ a * (star (DjU k j ρ g))⁻¹ ^ b) g‖ ≤
          C * B.gN g ^ (κ : ℝ) := by
  obtain ⟨hPs, hWB⟩ := hP k (j + ρ) κ P hPd
  obtain ⟨CP, hCP⟩ := hWB n
  obtain ⟨lam, hlam⟩ := cB_curve hC k j ρ a b
  set Λ : ℝ := ((a + b : ℕ) : ℝ) * j with hΛ
  have hΛ0 : 0 ≤ Λ := by positivity
  refine ⟨(1 + Λ) ^ n * (δ⁻¹ ^ (a + b) * |CP|), by positivity, ?_⟩
  intro u v hu hv hl g hg hDg
  have hw := cB_wP hu hv
  have e : (fun g => P g * (DjU k j ρ g)⁻¹ ^ a * (star (DjU k j ρ g))⁻¹ ^ b) =
      fun g => hhF k j ρ a b g • P g := by
    funext g; simp only [hhF, smul_eq_mul]; ring
  rw [e, cA_Dw_expmul lam (hhF k j ρ a b) _ P hPs (fun x hx g t => (hlam x (hw x hx).1).2 g t), norm_smul]
  have hp := gN_pos hg
  have hD0 : 0 < ‖DjU k j ρ g‖ := lt_of_lt_of_le hδ hDg
  have hh : ‖hhF k j ρ a b g‖ ≤ δ⁻¹ ^ (a + b) := by
    unfold hhF
    rw [norm_mul, norm_pow, norm_pow, norm_inv, norm_inv, norm_star, pow_add]
    have : ‖DjU k j ρ g‖⁻¹ ≤ δ⁻¹ := inv_anti₀ hδ hDg
    exact mul_le_mul (pow_le_pow_left₀ (by positivity) this a) (pow_le_pow_left₀ (by positivity) this b)
      (by positivity) (by positivity)
  have hb := cA_Dwl_bound lam hΛ0 g (|CP| * B.gN g ^ (κ : ℝ)) (wL u ++ wR v) P hPs
    (fun x hx => (hlam x (hw x hx).1).1.trans (by
      have := cB_mx_le (hw x hx).2
      calc ((a + b : ℕ) : ℝ) * j * mx x.2 ≤ ((a + b : ℕ) : ℝ) * j * 1 :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = Λ := by rw [mul_one]))
    (by
      intro s hs
      obtain ⟨u', v', hu', hv', rfl⟩ := sub_LR hs
      rw [← dLR_eq]
      have := hCP u' v' (fun X hX => cB_unitLie hu X (hu'.subset hX)) (fun X hX => cB_unitLie hv X (hv'.subset hX))
        (by have := hu'.length_le; have := hv'.length_le; omega) g hg
      simp only [List.map_append, List.map_const', List.sum_append, Nat.cast_add] at this
      refine this.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)) |>.trans_eq ?_
      congr 2
      simp)
  have hpow : (1 + Λ) ^ (wL u ++ wR v).length ≤ (1 + Λ) ^ n := by
    rw [len_LR]; exact pow_le_pow_right₀ (by linarith) hl
  calc ‖hhF k j ρ a b g‖ * ‖Dwl lam (wL u ++ wR v) P g‖
      ≤ δ⁻¹ ^ (a + b) * ((1 + Λ) ^ n * (|CP| * B.gN g ^ (κ : ℝ))) :=
        mul_le_mul hh (hb.trans (mul_le_mul_of_nonneg_right hpow (by positivity))) (norm_nonneg _) (by positivity)
    _ = (1 + Λ) ^ n * (δ⁻¹ ^ (a + b) * |CP|) * B.gN g ^ (κ : ℝ) := by ring

end PI.UnitaryCorollaryDerivatives
end
end

section

open Matrix
open scoped ComplexConjugate ContDiff

noncomputable section

namespace PI.UnitaryCorollaryDerivatives.CRH

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

def cs (cost : Mat k r → ℕ) (w : List (Bool × Mat k r)) : ℕ := (w.map fun x => cost x.2).sum

lemma cs_append (cost : Mat k r → ℕ) (w w' : List (Bool × Mat k r)) : cs cost (w ++ w') = cs cost w + cs cost w' := by
  simp [cs, List.map_append, List.sum_append]

lemma cs_perm (cost : Mat k r → ℕ) {w w' : List (Bool × Mat k r)} (h : w.Perm w') : cs cost w = cs cost w' := by
  unfold cs
  exact (h.map _).sum_eq

lemma cs_LR (cost : Mat k r → ℕ) (u v : List (Mat k r)) :
    ((u ++ v).map cost).sum = cs cost (wL u ++ wR v) := by
  simp [cs, wL, wR, List.map_append, List.map_map, Function.comp_def]

def admitted (n : ℕ) (w : List (Bool × Mat k r)) : Prop :=
  ∃ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) ∧ (∀ X ∈ v, unitLie k r X) ∧ u.length + v.length ≤ n ∧
    w = wL u ++ wR v

lemma Adm_sub {n : ℕ} {w w' : List (Bool × Mat k r)} (h : w'.Sublist w) (hw : admitted n w) : admitted n w' := by
  obtain ⟨u, v, hu, hv, hl, rfl⟩ := hw
  obtain ⟨r₁, r₂, rfl, h1, h2⟩ := List.sublist_append_iff.1 h
  obtain ⟨u', hu', rfl⟩ := List.sublist_map_iff.1 (show r₁.Sublist (u.map (Prod.mk true)) from h1)
  obtain ⟨v', hv', rfl⟩ := List.sublist_map_iff.1 (show r₂.Sublist (v.map (Prod.mk false)) from h2)
  refine ⟨u', v', fun X hX => hu X (hu'.subset hX), fun X hX => hv X (hv'.subset hX), ?_, rfl⟩
  have := hu'.length_le
  have := hv'.length_le
  omega

lemma cd_iter {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (q : ℕ) : ContDiff ℝ ∞ (iteratedDeriv q h) := by
  rw [iteratedDeriv_eq_iterate]
  exact ContDiff.iterate_deriv q hh

lemma cd_ofReal {ψ : Mat k r → ℝ} (hψ : ContDiff ℝ ∞ ψ) : ContDiff ℝ ∞ (fun g => ((ψ g : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp hψ

lemma chain (x : Bool × Mat k r) {ψ : Mat k r → ℝ} {h : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hh : ContDiff ℝ ∞ h)
    (q : ℕ) :
    Dx x (fun g => ((iteratedDeriv q h (ψ g) : ℝ) : ℂ)) =
      fun g => ((iteratedDeriv (q + 1) h (ψ g) : ℝ) : ℂ) * Dx x (fun g => ((ψ g : ℝ) : ℂ)) g := by
  funext g
  have h0 : crv x g 0 = g := by simp [crv]
  have hψc := hd_Dx x (dif (cd_ofReal hψ)) g
  set D := Dx x (fun g => ((ψ g : ℝ) : ℂ)) g with hDdef
  have hre : HasDerivAt (fun t => ψ (crv x g t)) D.re 0 := by
    have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hψc
    have hf : (⇑Complex.reCLM ∘ fun t => ((ψ (crv x g t) : ℝ) : ℂ)) = fun t => ψ (crv x g t) := by
      funext t; simp
    rw [hf] at this
    exact this.congr_deriv (by simp)
  have hD : D = (D.re : ℂ) := hψc.unique (by simpa using hre.ofReal_comp)
  have hit : HasDerivAt (iteratedDeriv q h) (iteratedDeriv (q + 1) h (ψ g)) (ψ (crv x g 0)) := by
    rw [h0, iteratedDeriv_succ]
    exact ((dif (cd_iter hh q)) (ψ g)).hasDerivAt
  have hcomp := (hit.comp (0 : ℝ) hre).ofReal_comp
  have hF := hd_Dx x (dif (cd_ofReal ((cd_iter hh q).comp hψ))) g
  have e1 : Dx x (fun g => ((iteratedDeriv q h (ψ g) : ℝ) : ℂ)) g
      = ((iteratedDeriv (q + 1) h (ψ g) * D.re : ℝ) : ℂ) := hF.unique hcomp
  rw [e1, Complex.ofReal_mul, ← hD]

private lemma Dw_append_singleton (w : List (Bool × Mat k r)) (x : Bool × Mat k r) (f : Mat k r → ℂ) :
    Dw (w ++ [x]) f = Dw w (Dx x f) := by
  unfold Dw
  rw [List.foldr_append]
  rfl

theorem main (ψ : Mat k r → ℝ) (h : ℝ → ℝ) (cost : Mat k r → ℕ) (n : ℕ) (C₀ : ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hh : ContDiff ℝ ∞ h) (hb : ∀ q : ℕ, ∃ c : ℝ, ∀ x, ‖iteratedDeriv q h x‖ ≤ c)
    (H : ∀ w, admitted n w → w ≠ [] → ∀ g ∈ GV k r,
      ‖Dw w (fun g => ((ψ g : ℝ) : ℂ)) g‖ ≤ C₀ * gN g ^ cs cost w) :
    ∀ m q : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ w, admitted n w → w.length ≤ m → ∀ g ∈ GV k r,
      ‖Dw w (fun g => ((iteratedDeriv q h (ψ g) : ℝ) : ℂ)) g‖ ≤ K * gN g ^ cs cost w := by
  have hgN : ∀ g : Mat k r, 0 ≤ gN g := by
    intro g
    first
    | (unfold gN; positivity)
    | (simp only [gN]; positivity)
  intro m
  induction m with
  | zero =>
    intro q
    obtain ⟨c, hc⟩ := hb q
    refine ⟨max c 0, le_max_right _ _, fun w _ hw g _ => ?_⟩
    have : w = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hw)
    subst this
    simp only [Dw, List.foldr_nil, cs, List.map_nil, List.sum_nil, pow_zero, mul_one, Complex.norm_real]
    exact (hc _).trans (le_max_left _ _)
  | succ m ih =>
    intro q
    obtain ⟨K₁, hK₁, h₁⟩ := ih q
    obtain ⟨K₂, hK₂, h₂⟩ := ih (q + 1)
    refine ⟨max K₁ (2 ^ m * (K₂ * max C₀ 0)), le_max_of_le_left hK₁, fun w hw hlen g hg => ?_⟩
    rcases Nat.lt_or_ge w.length (m + 1) with hlt | hge
    · exact (h₁ w hw (by omega) g hg).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (hgN g) _))
    · obtain ⟨w', x, rfl⟩ : ∃ w' x, w = w' ++ [x] := by
        rcases List.eq_nil_or_concat w with h0 | ⟨w', x, hx⟩
        · subst h0; simp at hge
        · exact ⟨w', x, by rw [hx, List.concat_eq_append]⟩
      have hlen' : w'.length = m := by simp at hlen hge; omega
      rw [Dw_append_singleton, chain x hψ hh q]
      have hyp : ∀ w₁ w₂, Spl w' w₁ w₂ →
          ‖Dw w₁ (fun g => ((iteratedDeriv (q + 1) h (ψ g) : ℝ) : ℂ)) g‖ *
            ‖Dw w₂ (Dx x fun g => ((ψ g : ℝ) : ℂ)) g‖ ≤ K₂ * max C₀ 0 * gN g ^ cs cost (w' ++ [x]) := by
        rintro w₁ w₂ ⟨s1, s2, hp⟩
        have hA1 : admitted n w₁ := Adm_sub (s1.trans (List.sublist_append_left _ _)) hw
        have hA2 : admitted n (w₂ ++ [x]) := Adm_sub (s2.append (List.Sublist.refl _)) hw
        have hl1 : w₁.length ≤ m := by have := s1.length_le; omega
        have e1 := h₂ w₁ hA1 hl1 g hg
        have e2 := H (w₂ ++ [x]) hA2 (by simp) g hg
        rw [Dw_append_singleton] at e2
        have hcs : cs cost w₁ + cs cost (w₂ ++ [x]) = cs cost (w' ++ [x]) := by
          rw [← cs_append]
          exact cs_perm cost (by rw [← List.append_assoc]; exact hp.append_right [x])
        calc _ ≤ (K₂ * gN g ^ cs cost w₁) * (max C₀ 0 * gN g ^ cs cost (w₂ ++ [x])) :=
              mul_le_mul e1 (e2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
                (pow_nonneg (hgN g) _))) (norm_nonneg _) (mul_nonneg hK₂ (pow_nonneg (hgN g) _))
          _ = K₂ * max C₀ 0 * gN g ^ cs cost (w' ++ [x]) := by rw [← hcs, pow_add]; ring
      have hM := leibB g (K₂ * max C₀ 0 * gN g ^ cs cost (w' ++ [x])) w'
        (fun g => ((iteratedDeriv (q + 1) h (ψ g) : ℝ) : ℂ)) (Dx x fun g => ((ψ g : ℝ) : ℂ))
        (cd_ofReal ((cd_iter hh (q + 1)).comp hψ)) (cd_Dx x (cd_ofReal hψ)) hyp
      calc _ ≤ 2 ^ w'.length * (K₂ * max C₀ 0 * gN g ^ cs cost (w' ++ [x])) := hM
        _ = (2 ^ m * (K₂ * max C₀ 0)) * gN g ^ cs cost (w' ++ [x]) := by rw [hlen']; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (hgN g) _)

end PI.UnitaryCorollaryDerivatives.CRH
end
end
