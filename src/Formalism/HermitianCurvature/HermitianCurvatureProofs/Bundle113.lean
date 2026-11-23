module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle108
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle109
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliWordSumExpansion
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ContDiffHerm
public import Formalism.HermitianCurvature.StatementD
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BaseIndexConstantInjective
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle110
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.BetaSesquilinearity
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.LT

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section op

variable {k r : ℕ} {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']

theorem coefLeib {O UU : Set (B.Mat k r)} (hO : IsOpen O) (hcov : ∀ g ∈ B.GV k r, g ∈ O ∨ g ∈ UU)
    {a : B.Mat k r → (E →L[ℂ] E')} {Φ : B.Mat k r → E} {d Bg A : ℝ} (hBg : 0 ≤ Bg)
    (ha : B.CkOn ⊤ UU a)
    (hab : ∀ m : ℕ, ∃ C : ℝ, ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ v, B.unitLie k r X) →
      u.length + v.length ≤ m → ∀ g ∈ B.GV k r, g ∉ O → ‖B.dLR u v a g‖ ≤ C * B.gN g ^ (d + Bg * m))
    (hΦ : B.CkOn ⊤ (B.GV k r) Φ) (hΦg : ∀ m : ℕ, B.InCC (A - Bg * m) m Φ)
    (hz : ∀ g ∈ B.GV k r, g ∈ O → Φ g = 0) :
    B.CkOn ⊤ (B.GV k r) (ap a Φ) ∧ ∀ n : ℕ, B.InCC (A - d - Bg * n) n (ap a Φ) := by
  have hP : Pr O UU ⊤ a Φ := ⟨ha, hΦ, hz⟩
  refine ⟨hP.ck hO hcov, fun n => ?_⟩
  choose Ca hCa using hab
  choose cF hcF using hΦg
  set Ka : ℝ := ∑ j ∈ Finset.range (n + 1), |Ca j| with hKa
  set K : ℝ := ∑ j ∈ Finset.range (n + 1), |cF j| with hK
  have hKaj : ∀ j ≤ n, |Ca j| ≤ Ka := fun j hj =>
    Finset.single_le_sum (f := fun j => |Ca j|) (fun i _ => abs_nonneg _)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
  have hKj : ∀ j ≤ n, |cF j| ≤ K := fun j hj =>
    Finset.single_le_sum (f := fun j => |cF j|) (fun i _ => abs_nonneg _)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
  have hKa0 : 0 ≤ Ka := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hCK : 0 ≤ Ka * K := mul_nonneg hKa0 hK0
  refine ⟨2 ^ n * (Ka * K), sCkOn_mono le_top (hP.ck hO hcov), fun u v hu hv hl g hg => ?_⟩
  have hlie := lie_LR (unit_lie hu) (unit_lie hv)
  have hw : (wL u ++ wR v).length = u.length + v.length := len_LR u v
  have hP' : Pr O UU ((wL u ++ wR v).length : ℕ) a Φ := hP.mono le_top
  have hp := gN_pos hg
  have hg1 := gN_ge_one hg
  rw [dLR_eq]
  by_cases hgO : g ∈ O
  · rw [Dw_vanish hO hlie (hP'.mono zero_le).apz g hg hgO]
    simp only [norm_zero, mul_zero]
    exact mul_nonneg (by positivity) hCK
  · have hb := leib_bound hO hcov g hg (Ka * K * B.gN g ^ (d + Bg * (((wL u ++ wR v).length : ℕ) : ℝ) - A))
      (wL u ++ wR v) a Φ hlie hP' (by
        intro w₁ w₂ hs₁ hs₂ hl₁₂
        obtain ⟨u₁, v₁, hu₁, hv₁, rfl⟩ := sub_LR hs₁
        obtain ⟨u₂, v₂, hu₂, hv₂, rfl⟩ := sub_LR hs₂
        rw [len_LR, len_LR] at hl₁₂
        have hl₁ : u₁.length + v₁.length ≤ n := by
          have := hu₁.length_le; have := hv₁.length_le; omega
        have hl₂ : u₂.length + v₂.length ≤ n := by
          have := hu₂.length_le; have := hv₂.length_le; omega
        have hu₁' : ∀ X ∈ u₁, B.unitLie k r X := fun X hX => hu X (hu₁.subset hX)
        have hv₁' : ∀ X ∈ v₁, B.unitLie k r X := fun X hX => hv X (hv₁.subset hX)
        have hu₂' : ∀ X ∈ u₂, B.unitLie k r X := fun X hX => hu X (hu₂.subset hX)
        have hv₂' : ∀ X ∈ v₂, B.unitLie k r X := fun X hX => hv X (hv₂.subset hX)
        set L₁ : ℝ := ((u₁.length + v₁.length : ℕ) : ℝ) with hL₁
        set L₂ : ℝ := ((u₂.length + v₂.length : ℕ) : ℝ) with hL₂
        have b1 : ‖Dw (wL u₁ ++ wR v₁) a g‖ ≤ Ka * B.gN g ^ (d + Bg * L₁) := by
          rw [← dLR_eq]
          have h1 := hCa (u₁.length + v₁.length) u₁ v₁ hu₁' hv₁' le_rfl g hg hgO
          calc _ ≤ Ca (u₁.length + v₁.length) * B.gN g ^ (d + Bg * L₁) := by rw [hL₁]; exact h1
            _ ≤ |Ca (u₁.length + v₁.length)| * B.gN g ^ (d + Bg * L₁) :=
              mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg hp.le _)
            _ ≤ Ka * B.gN g ^ (d + Bg * L₁) :=
              mul_le_mul_of_nonneg_right (hKaj _ hl₁) (Real.rpow_nonneg hp.le _)
        have b2 : ‖Dw (wL u₂ ++ wR v₂) Φ g‖ ≤ K * B.gN g ^ (Bg * L₂ - A) := by
          rw [← dLR_eq]
          have h1 := (hcF (u₂.length + v₂.length)).2 u₂ v₂ hu₂' hv₂' le_rfl g hg
          have e : B.gN g ^ (Bg * L₂ - A) * B.gN g ^ (A - Bg * L₂) = 1 := by
            rw [← Real.rpow_add hp]; simp
          have h4 : ‖B.dLR u₂ v₂ Φ g‖ =
              B.gN g ^ (Bg * L₂ - A) * (B.gN g ^ (A - Bg * L₂) * ‖B.dLR u₂ v₂ Φ g‖) := by
            rw [← mul_assoc, e, one_mul]
          rw [h4]
          have h5 : B.gN g ^ (A - Bg * L₂) * ‖B.dLR u₂ v₂ Φ g‖ ≤ K := by
            refine le_trans ?_ (hKj _ hl₂)
            refine le_trans ?_ (le_abs_self _)
            simpa [hL₂] using h1
          calc _ ≤ B.gN g ^ (Bg * L₂ - A) * K := mul_le_mul_of_nonneg_left h5 (Real.rpow_nonneg hp.le _)
            _ = K * B.gN g ^ (Bg * L₂ - A) := mul_comm _ _
        have hsum : (d + Bg * L₁) + (Bg * L₂ - A) = d + Bg * (((wL u ++ wR v).length : ℕ) : ℝ) - A := by
          rw [← hl₁₂, hL₁, hL₂]; push_cast; ring
        calc ‖Dw (wL u₁ ++ wR v₁) a g‖ * ‖Dw (wL u₂ ++ wR v₂) Φ g‖
            ≤ (Ka * B.gN g ^ (d + Bg * L₁)) * (K * B.gN g ^ (Bg * L₂ - A)) :=
              mul_le_mul b1 b2 (norm_nonneg _) (mul_nonneg hKa0 (Real.rpow_nonneg hp.le _))
          _ = Ka * K * (B.gN g ^ (d + Bg * L₁) * B.gN g ^ (Bg * L₂ - A)) := by ring
          _ = Ka * K * B.gN g ^ (d + Bg * (((wL u ++ wR v).length : ℕ) : ℝ) - A) := by
              rw [← Real.rpow_add hp, hsum])
    have hlen : ((wL u ++ wR v).length : ℕ) ≤ n := by rw [hw]; exact hl
    have e2 : B.gN g ^ (A - d - Bg * n) * B.gN g ^ (d + Bg * (((wL u ++ wR v).length : ℕ) : ℝ) - A) ≤ 1 := by
      rw [← Real.rpow_add hp]
      refine Real.rpow_le_one_of_one_le_of_nonpos hg1 ?_
      have h6 : (((wL u ++ wR v).length : ℕ) : ℝ) ≤ n := by exact_mod_cast hlen
      nlinarith [mul_le_mul_of_nonneg_left h6 hBg]
    have e3 : (2 : ℝ) ^ (wL u ++ wR v).length ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hlen
    calc B.gN g ^ (A - d - Bg * n) * ‖Dw (wL u ++ wR v) (ap a Φ) g‖
        ≤ B.gN g ^ (A - d - Bg * n) * (2 ^ (wL u ++ wR v).length *
            (Ka * K * B.gN g ^ (d + Bg * (((wL u ++ wR v).length : ℕ) : ℝ) - A))) :=
          mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hp.le _)
      _ = 2 ^ (wL u ++ wR v).length * (Ka * K) *
            (B.gN g ^ (A - d - Bg * n) * B.gN g ^ (d + Bg * (((wL u ++ wR v).length : ℕ) : ℝ) - A)) := by ring
      _ ≤ 2 ^ (wL u ++ wR v).length * (Ka * K) * 1 :=
          mul_le_mul_of_nonneg_left e2 (mul_nonneg (by positivity) hCK)
      _ ≤ 2 ^ n * (Ka * K) := by rw [mul_one]; exact mul_le_mul_of_nonneg_right e3 hCK

theorem rwG {w : List (B.Mat k r)} (hw : ∀ X ∈ w, B.inLie k r X) {Φ : B.Mat k r → E} {A Bg : ℝ}
    (hΦ : B.CkOn ⊤ (B.GV k r) Φ) (hΦg : ∀ m : ℕ, B.InCC (A - Bg * m) m Φ) :
    B.CkOn ⊤ (B.GV k r) (B.Rw w Φ) ∧ ∀ m : ℕ, B.InCC (A - Bg * w.length - Bg * m) m (B.Rw w Φ) := by
  refine ⟨?_, fun m => ?_⟩
  · rw [← Dw_wR]
    apply CkOn_Dw (fun x hx => lie_LR (u := []) (by simp) hw x (by simpa [wL] using hx))
    simpa using hΦ
  · have h := InCC_Rw (m := m) hw (hΦg (m + w.length))
    have e : A - Bg * ((m + w.length : ℕ) : ℝ) = A - Bg * w.length - Bg * m := by push_cast; ring
    rwa [e] at h

theorem listSumG {ι : Type*} (l : List ι) (f : ι → B.Mat k r → E) {A Bg : ℝ}
    (h : ∀ i ∈ l, B.CkOn ⊤ (B.GV k r) (f i) ∧ ∀ m : ℕ, B.InCC (A - Bg * m) m (f i)) :
    B.CkOn ⊤ (B.GV k r) (fun g => (l.map fun i => f i g).sum) ∧
      ∀ m : ℕ, B.InCC (A - Bg * m) m (fun g => (l.map fun i => f i g).sum) := by
  induction l with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    exact ⟨CkOn_zero, fun m => ⟨0, CCle_zero⟩⟩
  | cons i l ih =>
    have hi := h i (by simp)
    have hl := ih (fun j hj => h j (by simp [hj]))
    simp only [List.map_cons, List.sum_cons]
    refine ⟨CkOn_add hi.1 hl.1, fun m => ?_⟩
    obtain ⟨c, hc⟩ := hi.2 m
    obtain ⟨c', hc'⟩ := hl.2 m
    exact ⟨c + c', CCle_add hc hc'⟩

end op

theorem operator_in_class_holds : OpCCg := by
  intro k r Wp Wq _ _ _ _ _ _ Bs Θ d Bg A η F hη hBg hSC hCG hF hFg hz
  set O : Set (B.Mat k r) := {g | Gf k r Bs.z Bs.z' g < η} with hOdef
  have hO : IsOpen O := isOpen_lt (Gf_cont _ _) continuous_const
  have hcov : ∀ g ∈ B.GV k r, g ∈ O ∨ g ∈ B.GPos Bs := by
    intro g hg
    by_cases h : Gf k r Bs.z Bs.z' g < η
    · exact Or.inl h
    · exact Or.inr ⟨hg, lt_of_lt_of_le hη (not_lt.1 h)⟩
  have hzO : ∀ g ∈ B.GV k r, g ∈ O → F g = 0 := fun g hg h => hz g hg h
  have hoff : ∀ g, g ∉ O → η ≤ Gf k r Bs.z Bs.z' g := fun g h => not_lt.1 h
  have hab1 : ∀ T ∈ Θ, ∀ m : ℕ, ∃ C : ℝ, ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) →
      (∀ X ∈ v, B.unitLie k r X) → u.length + v.length ≤ m → ∀ g ∈ B.GV k r, g ∉ O →
        ‖B.dLR u v T.coef g‖ ≤ C * B.gN g ^ (d + Bg * m) := by
    intro T hT m
    obtain ⟨C, hC⟩ := hCG T hT η hη m
    exact ⟨C, fun u v hu hv hl g hg hgO => (hC u v hu hv hl g hg (hoff g hgO)).1⟩
  have hab2 : ∀ T ∈ Θ, ∀ m : ℕ, ∃ C : ℝ, ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) →
      (∀ X ∈ v, B.unitLie k r X) → u.length + v.length ≤ m → ∀ g ∈ B.GV k r, g ∉ O →
        ‖B.dLR u v T.coefAdj g‖ ≤ C * B.gN g ^ (d + Bg * m) := by
    intro T hT m
    obtain ⟨C, hC⟩ := hCG T hT η hη m
    exact ⟨C, fun u v hu hv hl g hg hgO => (hC u v hu hv hl g hg (hoff g hgO)).2⟩
  have hApp : ∀ T ∈ Θ, B.CkOn ⊤ (B.GV k r) (ap T.coef (B.Rw T.word F)) ∧
      ∀ m : ℕ, B.InCC (A - d - Bg * (B.opOrder Θ : ℝ) - Bg * m) m (ap T.coef (B.Rw T.word F)) := by
    intro T hT
    have hR := rwG T.word_lie hF hFg
    have hzR : ∀ g ∈ B.GV k r, g ∈ O → B.Rw T.word F g = 0 := Rw_vanish hO T.word_lie hzO
    have hc := coefLeib hO hcov hBg (hSC T hT).1 (hab1 T hT) hR.1 hR.2 hzR
    have hlen : (T.word.length : ℝ) ≤ (B.opOrder Θ : ℝ) := by
      exact_mod_cast Formalism.FourierDecayAlt.P.B5.len_le_order Θ hT
    refine ⟨hc.1, fun m => sInCC_mono ?_ le_rfl (hc.2 m)⟩
    nlinarith [mul_le_mul_of_nonneg_left hlen hBg]
  have hAdj : ∀ T ∈ Θ, B.CkOn ⊤ (B.GV k r)
        (fun g => ((-1 : ℂ) ^ T.word.length) • B.Rw T.word.reverse (fun x => T.coefAdj x (F x)) g) ∧
      ∀ m : ℕ, B.InCC (A - d - Bg * (B.opOrder Θ : ℝ) - Bg * m) m
        (fun g => ((-1 : ℂ) ^ T.word.length) • B.Rw T.word.reverse (fun x => T.coefAdj x (F x)) g) := by
    intro T hT
    have hc := coefLeib hO hcov hBg (hSC T hT).2 (hab2 T hT) hF hFg hzO
    have hR := rwG (w := T.word.reverse) (fun X hX => T.word_lie X (List.mem_reverse.1 hX)) hc.1 hc.2
    have hlen : (T.word.length : ℝ) ≤ (B.opOrder Θ : ℝ) := by
      exact_mod_cast Formalism.FourierDecayAlt.P.B5.len_le_order Θ hT
    refine ⟨CkOn_smul _ hR.1, fun m => ?_⟩
    have h2 := hR.2 m
    rw [List.length_reverse] at h2
    obtain ⟨c, hcc⟩ := sInCC_mono (A := A - d - Bg * (B.opOrder Θ : ℝ) - Bg * m) (by
      nlinarith [mul_le_mul_of_nonneg_left hlen hBg]) le_rfl h2
    exact ⟨_, CCle_smul _ hcc⟩
  exact ⟨listSumG Θ (fun T => ap T.coef (B.Rw T.word F)) hApp,
    listSumG Θ (fun T g => ((-1 : ℂ) ^ T.word.length) • B.Rw T.word.reverse (fun x => T.coefAdj x (F x)) g) hAdj⟩

end Formalism.FourierDecayAlt.P.CutMP.JA.LT

end
end

section

open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.GaugeNormPower

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.CapelliWordSumExpansion

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section closed

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem aa_closed (P : (Mat k r → E) → Prop)
    (hRd : ∀ (X : Mat k r) (f : Mat k r → E), inLie k r X → P f → P (RdV X f))
    (hadd : ∀ f₁ f₂ : Mat k r → E, P f₁ → P f₂ → P (fun x => f₁ x + f₂ x))
    (hmul : ∀ (φ : Mat k r → ℂ), ContDiff ℝ (⊤ : ℕ∞) φ → ∀ f : Mat k r → E, P f → P (fun x => φ x • f x))
    (hzero : P (fun _ => 0)) (m : ℕ) (hm : m ≤ r) (u : ℂ) (f : Mat k r → E) (hf : P f) :
    P (C3.AAop k r m hm u f) :=
  _root_.UpperTheory.Reformulated.B.Qj20.aa_closed P hRd hadd hmul hzero m hm u f hf

theorem loc_add' {m : ℕ∞} {f₁ f₂ : Mat k r → E} {g : Mat k r} (h₁ : Loc m f₁ g) (h₂ : Loc m f₂ g) :
    Loc m (fun x => f₁ x + f₂ x) g := by
  obtain ⟨U₁, f₁', hU₁, hg₁, hf₁, he₁⟩ := h₁
  obtain ⟨U₂, f₂', hU₂, hg₂, hf₂, he₂⟩ := h₂
  exact ⟨U₁ ∩ U₂, fun x => f₁' x + f₂' x, hU₁.inter hU₂, ⟨hg₁, hg₂⟩,
    (hf₁.mono Set.inter_subset_left).add (hf₂.mono Set.inter_subset_right),
    fun x hx hxG => by show f₁ x + f₂ x = f₁' x + f₂' x; rw [he₁ x hx.1 hxG, he₂ x hx.2 hxG]⟩

theorem loc_smulFun {m : ℕ∞} (φ : Mat k r → ℂ) {V : Set (Mat k r)} (hV : IsOpen V)
    (hφ : ContDiffOn ℝ (m : WithTop ℕ∞) φ V) {f : Mat k r → E} {g : Mat k r} (hgV : g ∈ V) (h : Loc m f g) :
    Loc m (fun x => φ x • f x) g := by
  obtain ⟨U, f', hU, hgU, hf, he⟩ := h
  exact ⟨U ∩ V, fun x => φ x • f' x, hU.inter hV, ⟨hgU, hgV⟩,
    (hφ.mono Set.inter_subset_right).smul (hf.mono Set.inter_subset_left),
    fun x hx hxG => by show φ x • f x = φ x • f' x; rw [he x hx.1 hxG]⟩

theorem loc_zero' {m : ℕ∞} {g : Mat k r} : Loc m (fun _ => (0 : E)) g :=
  ⟨Set.univ, fun _ => 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩

theorem loc_AAop {f : Mat k r → E} {g : Mat k r} (h : Loc ⊤ f g) (m : ℕ) (hm : m ≤ r) (u : ℂ) :
    Loc ⊤ (C3.AAop k r m hm u f) g := by
  refine aa_closed (fun f => Loc ⊤ f g) (fun X f hX hf => ?_) (fun _ _ h₁ h₂ => loc_add' h₁ h₂)
    (fun φ hφ f hf => loc_smulFun φ isOpen_univ hφ.contDiffOn (Set.mem_univ g) hf) loc_zero' m hm u f h
  have hf' : Loc ((⊤ : ℕ∞) + 1) f g := by rw [top_add]; exact hf
  exact loc_RdV hX hf'

theorem zero_AAop {f : Mat k r → E} {U : Set (Mat k r)} (hU : IsOpen U) (h : ∀ x ∈ U, x ∈ GV k r → f x = 0)
    (m : ℕ) (hm : m ≤ r) (u : ℂ) : ∀ x ∈ U, x ∈ GV k r → C3.AAop k r m hm u f x = 0 := by
  refine aa_closed (fun f => ∀ x ∈ U, x ∈ GV k r → f x = 0) (fun X f hX hf => ?_)
    (fun f₁ f₂ h₁ h₂ x hx hxG => by simp [h₁ x hx hxG, h₂ x hx hxG])
    (fun φ _ f hf x hx hxG => by simp [hf x hx hxG]) (fun _ _ _ => rfl) m hm u f h
  intro x hx hxG
  rw [rdV_congr (f₂ := fun _ => (0 : E)) hU hx hxG hX (fun y hy hyG => hf y hy hyG)]
  simp [RdV]

end closed

end Formalism.FourierDecayAlt.P.GaugeNormPower

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.GaugeNormPower

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem raising_compact_support : PBN.AACpt := by
  intro k r Wp Wq _ _ _ _ Bs F y hF
  obtain ⟨hs, ⟨R, hR⟩, ⟨ε, hε, hG⟩⟩ := hF
  have hGc : Continuous fun g : Mat k r => Gf k r Bs.z Bs.z' g :=
    (Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf Bs.z Bs.z').continuous
  have hvan : ∀ U : Set (Mat k r), IsOpen U → (∀ x ∈ U, x ∈ GV k r → F x = 0) →
      ∀ x ∈ U, x ∈ GV k r → PBN.aaTop Bs y F x = 0 := by
    intro U hU hF0 x hx hxG
    have := zero_AAop hU hF0 r le_rfl ((y : ℂ) + ((2 * r + k : ℕ) : ℂ) / 2) x hx hxG
    simp only [PBN.aaTop, this, smul_zero]
  have hUε : IsOpen {x : Mat k r | Gf k r Bs.z Bs.z' x < ε} := isOpen_lt hGc continuous_const
  have hFε : ∀ x ∈ {x : Mat k r | Gf k r Bs.z Bs.z' x < ε}, x ∈ GV k r → F x = 0 := by
    intro x hx hxG
    by_contra h
    exact absurd (hG x hxG h) (not_le.mpr hx)
  refine ⟨?_, ⟨R, ?_⟩, ⟨ε, hε, ?_⟩⟩
  · intro g₀ hg₀
    by_cases hlt : Gf k r Bs.z Bs.z' g₀ < ε
    · exact ⟨_, fun _ => 0, hUε, hlt, contDiffOn_const, fun x hx hxG => hvan _ hUε hFε x hx hxG⟩
    · push Not at hlt
      have hD : Dmin k r Bs.z Bs.z' g₀ (Fin.last (r + 1)) ≠ 0 := by
        intro h0
        have h1 : 0 ≤ Tz k r Bs.z * Tz k r Bs.z' * Complex.normSq (Dmin k r Bs.z Bs.z' g₀ ⟨r, by omega⟩) :=
          mul_nonneg (mul_pos Bs.T_pos Bs.T'_pos).le (Complex.normSq_nonneg _)
        simp only [Gf, h0, map_zero] at hlt
        linarith
      have hDc : ContDiff ℝ (⊤ : ℕ∞) fun x : Mat k r => Dmin k r Bs.z Bs.z' x (Fin.last (r + 1)) :=
        Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin Bs.z Bs.z' _
      have hV : IsOpen {x : Mat k r | Dmin k r Bs.z Bs.z' x (Fin.last (r + 1)) ≠ 0} :=
        isOpen_ne_fun hDc.continuous continuous_const
      have hloc : Loc ⊤ (C3.AAop k r r le_rfl ((y : ℂ) + ((2 * r + k : ℕ) : ℂ) / 2) F) g₀ :=
        loc_AAop (hs g₀ hg₀) r le_rfl _
      exact loc_smulFun (fun x => (Dmin k r Bs.z Bs.z' x (Fin.last (r + 1)))⁻¹) hV
        (hDc.contDiffOn.inv fun x hx => hx) hD hloc
  · intro g hg hne
    by_contra hgt
    push Not at hgt
    have hU : IsOpen {x : Mat k r | R < gN x} := isOpen_lt continuous_const Formalism.FourierDecayAlt.P.B6.gN_continuous
    refine hne (hvan _ hU (fun x hx hxG => ?_) g hgt hg)
    by_contra h
    exact absurd (hR x hxG h) (not_le.mpr hx)
  · intro g hg hne
    by_contra hlt
    push Not at hlt
    exact hne (hvan _ hUε hFε g hlt hg)

end Formalism.FourierDecayAlt.P
end
end

section

open Matrix Finset MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBG

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section supp

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem qminorOp_zero {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) :
    qminorOp (Q.EH k r) a b u (fun _ : Q.Mx k r => (0 : E)) = fun _ => 0 := by
  have htop : ∀ (v : ℂ) (p q : Fin (2 * r + k + 1)),
      QuantumDeterminants.Top (Q.EH k r) v p q (fun _ : Q.Mx k r => (0 : E)) = fun _ => 0 := by
    intro v p q
    funext x
    simp only [QuantumDeterminants.Top, smul_zero, ite_self, zero_add]
    exact eabH_zero p q x
  have hfold : ∀ L : List ((Q.Mx k r → E) → Q.Mx k r → E), (∀ T ∈ L, T (fun _ => 0) = fun _ => 0) →
      L.foldr (fun T h => T h) (fun _ : Q.Mx k r => (0 : E)) = fun _ => 0 := by
    intro L
    induction L with
    | nil => intro _; rfl
    | cons T L ih =>
      intro hT
      simp only [List.foldr_cons]
      rw [ih (fun T' h' => hT T' (by simp [h']))]
      exact hT T (by simp)
  funext x
  unfold qminorOp
  simp only [Finset.sum_apply, Pi.smul_apply]
  apply Finset.sum_eq_zero
  intro σ _
  rw [hfold _ (fun T hT => by
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hT
    exact htop _ _ _)]
  simp

theorem AAop_zero' (m : ℕ) (hm : m ≤ r) (u : ℂ) (g : Q.Mx k r) :
    C3.AAop k r m hm u (fun _ : Q.Mx k r => (0 : E)) g = 0 := by
  unfold C3.AAop
  apply Finset.sum_eq_zero
  intro c _
  split_ifs
  · rw [qminorOp_zero]; simp
  · rfl

theorem AAvop_zero' (m : ℕ) (hm : m ≤ r) (ell : ℂ) (g : Q.Mx k r) :
    C3.AAvop k r m hm ell (fun _ : Q.Mx k r => (0 : E)) g = 0 := by
  unfold C3.AAvop
  apply Finset.sum_eq_zero
  intro c _
  split_ifs
  · rw [qminorOp_zero]; simp
  · rfl

theorem vLet_zero_near (z z' : Fin (2 * r + k + 1) → ℂ) (j : ℕ) (hj : j ≤ r) (l : C.Letter) (e : Fin 2)
    (f : B.Mat k r → E) {V : Set (Q.Mx k r)} (hV : IsOpen V) (hf : ∀ x ∈ V, x ∈ B.GV k r → f x = 0)
    (g : B.Mat k r) (hg : g ∈ V) (hgG : g ∈ B.GV k r) : D.vLet k r z z' j hj l e f g = 0 := by
  have hgl : g ∈ Q.Glev k r 0 ∩ V := ⟨Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hgG, hg⟩
  have hloc : ∀ x ∈ Q.Glev k r 0 ∩ V, f x = (fun _ : Q.Mx k r => (0 : E)) x := fun x hx => hf x hx.2 hx.1.1
  unfold D.vLet
  split_ifs
  · rfl
  · rw [AAop_loc hV _ _ _ f _ hloc g hgl, AAop_zero', smul_zero]
  · rw [AAvop_loc hV _ _ _ f _ hloc g hgl, AAvop_zero', smul_zero]

theorem uwG_supp (z z' : Fin (2 * r + k + 1) → ℂ) (F : B.Mat k r → E) (R : ℝ)
    (hR : ∀ g ∈ B.GV k r, F g ≠ 0 → B.gN g ≤ R) (j : ℕ) (hj : j ≤ r) :
    ∀ (w : List C.Letter) (e : Wd.Ix (Fin w.length)), ∀ g ∈ B.GV k r,
      D.uwG k r z z' F j hj w e g ≠ 0 → B.gN g ≤ R
  | [], _, g, hg, hne => hR g hg hne
  | l :: w, e, g, hg, hne => by
    by_contra hgt
    push Not at hgt
    apply hne
    show D.vLet k r z z' j hj l (e 0) (D.uwG k r z z' F j hj w fun a => e a.succ) g = 0
    refine vLet_zero_near z z' j hj l (e 0) _ (V := {x | R < B.gN x})
      (isOpen_lt continuous_const Formalism.FourierDecayAlt.P.B6.gN_continuous) (fun x hx hxG => ?_) g hgt hg
    by_contra h0
    exact absurd (uwG_supp z z' F R hR j hj w _ x hxG h0) (not_le.2 hx)

theorem contOn_of_loc {f : B.Mat k r → E} {S : Set (B.Mat k r)}
    (h : ∀ x ∈ S, x ∈ B.GV k r → CapelliWordSumExpansion.Loc (⊤ : ℕ∞) f x) : ContinuousOn f {x | x ∈ B.GV k r ∧ x ∈ S} := by
  intro x hx
  obtain ⟨U, f', hU, hxU, hf', he⟩ := h x hx.2 hx.1
  have hc : ContinuousWithinAt f' {x | x ∈ B.GV k r ∧ x ∈ S} x :=
    ((hf'.continuousOn).continuousAt (hU.mem_nhds hxU)).continuousWithinAt
  refine hc.congr_of_eventuallyEq ?_ (he x hxU hx.1)
  filter_upwards [nhdsWithin_le_nhds (hU.mem_nhds hxU), self_mem_nhdsWithin] with y hyU hyS
  exact he y hyU hyS.1

end supp

end Formalism.FourierDecayAlt.P.PBG
end
end
