module

public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle002
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle011
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BlockValuationZpOfValuationBound
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle006
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle010
import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle005
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RatioConditionOfSegFacts
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle014
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
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle007

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

section Inst

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

def RestValNum : Prop :=
  ∀ aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA), ∀ aPlus ∈ X.winA,
    ∀ b, Kept X.p X.r (X.S C0 CE1 CE2) aTop b →
      ∀ l ∈ levels (gB C0 CE1 CE2 X aTop aPlus b),
        ∀ (j' : Fin (gB C0 CE1 CE2 X aTop aPlus b).T.t → ℕ) (jp' : ℕ), (gB C0 CE1 CE2 X aTop aPlus b).LevelOK j' jp' →
        ∀ μ : Formalism.GM.M.BVar (2 * X.s + 1) X.r (gB C0 CE1 CE2 X aTop aPlus b).T.t →₀ ℕ,
          (∀ a, Finsupp.weight (wL (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) a) μ =
            dLvl (gB C0 CE1 CE2 X aTop aPlus b) j' jp' a) →
          (padicValNat X.p (lvC (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) l.1 l.2 *
              degFact (gB C0 CE1 CE2 X aTop aPlus b) l.1 l.2) : ℝ) +
            2 * (expU X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) (aBig X) : ℝ) ≤
          (padicValNat X.p (μ.prod fun _ k => k.factorial) : ℝ) + levelPassageLoss X

theorem restVal_of_num (h : RestValNum C0 CE1 CE2 X) : RestVal C0 CE1 CE2 X := by
  intro aTop hT aPlus hP b hK l hl z hz μ hμ
  obtain ⟨j', jp', hl', hw⟩ := SSZ_support X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) z hz μ hμ
  exact h aTop hT aPlus hP b hK l hl j' jp' hl' μ hw

theorem block_valuation_Zp_of_numeric_bound {CYb Cde Ck CD Cb Cc : ℝ} (hCYb : 1 ≤ CYb) (hCE1 : 0 ≤ CE1) (hCE2 : 0 ≤ CE2)
    (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X) (hV : RestValNum C0 CE1 CE2 X) : BlockBoundIntegers C0 CE1 CE2 X :=
  block_valuation_Zp_of_valuation_bound C0 CE1 CE2 X hCYb hCE1 hCE2 hH (restVal_of_num C0 CE1 CE2 X hV)

end Inst

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

theorem thr_mono_seg {P Q : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop}
    (h : ∀ C0 CYb Cde Ck CD Cb CE1 CE2 Cc, 2 ≤ CYb → 0 ≤ CD → 1 ≤ Cb → 0 ≤ CE1 → 0 ≤ CE2 →
      P C0 CYb Cde Ck CD Cb CE1 CE2 Cc → Q C0 CYb Cde Ck CD Cb CE1 CE2 Cc)
    (hP : TransportedAlt P) : TransportedAlt Q := by
  intro Cc hCc
  obtain ⟨T0, hT0, h0⟩ := hP Cc hCc
  refine ⟨T0, hT0, fun C0 hC0 => ?_⟩
  obtain ⟨T1, hT1, h1⟩ := h0 C0 hC0
  refine ⟨T1, hT1, fun CE1 CE2 a1 a2 => ?_⟩
  obtain ⟨T2, hT2, h2⟩ := h1 CE1 CE2 a1 a2
  refine ⟨max T2 2, lt_max_of_lt_left hT2, fun CYb Cde Ck CD Cb b1 b2 b3 b4 b5 => ?_⟩
  have m1 := le_max_left T2 2
  have m2 := le_max_right T2 2
  exact h _ _ _ _ _ _ _ _ _ (m2.trans b1) (by linarith) (by linarith) (by linarith) (by linarith)
    (h2 CYb Cde Ck CD Cb (m1.trans b1) (m1.trans b2) (m1.trans b3) (m1.trans b4) (m1.trans b5))

def RestOpen (C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM : ℝ) (X : flipOneThree.Inst) : Prop :=
  flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X →
    BlockBoundUniformiser C0 CE1 CE2 X ∧ RestPlus C0 CE1 CE2 X CM ∧ RestTM C0 CE1 CE2 X CM ∧ RestDir C0 CE1 CE2 X

def RestOpenE (D : Formalism.BasicNotions.D7) : Prop :=
  TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc => ∀ Ckap Cs : ℝ, ∃ CM : ℝ, 0 ≤ CM ∧
    ∀ X : flipOneThree.Inst, AdmNoK D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs X → RestOpen C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM X

theorem restAllE_of_open (D : Formalism.BasicNotions.D7) (h : RestOpenE D) : RestAllE D :=
  thr_mono_seg (fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc hY hD hb h1 h2 hP Ckap Cs => by
    obtain ⟨CM, hCM, hX⟩ := hP Ckap Cs
    have he : (0 : ℝ) < Real.exp 3 := Real.exp_pos 3
    refine ⟨CM, max (2 * ((30 + CM) * Real.exp 3 + 5) * Real.exp 3) (18 * (1 + CM) + 20), hCM,
      le_max_of_le_right (by linarith), le_max_left _ _, fun X hA hH => ?_⟩
    obtain ⟨a, b, c, d⟩ := hX X hA hH
    have hS := segFacts hY hb hD h1 h2 hH
    exact ⟨a, b, c, d, restFree_proved hS, ratioCondition_of_segFacts hS,
      restDepth_proved CM _ (by linarith) hCM (le_max_right _ _) hH⟩) h

theorem closed_of_open_conditions (D : Formalism.BasicNotions.D7) (h : RestOpenE D) : IntegralityFromMetricForLargeConstants D :=
  theorem_A_closed_of_all_remaining_bounds D (restAllE_of_open D h)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

theorem restTM_of (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst) {CYb Cde Ck CD Cb Cc : ℝ} (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X)
    (D : Formalism.BasicNotions.D7) (hM : ∀ XM : flipOneThree.InstM, ModelLatticeRank D XM) (hF : RestFree C0 CE1 CE2 X)
    (hS : RestTMSize C0 CE1 CE2 X) (hE : RestTMEps C0 CE1 CE2 X 1) : RestTM C0 CE1 CE2 X 1 :=
  restTM_of_rests D hM hF (restTMHyp_of hH hS) hE

theorem restTM_exists : ∃ CM : ℝ, 1 ≤ CM ∧ ∀ (_D : Formalism.BasicNotions.D7) (C0 CE1 CE2 CYb Cde Ck CD Cb Cc : ℝ) (X : flipOneThree.Inst),
    flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X → RestFree C0 CE1 CE2 X → RestTMSize C0 CE1 CE2 X →
      RestTMEps C0 CE1 CE2 X CM → RestTM C0 CE1 CE2 X CM := by
  exact ⟨1, le_rfl, fun D C0 CE1 CE2 CYb Cde Ck CD Cb Cc X hH hF hS hE =>
    restTM_of C0 CE1 CE2 X hH D (alternative_mean_value_theorem D) hF hS hE⟩

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end
