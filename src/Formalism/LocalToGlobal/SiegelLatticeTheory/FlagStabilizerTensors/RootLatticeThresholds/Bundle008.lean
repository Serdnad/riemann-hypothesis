module

public import Formalism.HermitianCurvature.StatementC
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.CuspSpanNormBounds.LocalModelPeriodLattices
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSecondOrder.SmoothClassInFiniteOrder
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.CarrierSz

theorem unram_host (D : D7) :
    haveI : IsCMField D.host.E := D.host.isCMField_hostE
    Formalism.FourierDecayAlt.S6.Unram D.host.E := by
  have : IsCMField D.host.E := D.host.isCMField_hostE
  exact Formalism.MainNotions.LocalModelPeriodLattices.unramE D

theorem g_pos (D : D7) : 0 < D.host.g 0 ∧ 0 < D.host.g 1 :=
  ⟨(D.host.g_prime 0).pos, (D.host.g_prime 1).pos⟩

section Cut

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]

end Cut

def ClCut (C₆ : ℝ) : ℝ := max 1 ((420 * C₆ + 48125) / 8)

section Grids

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Sz

def GridsAt (c : Cfg) (l N : ℕ) (grid : ℕ → Finset ℝ) (grid1 : Finset ℝ) : Prop :=
  6 * (N : ℝ) ^ 3 + 6 * N ≤ (c.Del / 2 - c.v l) - (5 / 2 - c.v l) ∧
  (∀ a, ∀ y ∈ grid a, 1 ≤ a ∧ a ≤ N ∧ C.gridL (5 / 2 - c.v l) (c.Del / 2 - c.v l) N a ≤ y ∧
      y ≤ C.gridL (5 / 2 - c.v l) (c.Del / 2 - c.v l) N a +
        ((c.Del / 2 - c.v l) - (5 / 2 - c.v l)) / (6 * N) - 1) ∧
  (∀ y ∈ grid1, y ∈ c.cutIntervalLong l N ∧ y + 1 ∈ c.cutIntervalLong l N) ∧
  (∀ y ∈ grid1, ∀ y' ∈ grid1, y ≠ y' → ∀ e ∈ ({0, 1} : Finset ℝ), ∀ e' ∈ ({0, 1} : Finset ℝ),
      (N : ℝ) ^ 2 / 8 ≤ |(y + e) - (y' + e')|) ∧
  (∀ y ∈ grid1, ∀ a, ∀ y' ∈ grid a, ∀ e ∈ ({0, 1} : Finset ℝ), ∀ e' ∈ ({0, 1} : Finset ℝ),
      (N : ℝ) ^ 2 + 1 ≤ |(y + e) - (y' + e')|) ∧
  (∀ y, ((∃ a, y ∈ grid a) ∨ y ∈ grid1) →
      y ∈ c.cutI l ∧ y + 1 ∈ c.cutI l ∧ c.P y ≠ 0 ∧ c.P (y + 1) ≠ 0)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]

theorem gridsOK_iff (S : C.HidaSetting E Wp Wq) :
    C.GridsOK S ↔ ∀ v, GridsAt (S.G.place (S.pl v)) S.l S.Ntop (S.grid v) (S.grid1 v) := Iff.rfl

theorem exists_good (c : Cfg) {A B : ℝ} (h : A < B) :
    ∃ y, A ≤ y ∧ y ≤ B ∧ c.P y ≠ 0 ∧ c.P (y + 1) ≠ 0 := by
  classical
  let bad : Finset ℝ := (Finset.Icc 1 (c.k + c.m - 1)).image (fun s => -c.lam s) ∪
    (Finset.Icc 1 (c.k + c.m - 1)).image (fun s => -c.lam s - 1)
  obtain ⟨y, hy, hyb⟩ := (Set.Icc_infinite h).exists_notMem_finset bad
  refine ⟨y, hy.1, hy.2, ?_, ?_⟩
  · intro h0
    unfold Cfg.P at h0
    obtain ⟨s, hs, hs0⟩ := Finset.prod_eq_zero_iff.mp h0
    exact hyb (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨s, hs, by linarith⟩))
  · intro h0
    unfold Cfg.P at h0
    obtain ⟨s, hs, hs0⟩ := Finset.prod_eq_zero_iff.mp h0
    exact hyb (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨s, hs, by linarith⟩))

def pickIn (c : Cfg) (A B : ℝ) : ℝ :=
  Classical.epsilon (fun y => A ≤ y ∧ y ≤ B ∧ c.P y ≠ 0 ∧ c.P (y + 1) ≠ 0)

theorem pickIn_spec (c : Cfg) {A B : ℝ} (h : A < B) :
    A ≤ pickIn c A B ∧ pickIn c A B ≤ B ∧ c.P (pickIn c A B) ≠ 0 ∧ c.P (pickIn c A B + 1) ≠ 0 :=
  Classical.epsilon_spec (exists_good c h)

def gridOf (c : Cfg) (l N : ℕ) (a : ℕ) : Finset ℝ :=
  if 1 ≤ a ∧ a ≤ N then
    {pickIn c (C.gridL (5 / 2 - c.v l) (c.Del / 2 - c.v l) N a)
      (C.gridL (5 / 2 - c.v l) (c.Del / 2 - c.v l) N a + ((c.Del / 2 - c.v l) - (5 / 2 - c.v l)) / (6 * N) - 1)}
  else ∅

def node1 (c : Cfg) (l N j : ℕ) : ℝ :=
  pickIn c (5 / 2 - c.v l + (j : ℝ) * (N : ℝ) ^ 2) (5 / 2 - c.v l + (j : ℝ) * (N : ℝ) ^ 2 + 1 / 2)

def grid1Of (c : Cfg) (l N : ℕ) : Finset ℝ := (Finset.range N).image (node1 c l N)

theorem first_level_node_spec (c : Cfg) (l N j : ℕ) :
    5 / 2 - c.v l + (j : ℝ) * (N : ℝ) ^ 2 ≤ node1 c l N j ∧
      node1 c l N j ≤ 5 / 2 - c.v l + (j : ℝ) * (N : ℝ) ^ 2 + 1 / 2 ∧
      c.P (node1 c l N j) ≠ 0 ∧ c.P (node1 c l N j + 1) ≠ 0 :=
  pickIn_spec c (by linarith)

theorem first_level_nodes_separated (c : Cfg) (l N : ℕ) {j j' : ℕ} (h : j < j') :
    (N : ℝ) ^ 2 - 1 / 2 ≤ node1 c l N j' - node1 c l N j := by
  have h1 := first_level_node_spec c l N j
  have h2 := first_level_node_spec c l N j'
  have hj : (j : ℝ) + 1 ≤ j' := by exact_mod_cast h
  have hN : 0 ≤ (N : ℝ) ^ 2 := by positivity
  nlinarith [h1.2.1, h2.1]

theorem grids_card (c : Cfg) (l N : ℕ) (hN : 1 ≤ N) :
    (grid1Of c l N).card = N ∧ ∀ a, 1 ≤ a → a ≤ N → (gridOf c l N a).card = 1 := by
  refine ⟨?_, fun a h1 h2 => by simp [gridOf, h1, h2]⟩
  unfold grid1Of
  rw [Finset.card_image_of_injective _ ?_, Finset.card_range]
  intro j j' h
  by_contra hne
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rcases Nat.lt_or_gt_of_ne hne with hl | hl
  · have := first_level_nodes_separated c l N hl; rw [h] at this; nlinarith
  · have := first_level_nodes_separated c l N hl; rw [h] at this; nlinarith

end Grids

section TransportedAlt

open Formalism.FourierDecayAlt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]

end TransportedAlt

end Formalism.L2.SG.Pf.CarrierSz
end
end

section

open Matrix Finset

noncomputable section

namespace Formalism.L2.SG.Pf.CoefDecay

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt PI.ComplexConjugateDerivative

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def CCw (k r : ℕ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (A : ℝ) (F : B.Mat k r → E) : Prop :=
  SS k r F ∧ ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ v, B.unitLie k r X) →
    ∃ C : ℝ, ∀ g ∈ B.GV k r, B.gN g ^ A * ‖B.dLR u v F g‖ ≤ C


open Classical in
def cstW {A : ℝ} {F : B.Mat k r → E} (hF : CCw k r A F) (u v : List (B.Mat k r)) : ℝ :=
  if h : (∀ X ∈ u, B.unitLie k r X) ∧ (∀ X ∈ v, B.unitLie k r X) then Classical.choose (hF.2 u v h.1 h.2) else 0

theorem cstW_spec {A : ℝ} {F : B.Mat k r → E} (hF : CCw k r A F) (u v : List (B.Mat k r))
    (hu : ∀ X ∈ u, B.unitLie k r X) (hv : ∀ X ∈ v, B.unitLie k r X) {g : B.Mat k r} (hg : g ∈ B.GV k r) :
    B.gN g ^ A * ‖B.dLR u v F g‖ ≤ cstW hF u v := by
  unfold cstW
  rw [dite_eq_left ⟨hu, hv⟩]
  exact Classical.choose_spec (hF.2 u v hu hv) g hg

def termW {N : ℕ} (e : Fin N → B.Mat k r) (K : ℝ) {A : ℝ} {F : B.Mat k r → E} (hF : CCw k r A F)
    (a b : ℕ) : ℝ :=
  K ^ (a + b) * bsum e (List.replicate a true ++ List.replicate b false)
    (fun β => max (cstW hF (β.take a) (β.drop a)) 0)

theorem inCC_of_CCw {A : ℝ} {F : B.Mat k r → E} (hF : CCw k r A F) (m : ℕ) :
    B.InCC (k := k) (r := r) A m F := by
  obtain ⟨N, e, c, K, hK, he, hc, hcK⟩ := basis_exists k r
  have he' : ∀ i, B.inLie k r (e i) := fun i => (he i).1
  have hgN : ∀ g : B.Mat k r, 0 ≤ B.gN g ^ A := fun g => Real.rpow_nonneg (Real.sqrt_nonneg _) A
  have hterm : ∀ a b, 0 ≤ termW e K hF a b := fun a b =>
    mul_nonneg (pow_nonneg hK _) (bsum_nonneg e _ _ fun β => le_max_right _ _)

  have hword : ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ v, B.unitLie k r X) →
      ∀ g ∈ B.GV k r, B.gN g ^ A * ‖B.dLR u v F g‖ ≤ termW e K hF u.length v.length := by
    intro u v hu hv g hg
    set ks := List.replicate u.length true ++ List.replicate v.length false with hks
    have hlen : (u ++ v).length = ks.length := by simp [hks]
    have hxs : ∀ X ∈ u ++ v, B.inLie k r X ∧ ∀ i, |c i X| ≤ K := by
      intro X hX
      have hX' : B.unitLie k r X := by
        rcases List.mem_append.1 hX with h | h
        · exact hu X h
        · exact hv X h
      exact ⟨hX'.1, hcK X hX'⟩
    have hexp := expand e c hK he' hc ks (u ++ v) hlen hxs id good_id F hF.1 g hg
    rw [B.dLR, ← B.dLR, dLR_eq_ev]
    have hl : (u ++ v).length = u.length + v.length := List.length_append
    rw [hl] at hexp
    calc B.gN g ^ A * ‖ev ks (u ++ v) F g‖
        ≤ B.gN g ^ A * (K ^ (u.length + v.length) * bsum e ks (fun β => ‖id (ev ks β F) g‖)) :=
          mul_le_mul_of_nonneg_left hexp (hgN g)
      _ = K ^ (u.length + v.length) * bsum e ks (fun β => B.gN g ^ A * ‖ev ks β F g‖) := by
          rw [bsum_mul]; simp only [id]; ring
      _ ≤ termW e K hF u.length v.length := by
          unfold termW
          refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hK _)
          refine bsum_mono e ks _ _ ?_
          intro β hβ hβe
          have hβl : β.length = u.length + v.length := by rw [hβ]; simp [hks]
          have h1 : (β.take u.length).length = u.length := by simp [List.length_take, hβl]
          have h2 : (β.drop u.length).length = v.length := by simp [List.length_drop, hβl]
          have hev : ev ks β F = B.dLR (β.take u.length) (β.drop u.length) F := by
            rw [dLR_eq_ev, h1, h2, List.take_append_drop]
          have hunit : ∀ X ∈ β, B.unitLie k r X := by
            intro X hX
            obtain ⟨i, rfl⟩ := hβe X hX
            exact he i
          rw [hev]
          exact (cstW_spec hF _ _ (fun X hX => hunit X (List.mem_of_mem_take hX))
            (fun X hX => hunit X (List.mem_of_mem_drop hX)) hg).trans (le_max_left _ _)
  refine ⟨∑ a ∈ Finset.range (m + 1), ∑ b ∈ Finset.range (m + 1), termW e K hF a b, ?_, ?_⟩
  · intro g₀ hg₀
    obtain ⟨U, f', hU, hgU, hf', hff'⟩ := hF.1 g₀ hg₀
    exact ⟨U, f', hU, hgU, hf'.of_le (by exact_mod_cast le_top), hff'⟩
  · intro u v hu hv hl g hg
    refine (hword u v hu hv g hg).trans ?_
    have ha : u.length ∈ Finset.range (m + 1) := Finset.mem_range.2 (by omega)
    have hb : v.length ∈ Finset.range (m + 1) := Finset.mem_range.2 (by omega)
    calc termW e K hF u.length v.length
        ≤ ∑ b ∈ Finset.range (m + 1), termW e K hF u.length b :=
          Finset.single_le_sum (fun b _ => hterm _ b) hb
      _ ≤ ∑ a ∈ Finset.range (m + 1), ∑ b ∈ Finset.range (m + 1), termW e K hF a b :=
          Finset.single_le_sum (f := fun a => ∑ b ∈ Finset.range (m + 1), termW e K hF a b)
            (fun a _ => Finset.sum_nonneg fun b _ => hterm a b) ha

end Formalism.L2.SG.Pf.CoefDecay
end
end
