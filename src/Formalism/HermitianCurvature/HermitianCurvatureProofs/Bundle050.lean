module

public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
public import Formalism.HermitianCurvature.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

namespace Formalism.FourierDecayAlt.P.PBD

open Formalism.FourierDecayAlt NumberField

theorem plusW_eq (ys : List ℝ) (w : List C.Letter) :
    KB.plusW ys w = ys.map (fun y => ((true, y) : C.Letter)) ++ w := by
  induction ys with
  | nil => rfl
  | cons y ys ih => simp only [KB.plusW, ih, List.map_cons, List.cons_append]

theorem minusW_eq (ys : List ℝ) (w : List C.Letter) :
    KB.minusW ys w = ys.map (fun y => ((false, y + 1) : C.Letter)) ++ w := by
  induction ys with
  | nil => rfl
  | cons y ys ih => simp only [KB.minusW, ih, List.map_cons, List.cons_append]

theorem cutWord_iff (P : M.Par) (l0 : ℕ) (L : List C.Letter) :
    KB.CutWord P l0 L ↔ (∀ x ∈ L, I.OnCut P.u P.u' l0 x.2) ∧ L.Pairwise (fun x y => 2 < |x.2 - y.2|) := by
  unfold KB.CutWord
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun x hx => ?_, ?_⟩
    · obtain ⟨a, rfl⟩ := List.mem_iff_get.1 hx
      exact h1 a
    · rw [List.pairwise_iff_get]
      intro i j hij
      exact h2 i j (ne_of_lt hij)
  · rintro ⟨h1, h2⟩
    refine ⟨fun a => h1 _ (List.mem_iff_get.2 ⟨a, rfl⟩), fun a b hab => ?_⟩
    rw [List.pairwise_iff_get] at h2
    rcases lt_or_gt_of_ne hab with h | h
    · exact h2 a b h
    · rw [abs_sub_comm]; exact h2 b a h

theorem pick_one (lo hi : ℝ) (Q B : Finset ℝ) (h : 9 * ((Q.card : ℝ) + B.card) + 1 ≤ hi - lo) :
    ∃ y, lo ≤ y ∧ y + 1 ≤ hi ∧ y ∉ B ∧ y + 1 ∉ B ∧ ∀ q ∈ Q, 4 < |y - q| := by
  classical
  by_cases hn : Q.card + B.card = 0
  · have hQ : Q = ∅ := Finset.card_eq_zero.mp (by omega)
    have hB : B = ∅ := Finset.card_eq_zero.mp (by omega)
    subst hQ; subst hB
    simp only [Finset.card_empty, Nat.cast_zero, add_zero, mul_zero, zero_add] at h
    exact ⟨lo, le_refl _, by linarith, by simp, by simp, by simp⟩
  · have hn1 : (1 : ℝ) ≤ (Q.card : ℝ) + B.card := by
      have : 1 ≤ Q.card + B.card := Nat.one_le_iff_ne_zero.mpr hn
      exact_mod_cast this
    by_contra hcon
    push_neg at hcon
    have hsub : Set.Icc lo (hi - 1) ⊆
        (⋃ q ∈ Q, Metric.closedBall q 4) ∪ ((B : Set ℝ) ∪ (fun b => b - 1) '' (B : Set ℝ)) := by
      intro y hy
      by_cases hyB : y ∈ B
      · exact Or.inr (Or.inl hyB)
      by_cases hyB' : y + 1 ∈ B
      · exact Or.inr (Or.inr ⟨y + 1, hyB', by ring⟩)
      obtain ⟨q, hq, hyq⟩ := hcon y hy.1 (by linarith [hy.2]) hyB hyB'
      refine Or.inl (Set.mem_biUnion hq ?_)
      rw [Metric.mem_closedBall, Real.dist_eq]
      exact hyq
    have hfin : ((B : Set ℝ) ∪ (fun b => b - 1) '' (B : Set ℝ)).Finite :=
      B.finite_toSet.union (B.finite_toSet.image _)
    have h1 := MeasureTheory.measure_mono (μ := MeasureTheory.volume) hsub
    have h2 : MeasureTheory.volume ((⋃ q ∈ Q, Metric.closedBall q 4) ∪
        ((B : Set ℝ) ∪ (fun b => b - 1) '' (B : Set ℝ))) ≤
        ∑ q ∈ Q, MeasureTheory.volume (Metric.closedBall q (4 : ℝ)) := by
      refine (MeasureTheory.measure_union_le _ _).trans ?_
      rw [hfin.measure_zero, add_zero]
      exact MeasureTheory.measure_biUnion_finset_le _ _
    have h3 := h1.trans h2
    simp only [Real.volume_Icc, Real.volume_closedBall, Finset.sum_const, nsmul_eq_mul] at h3
    have h4 : ENNReal.ofReal (hi - 1 - lo) ≤ ENNReal.ofReal (8 * Q.card) := by
      refine h3.trans (le_of_eq ?_)
      rw [show (8 : ℝ) * Q.card = (Q.card : ℝ) * (2 * 4) by ring,
        ENNReal.ofReal_mul (p := (Q.card : ℝ)) (by positivity), ENNReal.ofReal_natCast]
    rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h4
    have : (0 : ℝ) ≤ Q.card := by positivity
    have : (0 : ℝ) ≤ B.card := by positivity
    linarith

theorem pick_many (lo hi : ℝ) (B : Finset ℝ) : ∀ (m : ℕ) (Q : Finset ℝ),
    9 * ((Q.card : ℝ) + m + B.card) + 1 ≤ hi - lo →
    ∃ ys : List ℝ, ys.length = m ∧
      (∀ y ∈ ys, lo ≤ y ∧ y + 1 ≤ hi ∧ y ∉ B ∧ y + 1 ∉ B ∧ ∀ q ∈ Q, 4 < |y - q|) ∧
      ys.Pairwise (fun y y' => 4 < |y - y'|) := by
  intro m
  induction m with
  | zero => exact fun _ _ => ⟨[], rfl, by simp, List.Pairwise.nil⟩
  | succ m ih =>
    intro Q h
    classical
    push_cast at h
    have hpick : 9 * ((Q.card : ℝ) + B.card) + 1 ≤ hi - lo := by linarith
    obtain ⟨y, h1, h2, h3, h4, h5⟩ := pick_one lo hi Q B hpick
    have hc : ((insert y Q).card : ℝ) ≤ Q.card + 1 := by exact_mod_cast Finset.card_insert_le y Q
    obtain ⟨ys, hl, hys, hp⟩ := ih (insert y Q) (by linarith)
    refine ⟨y :: ys, by simp [hl], ?_, ?_⟩
    · intro z hz
      rcases List.mem_cons.1 hz with rfl | hz
      · exact ⟨h1, h2, h3, h4, h5⟩
      · obtain ⟨a, b, c, d, e⟩ := hys z hz
        exact ⟨a, b, c, d, fun q hq => e q (Finset.mem_insert_of_mem hq)⟩
    · refine List.Pairwise.cons (fun z hz => ?_) hp
      have := (hys z hz).2.2.2.2 y (Finset.mem_insert_self y Q)
      rwa [abs_sub_comm] at this

theorem two_lt_of_four_lt {y p : ℝ} (h : 4 < |y - p|) : 2 < |y + 1 - p| := by
  rcases lt_abs.mp h with h | h
  · exact lt_abs.mpr (Or.inl (by linarith))
  · exact lt_abs.mpr (Or.inr (by linarith))

def RoomOffGrid : Prop :=
  ∀ (P : M.Par) (l0 : ℕ) (lo hi : ℝ), (∀ Y, lo ≤ Y → Y ≤ hi → I.OnCut P.u P.u' l0 Y) →
    ∀ (w : List C.Letter) (m : ℕ) (B : Finset ℝ), KB.CutWord P l0 w →
      10 * ((w.length : ℝ) + m + B.card + 1) ≤ hi - lo →
      ∃ ys : List ℝ, ys.length = m ∧ (∀ y ∈ ys, lo ≤ y ∧ y + 1 ≤ hi ∧ y ∉ B ∧ y + 1 ∉ B) ∧
        ys.Pairwise (fun y y' => 4 < |y - y'|) ∧ KB.CutWord P l0 (KB.plusW ys w) ∧
        KB.CutWord P l0 (KB.minusW ys w)

theorem roomOffGrid : RoomOffGrid := by
  intro P l0 lo hi hOn w m B hw hlen
  classical
  obtain ⟨hw1, hw2⟩ := (cutWord_iff P l0 w).1 hw
  have hQ : (((w.map Prod.snd).toFinset).card : ℝ) ≤ w.length := by
    have := List.toFinset_card_le (w.map Prod.snd)
    rw [List.length_map] at this
    exact_mod_cast this
  obtain ⟨ys, hlen', hys, hpw⟩ := pick_many lo hi B m ((w.map Prod.snd).toFinset) (by
    have : (0 : ℝ) ≤ B.card := by positivity
    have : (0 : ℝ) ≤ m := by positivity
    linarith)
  have hfar : ∀ y ∈ ys, ∀ x ∈ w, 4 < |y - x.2| := fun y hy x hx =>
    (hys y hy).2.2.2.2 x.2 (List.mem_toFinset.2 (List.mem_map.2 ⟨x, hx, rfl⟩))
  refine ⟨ys, hlen', fun y hy => ⟨(hys y hy).1, (hys y hy).2.1, (hys y hy).2.2.1, (hys y hy).2.2.2.1⟩,
    hpw, ?_, ?_⟩
  · rw [plusW_eq, cutWord_iff]
    refine ⟨fun x hx => ?_, ?_⟩
    · rcases List.mem_append.1 hx with hx | hx
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
        exact hOn y (hys y hy).1 (by linarith [(hys y hy).2.1])
      · exact hw1 x hx
    · rw [List.pairwise_append]
      refine ⟨?_, hw2, ?_⟩
      · rw [List.pairwise_map]
        exact hpw.imp fun h => by dsimp only; linarith
      · intro a ha b hb
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 ha
        have := hfar y hy b hb
        dsimp only
        linarith
  · rw [minusW_eq, cutWord_iff]
    refine ⟨fun x hx => ?_, ?_⟩
    · rcases List.mem_append.1 hx with hx | hx
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
        exact hOn (y + 1) (by linarith [(hys y hy).1]) (hys y hy).2.1
      · exact hw1 x hx
    · rw [List.pairwise_append]
      refine ⟨?_, hw2, ?_⟩
      · rw [List.pairwise_map]
        exact hpw.imp fun h => by dsimp only; rw [add_sub_add_right_eq_sub]; linarith
      · intro a ha b hb
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 ha
        exact two_lt_of_four_lt (hfar y hy b hb)

end Formalism.FourierDecayAlt.P.PBD

theorem Formalism.FourierDecayAlt.P.room_off_grid : Formalism.FourierDecayAlt.P.PBD.RoomOffGrid := Formalism.FourierDecayAlt.P.PBD.roomOffGrid
end

section

noncomputable section

open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.PBI

def FrameTransport : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (X₀ : Q.ActualOps P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π') (μ₀ : Measure (Mt P.k P.r))
    (L₀ : R.LevelData (Q.Pr (Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π')) P.r)
    (st₀ : Fr.Start (Q.Pr (Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π')))
    (X : Q.ActualOps (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π')
    (μ : Measure (Mt P.k (P.r - P.r)))
    (L : R.LevelData (Q.Pr (Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
      (p.T.bs P.r).π (p.T.bs P.r).π')) (JC.parLev P P.r).r)
    (st : Fr.Start (Q.Pr (Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
      (p.T.bs P.r).π (p.T.bs P.r).π'))),
    P5.IsData P p.T.base.z p.T.base.z' p.T.base.π p.T.base.π' X₀ μ₀ L₀ st₀ p.l0 →
    P5.IsData (JC.parLev P P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π' X μ L st p.l0 →
    ∀ c : Fin P.r → ℂ, c ∈ Formalism.QuantumDeterminants.OmX P.r →
    ∃ T : Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π' →ₗ[ℂ]
        Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π',
      (∀ Ψ c' g, (T Ψ : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) c' g =
        (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (D.castM (by omega) (ιLev P.k P.r (P.r - P.r) g))) ∧
      ∀ (w : List C.Letter), Fr.admitted st₀ (D.positionted w) → Fr.admitted st (D.positionted w) →
      ∀ (Ψ : Wd.Ix (Fin w.length) → Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π')
        (e : Wd.Ix (Fin w.length)) (c' : Fin (JC.parLev P P.r).r → ℂ) (g : B.Mat P.k (P.r - P.r)),
        g ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) → 0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' g →
        (P5.act (Fr.ofWord L₀ st₀ (D.positionted w)).F Ψ e : Q.Fn P.k P.r (Wq →L[ℂ] Wp))
            c (D.castM (by omega) (ιLev P.k P.r (P.r - P.r) g)) =
          (P5.act (Fr.ofWord L st (D.positionted w)).F (fun e' => T (Ψ e')) e :
            Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) c' g

def ParFam {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {Par : Type} [NormedAddCommGroup Par]
    [NormedSpace ℝ Par] (k ρ : ℕ) (U₀ : Set (Par × Mt k ρ)) (f : Par × Mt k ρ → E) : Prop :=
  ∀ q₀ ∈ U₀, Matrix.of q₀.2 ∈ Q.Glev k ρ (Fin.last ρ) → ∃ (U : Set (Par × Mt k ρ)) (F : Par × Mt k ρ → E),
    IsOpen U ∧ q₀ ∈ U ∧ ContDiffOn ℝ ∞ F U ∧ ∀ q ∈ U, Matrix.of q.2 ∈ Q.Glev k ρ (Fin.last ρ) → f q = F q

def FrameParam : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (X : Q.ActualOps (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π')
    (μ : Measure (Mt P.k (P.r - P.r)))
    (L : R.LevelData (Q.Pr (Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
      (p.T.bs P.r).π (p.T.bs P.r).π')) (JC.parLev P P.r).r)
    (st : Fr.Start (Q.Pr (Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
      (p.T.bs P.r).π (p.T.bs P.r).π'))),
    P5.IsData (JC.parLev P P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π' X μ L st p.l0 →
    ∀ (w : List C.Letter), Fr.admitted st (D.positionted w) →
    ∀ (Par : Type) [NormedAddCommGroup Par] [NormedSpace ℝ Par] [FiniteDimensional ℝ Par] [MeasurableSpace Par]
      [BorelSpace Par] (U₀ : Set (Par × Mt P.k (P.r - P.r))), IsOpen U₀ →
      U₀ ⊆ Set.univ ×ˢ {y | 0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Matrix.of y)} →
    ∀ (Ψ : Par → Wd.Ix (Fin w.length) → Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z
        (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π')
      (Ψf : Par → Wd.Ix (Fin w.length) → Mt P.k (P.r - P.r) → (Wq →L[ℂ] Wp)),
      (∀ Z e c y, Matrix.of y ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) →
        (Ψ Z e : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) c (Matrix.of y) = Ψf Z e y) →
      (∀ e, ParFam P.k (P.r - P.r) U₀ (fun q => Ψf q.1 e q.2)) →
      ∃ Φf : Par → Wd.Ix (Fin w.length) → Mt P.k (P.r - P.r) → (Wq →L[ℂ] Wp),
        (∀ Z e c y, Matrix.of y ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) →
          (P5.act (Fr.ofWord L st (D.positionted w)).F (Ψ Z) e :
            Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) c (Matrix.of y) = Φf Z e y) ∧
        (∀ e, ParFam P.k (P.r - P.r) U₀ (fun q => Φf q.1 e q.2)) ∧
        (∀ (K : Set (Par × Mt P.k (P.r - P.r))),
          (∀ e q, Matrix.of q.2 ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) → q ∉ K → Ψf q.1 e q.2 = 0) →
          ∀ e q, q ∈ U₀ → Matrix.of q.2 ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) → q ∉ closure K → Φf q.1 e q.2 = 0) ∧
        ∀ (ν : Measure Par) [IsFiniteMeasure ν] (Kp : Set Par), IsCompact Kp → ν Kpᶜ = 0 →
        ∀ (Ψi : Wd.Ix (Fin w.length) → Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z
            (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π') (y : Mt P.k (P.r - P.r)) (V : Set (Mt P.k (P.r - P.r))),
          IsOpen V → y ∈ V → Matrix.of y ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) → Kp ×ˢ V ⊆ U₀ →
          (∀ e c y', y' ∈ V → Matrix.of y' ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) →
            (Ψi e : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) c (Matrix.of y') =
              ∫ Z, Ψf Z e y' ∂ν) →
          ∀ e c, (P5.act (Fr.ofWord L st (D.positionted w)).F Ψi e :
              Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) c (Matrix.of y) = ∫ Z, Φf Z e y ∂ν

def RadWord : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (X₀ : Q.ActualOps P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π') (μ₀ : Measure (Mt P.k P.r))
    (L₀ : R.LevelData (Q.Pr (Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π')) P.r)
    (st₀ : Fr.Start (Q.Pr (Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π'))),
    P5.IsData P p.T.base.z p.T.base.z' p.T.base.π p.T.base.π' X₀ μ₀ L₀ st₀ p.l0 →
    ∀ (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), KB.CptCoef p.T.base G →
    ∀ (w : List C.Letter), KB.CutWord P p.l0 w →
    ∀ Φ_G : Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π', Top.IsRadOf P p.T.base Φ_G G →
    ∀ e : Wd.Ix (Fin w.length),
      Top.IsRadOf P p.T.base (P5.act (P5.bTall L₀ (D.positionted w)) (Top.firstStateVector Φ_G) e)
        (D.uwG P.k P.r p.T.base.z p.T.base.z' G P.r le_rfl w e)

def hcell {r : ℕ} (c : Fin r → ℂ) : C.LPt := List.ofFn fun j => (1, c j)

theorem ptSize_hcell {r : ℕ} (c : Fin r → ℂ) : D.ptSize (hcell c) = r := by
  simp [hcell, D.ptSize, List.map_ofFn, Function.comp_def]

def RadWordSlice : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (X₀ : Q.ActualOps P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π') (μ₀ : Measure (Mt P.k P.r))
    (L₀ : R.LevelData (Q.Pr (Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π')) P.r)
    (st₀ : Fr.Start (Q.Pr (Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π'))),
    P5.IsData P p.T.base.z p.T.base.z' p.T.base.π p.T.base.π' X₀ μ₀ L₀ st₀ p.l0 →
    ∀ (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), KB.CptCoef p.T.base G →
    ∀ (w : List C.Letter), KB.CutWord P p.l0 w →
    ∀ Φ_G : Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π', Top.IsRadOf P p.T.base Φ_G G →
    ∀ (e : Wd.Ix (Fin w.length)) (c : Fin P.r → ℂ), c ∈ Formalism.QuantumDeterminants.OmX P.r →
    ∀ g : B.Mat P.k (P.r - P.r), g ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) →
      0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' g →
      (P5.act (P5.bTall L₀ (D.positionted w)) (Top.firstStateVector Φ_G) e : Q.Fn P.k P.r (Wq →L[ℂ] Wp))
          c (D.castM (by omega) (ιLev P.k P.r (P.r - P.r) g)) =
        ((∏ j : Fin P.r, ‖c j‖ ^ (2 * (P.r - (j : ℕ)) + P.k) : ℝ) : ℂ) •
          B.JF (p.T.bs P.r) (D.castF (by rw [ptSize_hcell]) (D.sliceAt P.k P.r p.T.base.z p.T.base.z'
            (D.uwG P.k P.r p.T.base.z p.T.base.z' G P.r le_rfl w e) (hcell c))) g

def PicSlice : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), KB.CptCoef p.T.base G →
    ∀ Φ_G : Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π', Top.IsRadOf P p.T.base Φ_G G →
    ∀ (c : Fin P.r → ℂ), c ∈ Formalism.QuantumDeterminants.OmX P.r →
    ∀ g : B.Mat P.k (P.r - P.r), g ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) →
      0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' g →
      (Φ_G : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (D.castM (by omega) (ιLev P.k P.r (P.r - P.r) g)) =
        ((∏ j : Fin P.r, ‖c j‖ ^ (2 * (P.r - (j : ℕ)) + P.k) : ℝ) : ℂ) •
          B.JF (p.T.bs P.r) (D.castF (by rw [ptSize_hcell]) (D.sliceAt P.k P.r p.T.base.z p.T.base.z' G (hcell c))) g

end Formalism.FourierDecayAlt.P.PBI
end
end

section

open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

def mc {k ρ m : ℕ} (e : ρ + 1 = m) (c : ℂ) (γ : B.Mat k ρ) : B.Mat k m :=
  D.castM e (D.castM (Nat.add_comm 1 ρ) (U.mMap k 1 ρ (Matrix.of fun _ _ => c) γ))

def rn1 {k ρ m : ℕ} (e : ρ + 1 = m) (x : U.RC k 1 ρ) : B.Mat k m :=
  D.castM e (D.castM (Nat.add_comm 1 ρ) (U.Rn k 1 ρ x))

def lev1 {k ρ m : ℕ} (e : ρ + 1 = m) (y : B.Mat k ρ) : B.Mat k m :=
  D.castM e (D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ y))

def JFStep : Prop :=
  ∀ (k ρ m : ℕ) (e : ρ + 1 = m) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (B1 : B.RealPlaceData k m Wp Wq) (B0 : B.RealPlaceData k ρ Wp Wq),
    B1.z = D.castV e (D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ B0.z)) →
    B1.z' = D.castV e (D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ B0.z')) →
    (∀ y : B.Mat k ρ, B0.π y = B1.π (lev1 e y)) → (∀ y : B.Mat k ρ, B0.π' y = B1.π' (lev1 e y)) →
    B1.μW Set.univ = 1 → B1.μW' Set.univ = 1 → B0.μW Set.univ = 1 → B0.μW' Set.univ = 1 →
    B1.μN = D.muN k m → B0.μN = D.muN k ρ →
    ∀ (f1 : B.Mat k m → (Wq →L[ℂ] Wp)) (f0 : B.Mat k ρ → (Wq →L[ℂ] Wp)) (c : ℂ), c ≠ 0 → KB.CptCoef B1 f1 →
    (∀ γ ∈ B.GV k ρ, f0 γ = ∫ xx : U.RC k 1 ρ × U.RC k 1 ρ,
        (psi k m B1.z cStd (rn1 e xx.1) * star (psi k m B1.z' cStd (rn1 e xx.2))) •
          f1 ((rn1 e xx.1)⁻¹ * mc e c γ * rn1 e xx.2) ∂((U.muRC k 1 ρ).prod (U.muRC k 1 ρ))) →
    ∀ γ ∈ B.GV k ρ, γ ∈ Q.OmPlus k ρ B0.z B0.z' →
      B.JF B0 f0 γ = B.JF B1 f1 (mc e c γ)

end Formalism.FourierDecayAlt.P.PBH

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

def PointStep : Prop :=
  ∀ (k j ρ : ℕ) (σ : Equiv.Perm (Fin j)) (d : Fin j → ℂ), (∀ i, d i ≠ 0) → ∀ (c : ℂ), c ≠ 0 →
    ∀ (zA zA' : Fin (2 * (j + 1 + ρ) + k + 1) → ℂ), inWb k (j + 1 + ρ) zA → inWb k (j + 1 + ρ) zA' →
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (F : B.Mat k (j + 1 + ρ) → E)
      (γ : B.Mat k ρ),
      Integrable (fun ξ : U.Xi k j 1 ρ σ =>
          U.psiStar k ρ σ zA zA' ξ • F (U.gaXi k ρ σ d ξ (fun _ _ => c) γ)) (U.muXi k j 1 ρ σ) →
      U.PhiFun k ρ σ d zA zA' F (fun _ _ => c) γ =
        ∫ yy : U.RC k 1 ρ × U.RC k 1 ρ,
          (psi k (1 + ρ) (U.lowV k j (1 + ρ) (D.castV (by omega : j + 1 + ρ = j + (1 + ρ)) zA)) cStd
              (U.Rn k 1 ρ yy.1) *
            star (psi k (1 + ρ) (U.lowV k j (1 + ρ) (D.castV (by omega : j + 1 + ρ = j + (1 + ρ)) zA')) cStd
              (U.Rn k 1 ρ yy.2))) •
          U.PhiFun (p := j) (s := 0) k (1 + ρ) σ d (D.castV (by omega : j + 1 + ρ = j + (1 + ρ)) zA)
            (D.castV (by omega : j + 1 + ρ = j + (1 + ρ)) zA') (D.castF (by omega : j + (1 + ρ) = j + 1 + ρ) F)
            (fun a => a.elim0)
            ((U.Rn k 1 ρ yy.1)⁻¹ * U.mMap k 1 ρ (Matrix.of fun _ _ => c) γ * U.Rn k 1 ρ yy.2)
          ∂((U.muRC k 1 ρ).prod (U.muRC k 1 ρ))

end Formalism.FourierDecayAlt.P.PBH
end
end

section

namespace Formalism.FourierDecayAlt.P.PBI

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

def HighestUnipotentIntegral : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (h : C.LPt) (ζ : ℂ) (hh : D.IsLocPt h P.r)
    (ν'r : Fin (2 * (P.r - P.r) + P.k + 1) → ℂ) (m₀r : B.Mat P.k (P.r - P.r)),
    KB.CptCoef p.T.base F → ζ ≠ 0 →
    D.castV (by omega) (liftVec P.k P.r (P.r - P.r) ν'r) = p.ν' →
    D.castM (by omega) (ιLev P.k P.r (P.r - P.r) m₀r) = p.m₀ →
    p.V F (h ++ [(1, ζ)]) =
      D.vecV (p.T.bs P.r) ν'r m₀r
        (D.castF (by simp [hh.2]) (D.sliceAt P.k P.r p.T.base.z p.T.base.z' F h)) [(1, ζ)]

end

end Formalism.FourierDecayAlt.P.PBI
end

section

namespace Formalism.FourierDecayAlt.KB

open Finset Filter Topology NumberField MeasureTheory Matrix Formalism.QuantumDeterminants

noncomputable section

def SizeStdCpt : Prop :=
  P5.ThmPActualCpt → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : Pl P Wp Wq) (j : ℕ)
    (hj : j ≤ P.r) (w : List C.Letter) (ys : List ℝ),
    CutWord P p.l0 (plusW ys w) → CutWord P p.l0 (minusW ys w) → ys.Pairwise (fun y y' => 2 < |y - y'|) →
    (∀ y ∈ ys, 0 < (Wd.qw (M.qC P) (D.positionted w) y).re) ∧
    ∀ x x', (∀ e, CptCoef (p.T.bs j) (x e)) → (∀ e, CptCoef (p.T.bs j) (x' e)) →
      ‖pairJ (p.form j hj w) ys x x'‖ ^ 2 * (ys.map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) y).re).prod ≤
        (p.form j hj (plusW ys w) x x).re * (p.form j hj (minusW ys w) x' x').re

def VIsoCpt : Prop :=
  P5.ThmPActualCpt → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : Pl P Wp Wq) (j : ℕ)
    (hj : j ≤ P.r) (w : List C.Letter), CutWord P p.l0 w →
    ∀ (s : ℂ) x x', (∀ e, CptCoef (p.T.bs j) (x e)) → (∀ e, CptCoef (p.T.bs j) (x' e)) →
      (∀ e, CptCoef (p.T.bs j) (waveG (p.T.bs j) s w x e)) ∧
      p.form j hj w (waveG (p.T.bs j) s w x) (waveG (p.T.bs j) s w x') = p.form j hj w x x'

end

end Formalism.FourierDecayAlt.KB
end
