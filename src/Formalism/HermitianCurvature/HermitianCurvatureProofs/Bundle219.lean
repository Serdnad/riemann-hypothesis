module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle210
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleAtOfAdmissibleList
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChartSysWOfPartsOf
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutDec
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle090
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle209
public import Formalism.HermitianCurvature.StatementHeads
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DegLiftOf
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FirstDerivativeAtNormalSet
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyZeroNear
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle096
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle113
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
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
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

open Matrix Finset MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBG

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

def KrHyp : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (j : ℕ) (hj : j ≤ r) (H : B.Mat k r → (Wq →L[ℂ] Wp)),
    (∀ x ∈ B.GV k r, Dmin k r Bs.z Bs.z' x ⟨j, by omega⟩ ≠ 0 → CapelliWordSumExpansion.Loc (⊤ : ℕ∞) H x) →
    (∃ R : ℝ, ∀ x ∈ B.GV k r, H x ≠ 0 → B.gN x ≤ R) →
    ∀ y ∈ B.GV k r, Dmin k r Bs.z Bs.z' y ⟨j, by omega⟩ ≠ 0 →
      CapelliWordSumExpansion.Loc (⊤ : ℕ∞) (Kr Bs H) y ∧
      ∀ (l : C.Letter) (e : Fin 2), Kr Bs (D.vLet k r Bs.z Bs.z' j hj l e H) y = D.vLet k r Bs.z Bs.z' j hj l e (Kr Bs H) y

theorem liftDegAll_of (hLF : LeftFubiniLemmas.LeftFubini) (hNF : LeftFubiniLemmas.NFHypL) (hKr : KrHyp) : LiftDegAll := by
  intro Wp Wq _ _ _ _ _ _ P p F hF j s hj h τ ha w' a' b δ g hg
  have hsz : D.ptSize (h ++ [(s, τ)]) = D.ptSize h + s := Formalism.FourierDecayAlt.P.Dx2.SL.ptSize_append h s τ
  have hs1 : 1 ≤ s := (ha.1 (s, τ) (by simp)).1
  have hj1 : 1 ≤ j := by rw [← ha.2, hsz]; omega
  obtain ⟨X, _, μ, ℓ, sx, hsx, hFubG⟩ := hLF P.k P.r Wp Wq p.T p.hT j hj hj1 (h ++ [(s, τ)]) ha
  have hgG : g ∈ B.GV P.k (P.r - j) := hg.1
  have hg' : D.castM (by rw [ha.2]) g ∈ B.GV P.k (P.r - D.ptSize (h ++ [(s, τ)])) :=
    Formalism.FourierDecayAlt.P.PBE.castM_GV _ hgG
  have hl : D.IsLocPt (h ++ [(s, τ)]) (D.ptSize (h ++ [(s, τ)])) := ⟨ha.1, rfl⟩
  obtain ⟨hx₁G, hxi, hy⟩ := hNF P.k P.r (h ++ [(s, τ)]) (by rw [ha.2]; exact hj) _ hg' hl
  set PC : (B.Mat P.k P.r → (Wq →L[ℂ] Wp)) → Prop := fun H =>
    (∀ x ∈ B.GV P.k P.r, Dmin P.k P.r p.T.base.z p.T.base.z' x ⟨j, by omega⟩ ≠ 0 → CapelliWordSumExpansion.Loc (⊤ : ℕ∞) H x) ∧
    (∃ R : ℝ, ∀ x ∈ B.GV P.k P.r, H x ≠ 0 → B.gN x ≤ R) with hPC
  refine liftDeg_core p.T F j s hj h τ ha w' a' b δ g X μ ℓ sx _ hsx hx₁G ?_ ?_ PC
    (fun H hH => hFubG g hg H (contOn_of_loc (S := {x | Dmin P.k P.r p.T.base.z p.T.base.z' x ⟨j, by omega⟩ ≠ 0}) (fun x hx hxG => hH.1 x hxG hx)) hH.2) ?_
    (fun H hH y hyG hyD => (hKr P.k P.r Wp Wq p.T.base j hj H hH.1 hH.2 y hyG hyD).1)
    (fun H hH y hyG hyD => (hKr P.k P.r Wp Wq p.T.base j hj H hH.1 hH.2 y hyG hyD).2)
  · intro a₀ q ha₀
    rw [hxi a₀ q (by rw [hsz]; exact ha₀)]
    by_cases hq : q.val < D.ptSize h + s
    · rw [dite_eq_left (by rw [hsz]; exact hq), if_pos hq]
      exact hmat_zb h s τ hl a₀.val q.val _ _
    · rw [dite_eq_right (by rw [hsz]; exact hq), if_neg hq]
  · intro a₀ q ha₀
    rw [hy a₀ q (by rw [hsz]; exact ha₀)]
    by_cases hq : P.r + P.k < q.val ∧ 2 * P.r + P.k - q.val < D.ptSize h + s
    · rw [dite_eq_left (by rw [hsz]; exact hq), if_pos hq, hmat_zb h s τ hl a₀.val _ _ _]
    · rw [dite_eq_right (by rw [hsz]; exact hq), if_neg hq]
  · intro w e
    refine ⟨fun x hxG hxD => uwG_mem (E := Wq →L[ℂ] Wp) p.T.base.z p.T.base.z' j hj hF.1 w e x hxD hxG, ?_⟩
    obtain ⟨R, hR⟩ := hF.2.1
    exact ⟨R, uwG_supp p.T.base.z p.T.base.z' F R hR j hj w e⟩

theorem degLift_of_parts (hLF : LeftFubiniLemmas.LeftFubini) (hKr : KrHyp) : KB.DegLift :=
  degLift_of (liftDegAll_of hLF LeftFubiniLemmas.normal_form_left_hypothesis hKr)

end Formalism.FourierDecayAlt.P.PBG
end
end

section

namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

section helpers

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

theorem mix_pushT (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (ε : ℝ) (i : ℕ) {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ)
    (mk : List ℝ → List C.Letter) (P Q : C.LPt) :
    KB.mix S v ε i (PBD.pushU grid mk) (PBD.pushTh grid mk) P Q =
      ∑ n : Fin K → Fin (d + 1), ((F7.thGrid grid n : ℝ) : ℂ) * KB.gN S v ε i (mk (List.ofFn fun b => grid b (n b))) P Q := by
  unfold KB.mix PBD.pushTh
  simp only [Complex.ofReal_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hmem : mk (List.ofFn fun b => grid b (n b)) ∈ PBD.pushU grid mk :=
    Finset.mem_image_of_mem _ (Finset.mem_univ n)
  simp only [apply_ite, Complex.ofReal_zero, zero_mul, ite_mul]
  rw [Finset.sum_ite_eq, if_pos hmem]

end helpers

section lists

theorem ofFn_split {K : ℕ} (f : Fin K → ℝ) (ys₁ : List ℝ) (y : ℝ) (ys₂ : List ℝ)
    (h : List.ofFn f = ys₁ ++ y :: ys₂) :
    ∃ b₀ : Fin K, b₀.val = ys₁.length ∧ y = f b₀ ∧ ys₁.length + 1 + ys₂.length = K ∧
      ∀ y' ∈ ys₂, ∃ b' : Fin K, b₀ < b' ∧ y' = f b' := by
  have hlen : K = ys₁.length + 1 + ys₂.length := by
    have := congrArg List.length h
    simp only [List.length_ofFn, List.length_append, List.length_cons] at this
    omega
  have hb : ys₁.length < K := by omega
  refine ⟨⟨ys₁.length, hb⟩, rfl, ?_, hlen.symm, ?_⟩
  · have h1 : (List.ofFn f)[ys₁.length]'(by simp; omega) = (ys₁ ++ y :: ys₂)[ys₁.length]'(by simp) := by
      simp only [h]
    rw [List.getElem_ofFn, List.getElem_append_right (by omega)] at h1
    simp only [Nat.sub_self, List.getElem_cons_zero] at h1
    exact h1.symm
  · intro y' hy'
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy'
    refine ⟨⟨ys₁.length + (i + 1), by omega⟩, by simp only [Fin.lt_def]; omega, ?_⟩
    have h1 : (List.ofFn f)[ys₁.length + (i + 1)]'(by simp; omega) =
        (ys₁ ++ y :: ys₂)[ys₁.length + (i + 1)]'(by simp; omega) := by simp only [h]
    rw [List.getElem_ofFn] at h1
    simp only [List.getElem_append, Nat.add_sub_cancel_left, List.getElem_cons_succ,
      show ¬ (ys₁.length + (i + 1) < ys₁.length) by omega, dite_false] at h1
    exact h1.symm

theorem rhyp_of {P : M.Par} (l0 : ℕ) (a : List C.Letter) (e : Wd.Ix (Fin a.length)) (ρ : M.Ty P) (Pv : ℝ → ℝ)
    (C : ℝ) : ∀ ys : List ℝ, (∀ ys₁ y ys₂, ys = ys₁ ++ y :: ys₂ →
      0 < (topR l0 (KB.plusW ys₂ a) (KB.firstSt ys₂ e) ρ y).re ∧
      (topR l0 (KB.plusW ys₂ a) (KB.firstSt ys₂ e) ρ y).im = 0 ∧
      |Pv y| ≤ C * (topR l0 (KB.plusW ys₂ a) (KB.firstSt ys₂ e) ρ y).re) → RHyp l0 a e ρ Pv C ys
  | [], _ => trivial
  | y :: ys, H => ⟨H [] y ys rfl, rhyp_of l0 a e ρ Pv C ys fun ys₁ y' ys₂ h => H (y :: ys₁) y' ys₂ (by rw [h]; rfl)⟩

end lists

end

end Formalism.FourierDecayAlt.P.PBL
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix Polynomial
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem gv_facts {k r : ℕ} {g : B.Mat k r} (hg : g ∈ B.GV k r) :
    g⁻¹ * g = 1 ∧ g * g⁻¹ = 1 ∧ Hpk k r * g = (g⁻¹)ᴴ * Hpk k r ∧ gᴴ * Hpk k r = Hpk k r * g⁻¹ := by
  obtain ⟨-, hHH, -⟩ := Formalism.QuantumDeterminants.hermitian_pos_facts_hold k r
  have hg0 : gᴴ * Hpk k r * g = Hpk k r := hg
  have hl : (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
    calc (Hpk k r * gᴴ * Hpk k r) * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg0, hHH]
  have hr : g * (Hpk k r * gᴴ * Hpk k r) = 1 := mul_eq_one_comm.mp hl
  have hinv : g⁻¹ = Hpk k r * gᴴ * Hpk k r := Matrix.inv_eq_left_inv hl
  have hgi : g⁻¹ * g = 1 := by rw [hinv]; exact hl
  have hig : g * g⁻¹ = 1 := by rw [hinv]; exact hr
  refine ⟨hgi, hig, ?_, ?_⟩
  · calc Hpk k r * g = ((g⁻¹)ᴴ * gᴴ) * Hpk k r * g := by
          rw [← Matrix.conjTranspose_mul, hig, Matrix.conjTranspose_one, Matrix.one_mul]
      _ = (g⁻¹)ᴴ * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
      _ = (g⁻¹)ᴴ * Hpk k r := by rw [hg0]
  · calc gᴴ * Hpk k r = gᴴ * Hpk k r * (g * g⁻¹) := by rw [hig, Matrix.mul_one]
      _ = (gᴴ * Hpk k r * g) * g⁻¹ := by simp only [Matrix.mul_assoc]
      _ = Hpk k r * g⁻¹ := by rw [hg0]

theorem conjugation_algebraic_holds : ConjAlg := by
  intro k r g hg
  obtain ⟨hgi, hig, hHg, hgH⟩ := gv_facts hg
  refine ⟨fun A hA => ?_, fun A hA => ?_, fun A h0 => ?_, fun A X => ?_⟩
  · unfold B.inLie at hA ⊢
    have e1 : (g * A * g⁻¹)ᴴ * Hpk k r = (g⁻¹)ᴴ * (Aᴴ * Hpk k r) * g⁻¹ := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
      rw [hgH]
    have e2 : Hpk k r * (g * A * g⁻¹) = (g⁻¹)ᴴ * (Hpk k r * A) * g⁻¹ := by
      simp only [← Matrix.mul_assoc]
      rw [hHg]
    rw [e1, e2, ← Matrix.add_mul, ← Matrix.mul_add, hA, Matrix.mul_zero, Matrix.zero_mul]
  · obtain ⟨n, hn⟩ := hA
    refine ⟨n, ?_⟩
    have hp : ∀ m : ℕ, (g * A * g⁻¹) ^ m = g * A ^ m * g⁻¹ := by
      intro m
      induction m with
      | zero => simp [hig]
      | succ m ih =>
        rw [pow_succ, ih, pow_succ]
        calc g * A ^ m * g⁻¹ * (g * A * g⁻¹) = g * A ^ m * (g⁻¹ * g) * A * g⁻¹ := by
              simp only [Matrix.mul_assoc]
          _ = g * (A ^ m * A) * g⁻¹ := by rw [hgi, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    rw [hp, hn, Matrix.mul_zero, Matrix.zero_mul]
  · intro h
    apply h0
    calc A = (g⁻¹ * g) * A * (g⁻¹ * g) := by rw [hgi, Matrix.one_mul, Matrix.mul_one]
      _ = g⁻¹ * (g * A * g⁻¹) * g := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [h, Matrix.mul_zero, Matrix.zero_mul]
  · have e : (g * A * g⁻¹) * (g * X * g⁻¹) = g * (A * X * g⁻¹) := by
      calc (g * A * g⁻¹) * (g * X * g⁻¹) = g * A * (g⁻¹ * g) * X * g⁻¹ := by simp only [Matrix.mul_assoc]
        _ = g * (A * X * g⁻¹) := by rw [hgi, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    rw [e, Matrix.trace_mul_comm, Matrix.mul_assoc, hgi, Matrix.mul_one]

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def wfam {d : ℕ} {α : Type} (L : List (ℂ × List α)) (F : α → (Fin d → ℝ) → (Fin d → ℝ)) (c : ℂ) : WOp d :=
  L.map (fun t => (t.1, t.2.map F)) ++ [(c, [])]

def WFamApp : Prop :=
  ∀ (d : ℕ) (α : Type) (L : List (ℂ × List α)) (F : α → (Fin d → ℝ) → (Fin d → ℝ)) (c : ℂ)
    (v : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ),
    WOp.app (wfam L F c) v x = (L.map fun t => t.1 * vfW (t.2.map F) v x).sum + c * v x

def WFamSymb : Prop :=
  ∀ (d : ℕ) (α : Type) (L : List (ℂ × List α)) (F : α → (Fin d → ℝ) → (Fin d → ℝ)) (c : ℂ) (j : ℕ)
    (x ξ : Fin d → ℝ) (τ : α → ℂ), 1 ≤ j → (∀ t ∈ L, ∀ X ∈ t.2, ((ξ ⬝ᵥ F X x : ℝ) : ℂ) = τ X) →
    WOp.symb (wfam L F c) j x ξ = (L.map fun t => if t.2.length = j then t.1 * (t.2.map τ).prod else 0).sum

def TrRealLie : Prop :=
  ∀ (k r : ℕ) (A X : B.Mat k r), B.inLie k r A → B.inLie k r X →
    (((Matrix.trace (A * X)).re : ℝ) : ℂ) = Matrix.trace (A * X)

def CkLevOn : Prop :=
  ∀ (k r m : ℕ) (Dm : Set (B.Mat k r)) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (f : B.Mat k r → E),
    Q.CkLev k r 0 m Dm f → B.CkOn (m : ℕ∞) (B.GV k r ∩ Dm) f

theorem wfam_ok {d : ℕ} {α : Type} {O : Set (Fin d → ℝ)} (L : List (ℂ × List α))
    (F : α → (Fin d → ℝ) → (Fin d → ℝ)) (c : ℂ) (j : ℕ) (hL : ∀ t ∈ L, t.2.length ≤ j)
    (hF : ∀ X, ContDiffOn ℝ ∞ (F X) O) : FamOK O (wfam L F c) j := by
  intro t ht
  rw [wfam, List.mem_append] at ht
  rcases ht with ht | ht
  · obtain ⟨t0, ht0, rfl⟩ := List.mem_map.1 ht
    refine ⟨by simpa using hL t0 ht0, ?_⟩
    intro V hV
    obtain ⟨X, -, rfl⟩ := List.mem_map.1 hV
    exact hF X
  · simp only [List.mem_singleton] at ht
    subst ht
    exact ⟨by simp, by simp⟩

theorem opCVOf_of (hA : WFamApp) (hS : WFamSymb) (hT : TrRealLie) (hK : CkLevOn) : OpCVOf := by
  intro hRw hCW k r z z' d O U κ Φ u hC hOm hCk hev j hj1 hjn
  obtain ⟨_, hfld, hw⟩ := hRw k r z z' d O U κ Φ u hC hOm hCk
  obtain ⟨Ys, lam, L, cj, hcj, hL, hid, hsym⟩ := hCW k r j hj1 hjn
  choose c hc using hev
  refine ⟨wfam L (VR κ Φ) (-(∑ i, lam i * c (Ys i))), cj, hcj,
    wfam_ok L _ _ j (fun t ht => (hL t ht).1) (fun X => (hfld X).1), ?_, ?_⟩
  · intro x hx
    rw [hA]
    have hgG : κ x ∈ B.GV k r := (hC.2.2.2.2.1 x hx).1
    have hgO : κ x ∈ JF.Om k r z z' := ⟨hgG, hOm x hx⟩
    have e1 := hid ℂ (B.GV k r ∩ Q.OmPlus k r z z') u (hK k r _ _ ℂ u hCk) (κ x) ⟨hgG, hOm x hx⟩ hgG
    have e2 : (L.map fun t => t.1 * vfW (t.2.map (VR κ Φ)) (fun y => u (κ y)) x) =
        (L.map fun t => t.1 • B.Rw t.2 u (κ x)) := by
      refine List.map_congr_left (fun t ht => ?_)
      rw [(hw t.2 (hL t ht).2 ((hL t ht).1.trans hjn) x hx).1, smul_eq_mul]
    rw [e2, ← e1]
    simp only [hc _ _ hgO, smul_eq_mul]
    rw [neg_mul, Finset.sum_mul]
    simp only [mul_assoc, add_neg_cancel]
  · intro x hx ξ Ξ₀ hΞ₀ hcov
    rw [hS d _ L (VR κ Φ) _ j x ξ (fun X => Matrix.trace (Ξ₀ * X)) hj1 (fun t ht X hX => by
      rw [hcov X ((hL t ht).2 X hX), hT k r Ξ₀ X hΞ₀ ((hL t ht).2 X hX)])]
    exact hsym Ξ₀ hΞ₀

theorem opCapROf_of (hA : WFamApp) (hS : WFamSymb) (hT : TrRealLie) (hK : CkLevOn) : OpCapROf := by
  intro hRw hCW k r z z' d O U κ Φ u Bs hC hOm hCk hBs hev j hj1 hjk
  obtain ⟨_, hfld, hw⟩ := hRw k r z z' d O U κ Φ u hC hOm hCk
  obtain ⟨ws, lam, L, cj, hcj, hL, hid, hsym⟩ := hCW k r z' Bs hBs j hj1 hjk
  choose c hc using hev
  have hjn : j ≤ 2 * r + k + 1 := by omega
  refine ⟨wfam L (VR κ Φ) (-(∑ i, lam i * c (ws i))), cj, hcj,
    wfam_ok L _ _ j (fun t ht => (hL t ht).1) (fun X => (hfld X).1), ?_, ?_⟩
  · intro x hx
    rw [hA]
    have hgG : κ x ∈ B.GV k r := (hC.2.2.2.2.1 x hx).1
    have hgO : κ x ∈ JF.Om k r z z' := ⟨hgG, hOm x hx⟩
    have e1 := hid ℂ (B.GV k r ∩ Q.OmPlus k r z z') u (hK k r _ _ ℂ u hCk) (κ x) ⟨hgG, hOm x hx⟩ hgG
    have e2 : (L.map fun t => t.1 * vfW (t.2.map (VR κ Φ)) (fun y => u (κ y)) x) =
        (L.map fun t => t.1 • B.Rw t.2 u (κ x)) := by
      refine List.map_congr_left (fun t ht => ?_)
      rw [(hw t.2 (hL t ht).2 ((hL t ht).1.trans hjn) x hx).1, smul_eq_mul]
    rw [e2, ← e1]
    simp only [hc _ _ hgO, smul_eq_mul]
    rw [neg_mul, Finset.sum_mul]
    simp only [mul_assoc, add_neg_cancel]
  · intro x hx ξ Ξ₀ hΞ₀ hcov
    rw [hS d _ L (VR κ Φ) _ j x ξ (fun X => Matrix.trace (Ξ₀ * X)) hj1 (fun t ht X hX => by
      rw [hcov X ((hL t ht).2 X hX), hT k r Ξ₀ X hΞ₀ ((hL t ht).2 X hX)])]
    exact hsym Ξ₀ hΞ₀

theorem opCapLOf_of (hA : WFamApp) (hS : WFamSymb) (hT : TrRealLie) (hK : CkLevOn) : OpCapLOf := by
  intro hRw hCW k r z z' d O U κ Φ u Bs hC hOm hCk hBs hev j hj1 hjk
  obtain ⟨_, hfld, hw⟩ := hRw k r z z' d O U κ Φ u hC hOm hCk
  obtain ⟨ws, lam, L, cj, hcj, hL, hid, hsym⟩ := hCW k r z Bs hBs j hj1 hjk
  choose c hc using hev
  have hjn : j ≤ 2 * r + k + 1 := by omega
  refine ⟨wfam L (VL κ Φ) (-(∑ i, lam i * c (ws i))), cj, hcj,
    wfam_ok L _ _ j (fun t ht => (hL t ht).1) (fun X => (hfld X).2), ?_, ?_⟩
  · intro x hx
    rw [hA]
    have hgG : κ x ∈ B.GV k r := (hC.2.2.2.2.1 x hx).1
    have hgO : κ x ∈ JF.Om k r z z' := ⟨hgG, hOm x hx⟩
    have e1 := hid ℂ (B.GV k r ∩ Q.OmPlus k r z z') u (hK k r _ _ ℂ u hCk) (κ x) ⟨hgG, hOm x hx⟩ hgG
    have e2 : (L.map fun t => t.1 * vfW (t.2.map (VL κ Φ)) (fun y => u (κ y)) x) =
        (L.map fun t => t.1 • t.2.foldr Q.LdV u (κ x)) := by
      refine List.map_congr_left (fun t ht => ?_)
      rw [(hw t.2 (hL t ht).2 ((hL t ht).1.trans hjn) x hx).2, smul_eq_mul]
    rw [e2, ← e1]
    simp only [hc _ _ hgO, smul_eq_mul]
    rw [neg_mul, Finset.sum_mul]
    simp only [mul_assoc, add_neg_cancel]
  · intro x hx ξ Ξ hΞ hcov
    rw [hS d _ L (VL κ Φ) _ j x ξ (fun X => Matrix.trace (Ξ * X)) hj1 (fun t ht X hX => by
      rw [hcov X ((hL t ht).2 X hX), hT k r Ξ X hΞ ((hL t ht).2 X hX)])]
    exact hsym Ξ hΞ

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix Polynomial
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem nilpotent_of_char_poly : NilOfCharpoly := by
  intro n M h
  have hmon := Matrix.charpoly_monic M
  have hdeg : M.charpoly.natDegree = n := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hX : M.charpoly = (X : ℂ[X]) ^ n := by
    ext i
    rw [Polynomial.coeff_X_pow]
    rcases lt_trichotomy i n with hi | hi | hi
    · rw [if_neg (by omega)]
      have := h (n - i) (by omega) (by omega)
      rwa [show n - (n - i) = i by omega] at this
    · rw [if_pos hi]
      have h1 := hmon.coeff_natDegree
      rw [hdeg] at h1
      rw [hi]; exact h1
    · rw [if_neg (by omega)]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  refine ⟨n, ?_⟩
  have := Matrix.aeval_self_charpoly M
  rwa [hX, map_pow, Polynomial.aeval_X] at this

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section

open Filter Topology

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt

noncomputable section

theorem limZeroN_of_formLimit (Cb : ℝ) : ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (ε A : ℝ) (N : ℕ) (nn : ℝ → ℝ) (Y : Finset ℝ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → 0 < ε → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A m f) →
    Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
    LimZeroN p nn (D.cutF p.T.base χ f ε) Y N := by
  obtain ⟨Cc, hCc⟩ := Formalism.FourierDecayAlt.P.limit_of_module_forms Cb
  refine ⟨Cc, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f χ ε A N nn Y hDD hχ hε hf hfA hA
  have hFL := (hCc Wp Wq P p f χ ε A N (cutN P.k P.r) hDD hχ hε hf hfA hA (fun _ _ => rfl)).2
  intro w hw hN
  have hT := hFL 0 w hw.1 hN [] []
  have hre := (Complex.continuous_re.tendsto _).comp hT
  have e1 : ∀ n : ℕ, TBB.Ew p nn (apx (D.cutF p.T.base χ f ε) n) 0 w [] =
      (p.RR (fun g => cutN P.k P.r n g • D.cutF p.T.base χ f ε g) 0 w [] []).re / TBB.normC nn w :=
    fun n => Formalism.FourierDecayAlt.P.TBBx3.ew_zero_nil p nn _ w
  have e2 : TBB.Ew p nn (D.cutF p.T.base χ f ε) 0 w [] =
      (p.RR (D.cutF p.T.base χ f ε) 0 w [] []).re / TBB.normC nn w :=
    Formalism.FourierDecayAlt.P.TBBx3.ew_zero_nil p nn _ w
  simp only [e1, e2]
  exact hre.div_const _

end

end Formalism.FourierDecayAlt.P.CutBP
end
