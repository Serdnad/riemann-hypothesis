module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle046
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField

namespace GlobalTheory.EX.OB.Bridge

theorem exists_T_of_over {D : D7} {P : PreCh} {Lv : LevCh P} (h : Over D P Lv) (u : D.what₂.Word) :
    ∃ u', (D.mem u).A.T = Lv.T u' := by
  obtain ⟨sp, hT, hY, hA, hV, hz, X, h1, rfl⟩ := h
  have key : ∀ B : Pre, B = Pre.ofCh P Lv sp hT hY hA hV hz → ∀ v : B.Word, ∃ u', B.T v = Lv.T u' := by
    rintro B rfl v
    exact ⟨v, rfl⟩
  obtain ⟨u', hu⟩ := key X.B.toPre h1 u
  exact ⟨u', (X.C.A_T u).trans hu⟩

theorem scale_X'_le_of_log (eps cs : ℝ) (he : 0 < eps) (hc : 0 < cs) : ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks) (T : ℝ),
    s.eps = eps → x0 ≤ s.x → RankVal s R → 0 < T → cs * R.m * s.L ≤ Real.log T → s.X' ≤ T := by
  refine ⟨cs⁻¹ ^ ((2 * eps / 3)⁻¹), fun s R T hs hx hR hT h => ?_⟩
  have hx1 := s.one_lt_alt
  have hx0 : 0 < s.x := by linarith
  have hel := s.eps_lt
  have hm : (1 : ℝ) ≤ R.m := by
    refine le_trans ?_ hR.2.1.1
    rw [Real.one_le_sqrt, Scale.delta1, ← Real.rpow_one_add' hx0.le (by linarith)]
    exact Real.one_le_rpow hx1.le (by linarith)
  have h1 : cs⁻¹ ≤ s.x ^ (2 * eps / 3) := by
    have := Real.rpow_le_rpow (by positivity) hx (show 0 ≤ 2 * eps / 3 by positivity)
    rwa [Real.rpow_inv_rpow (by positivity) (by positivity)] at this
  have h2 : s.L = s.x ^ (2 * eps / 3) * s.x ^ (s.eps / 3) := by
    rw [Scale.L, ← Real.rpow_add hx0, hs]; congr 1; ring
  have h3 : 1 ≤ cs * s.x ^ (2 * eps / 3) := by
    have := mul_le_mul_of_nonneg_left h1 hc.le
    rwa [mul_inv_cancel₀ hc.ne'] at this
  have h4 : 0 < s.x ^ (s.eps / 3) := by positivity
  have h5 : s.x ^ (s.eps / 3) ≤ cs * R.m * s.L := by
    have : cs * R.m * s.L = (cs * s.x ^ (2 * eps / 3) * R.m) * s.x ^ (s.eps / 3) := by rw [h2]; ring
    rw [this]
    exact le_mul_of_one_le_left h4.le (one_le_mul_of_one_le_of_one_le h3 hm)
  rw [Scale.X', ← Real.le_log_iff_exp_le hT]
  exact h5.trans h

theorem scale_one_le_w'' (eps : ℝ) (he : 0 < eps) : ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks),
    s.eps = eps → x0 ≤ s.x → RankVal s R → 1 ≤ s.w'' R.n := by
  obtain ⟨x0, h⟩ := GlobalTheory.scale_poly_comparison eps 0 1 he one_pos
  refine ⟨max x0 4, fun s R hs hx hR => ?_⟩
  have hx4 : 4 ≤ s.x := (le_max_right _ _).trans hx
  have hx0 : 0 < s.x := by linarith
  have hel := s.eps_lt
  have hn : 1 ≤ R.n := Formalism.HC.Frame.ord_pos _
  have h2 : (2 : ℝ) ≤ s.x ^ ((1 : ℝ) / 2) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.le_sqrt_of_sq_le (by linarith)
  have h3 : (R.n : ℝ) ≤ s.x ^ (3 : ℝ) := by
    have a1 : s.x ^ (2 + 8 * s.eps) ≤ s.x ^ ((5 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have a2 : s.x ^ (3 : ℝ) = s.x ^ ((1 : ℝ) / 2) * s.x ^ ((5 : ℝ) / 2) := by
      rw [← Real.rpow_add hx0]; norm_num
    rw [a2]
    exact hR.1.2.trans (mul_le_mul h2 a1 (by positivity) (by positivity))
  have := ((h s hs ((le_max_left _ _).trans hx)).2.2.2.2.2.1 R.n hn h3).1
  simpa using this

end GlobalTheory.EX.OB.Bridge
end

section

noncomputable section

namespace GlobalTheory.EX.DQ

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB NumberField

def TupUsedAt (D : D7) : Prop := ∀ μ : D.what₂.Tup, DV.Used D μ

def GoodAllAt (D : D7) (C : NChoice D) (I : TwIn D) : Prop :=
  ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → I.Ok (C.twI w) ∧
    ∀ a : ℤ, Nat.Coprime a.natAbs (D.ntw.l (C.twI w)) → TwGoodOne D I (C.twI w) (C.sd w) (C.Q w) (C.k' w) (C.psi' w ^ a)

def TwAllAt (D : D7) (C : NChoice D) (T : ThData D) : Prop :=
  TwConjAt D C ∧ ∃ (N0 : D.ntw.Tw → ℕ) (S : ∀ (i' : D.ntw.Tw) (j : ℕ) (b : Bool), Finset (D.nexp.Dat i' j b)),
    GoodAllAt D C ⟨twEOf T, N0, S⟩

def MtStableAt (D : D7) : Prop :=
  ∀ (μ : D.what₂.Tup) (a : 𝓞 D.what₂.LL), ∀ y ∈ (D.what₂.Mtilde μ).carrier,
    D.what₂.embLL (a : D.what₂.LL) • y ∈ (D.what₂.Mtilde μ).carrier

def QD (D : D7) (O : Obj D) : Prop := TupUsedAt D ∧ TwAllAt D O.nch O.xd ∧ MtStableAt D

def withQD (QO : ∀ D : D7, Obj D → Prop) : ∀ D : D7, Obj D → Prop := fun D O => QO D O ∧ QD D O

def TupUsedF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x (_ : Fm.x1 < x), x0 ≤ x → ∀ (i : Fm.Ix x), ∀ μ : (Fm.D x i).what₂.Tup, DV.Used (Fm.D x i) μ

def TwAllF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
    TwConjAt (Fm.D x i) (Fm.ex x hx i).nch ∧
      ∃ (N0 : (Fm.D x i).ntw.Tw → ℕ) (S : ∀ (i' : (Fm.D x i).ntw.Tw) (j : ℕ) (b : Bool), Finset ((Fm.D x i).nexp.Dat i' j b)),
        GoodAllAt (Fm.D x i) (Fm.ex x hx i).nch ⟨twE Fm x hx i, N0, S⟩

def MtStableF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) (μ : (Fm.D x i).what₂.Tup) (a : 𝓞 (Fm.D x i).what₂.LL),
    ∀ y ∈ ((Fm.D x i).what₂.Mtilde μ).carrier,
      (Fm.D x i).what₂.embLL (a : (Fm.D x i).what₂.LL) • y ∈ ((Fm.D x i).what₂.Mtilde μ).carrier

def Duty7 {eps : ℝ} (Fm : FamP eps) : Prop :=
  DC.PageFix Fm ∧ DC.PageWin Fm ∧ DC.globalTwisting_fact Fm ∧ DC.TameDistinctF Fm ∧ DC.WallAll Fm ∧ TupUsedF Fm ∧ TwAllF Fm

def cls7 (QO : ∀ D : D7, Obj D → Prop) : FamClass := DC.cls (ptO (withQD QO))

theorem familyClass_sevenDuties_and_stableLattices (QO : ∀ D : D7, Obj D → Prop) {eps : ℝ} (Fm : FamP eps) (h : cls7 QO Fm) : Duty7 Fm ∧ MtStableF Fm := by
  obtain ⟨a, b, c, d, e⟩ := DC.duty_of_cls _ Fm h
  have hq := DC.classOf_of_cls _ Fm h
  exact ⟨⟨a, b, c, d, e, ⟨Fm.x1, fun x hx _ i => (hq x hx i).2.1⟩, ⟨Fm.x1, fun x _ hx i => (hq x hx i).2.2.1⟩⟩,
    ⟨Fm.x1 + 1, fun x hx i => (hq x (by linarith) i).2.2.2⟩⟩

theorem familyClass_points_satisfy_objectProperty (QO : ∀ D : D7, Obj D → Prop) {eps : ℝ} (Fm : FamP eps) (h : cls7 QO Fm) : classOf (ptO QO) Fm :=
  fun x hx i => (DC.classOf_of_cls _ Fm h x hx i).1

theorem TwAllAt.twAt {D : D7} {C : NChoice D} {T : ThData D} (h : TwAllAt D C T) : LocalQuadraticParts.TWAt D C T := by
  obtain ⟨hc, N0, S, hS⟩ := h
  refine ⟨hc, N0, S, fun w hw => ⟨(hS w hw).1, ?_⟩⟩
  have := (hS w hw).2 1 (by simp)
  rwa [zpow_one] at this

end GlobalTheory.EX.DQ

end
end
