module

public import Formalism.LocalToGlobal.CharacterGerms.Bundle002
public import Formalism.FormalGroupLog.FormalGroupLogProofs.ChainRule
public import Formalism.LocalToGlobal.CharacterGerms.Bundle010
public import Formalism.LocalToGlobal.CharacterGerms.Bundle009
public import Formalism.LocalToGlobal.CharacterGerms.CoeffSubstEqSum
public import Formalism.LocalToGlobal.CharacterGerms.RowTieDefs
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePGerm
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

section

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

namespace OActLog

open PartialDerivEval LogEx

variable {C : Type} [Field C] [CharZero C] {d : ℕ}

theorem ev_zero_pt {n : ℕ} (g : PS C 1 d) : ev (n := n) ![(0 : Pt C n d)] g = MvPowerSeries.C (constantCoeff g) := by
  have hz : (fun p : Fin 1 × Fin d => (![0] : Fin 1 → Pt C n d) p.1 p.2) = 0 := by
    funext p
    obtain ⟨k, b⟩ := p
    fin_cases k
    rfl
  rw [ev, hz, subst_zero_eq_C_constantCoeff, map_C]
  simp

theorem cc_pderiv {σ : Type} (i : σ) (f : MvPowerSeries σ C) :
    constantCoeff (pderiv (R := C) i f) = coeff (Finsupp.single i 1) f := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv]
  simp

theorem add_zero_of (G : FGLaw C d) (Q : PS C 1 d)
    (hQ : ev (n := 2) ![G.F] Q = ev (n := 2) ![pt C d 0] Q + ev (n := 2) ![pt C d 1] Q)
    (hlin : ∀ k, coeff (Finsupp.single ((0 : Fin 1), k) 1) Q = 0) (hc : constantCoeff Q = 0) : Q = 0 := by
  classical
  let A : Matrix (Fin d) (Fin d) (PS C 1 d) := Matrix.of fun k b =>
    ev (n := 1) ![pt C d 0, 0] (pderiv (R := C) ((1 : Fin 2), k) (G.F b))
  let u : Fin d → PS C 1 d := fun b => pderiv (R := C) ((0 : Fin 1), b) Q
  have hX (k b : Fin d) :
      pderiv (R := C) ((0 : Fin 1), k) (pt C d 0 b) = if k = b then 1 else 0 := by
    by_cases h : k = b
    · subst b
      simp [pt]
    · rw [ite_eq_right h]
      exact pderiv_X_of_ne (by simpa using Ne.symm h)
  have hA : (constantCoeff : PS C 1 d →+* C).mapMatrix A = 1 := by
    ext k b
    have hz := constant_zero_zero_point (pt C (n := 1) d 0) (coordinate_point_constantCoeff 0)
    have h := congrArg (pderiv (R := C) ((0 : Fin 1), k)) (G.unit b)
    change pderiv ((0 : Fin 1), k) (ev ![0, pt C d 0] (G.F b)) =
      pderiv ((0 : Fin 1), k) (pt C d 0 b) at h
    rw [ev, Formalism.G.LogCR.pderiv_subst
      (a := fun p : Fin 2 × Fin d => (![0, pt C d 0] : Fin 2 → Pt C 1 d) p.1 p.2)
      (fun p => hz p.1 p.2),
      Fintype.sum_prod_type, Fin.sum_univ_two] at h
    change (∑ j, ev ![0, pt C d 0] (pderiv ((0 : Fin 2), j) (G.F b)) *
        pderiv ((0 : Fin 1), k) (0 : PS C 1 d)) +
      (∑ j, ev ![0, pt C d 0] (pderiv ((1 : Fin 2), j) (G.F b)) *
        pderiv ((0 : Fin 1), k) (pt C d 0 j)) = _ at h
    simp only [map_zero, mul_zero, Finset.sum_const_zero, zero_add, hX, mul_ite, mul_one,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true] at h
    have hcc := congrArg constantCoeff h
    rw [constantCoeff_ev hz, apply_ite constantCoeff, map_one, map_zero] at hcc
    simpa only [RingHom.mapMatrix_apply, Matrix.map_apply, A, Matrix.of_apply, Matrix.one_apply,
      constantCoeff_ev constant_zero_first_zero] using hcc
  have hdet : IsUnit A.det := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff, RingHom.map_det, hA, Matrix.det_one]
    exact isUnit_one
  have hchain (P : Pt C 2 d) (hP : ∀ j, constantCoeff (P j) = 0) (q : Fin 2 × Fin d) :
      pderiv q (ev ![P] Q) = ∑ b, ev ![P] (u b) * pderiv q (P b) := by
    unfold ev
    rw [Formalism.G.LogCR.pderiv_subst
      (a := fun p : Fin 1 × Fin d => (![P] : Fin 1 → Pt C 2 d) p.1 p.2)
      (fun p => z0_1 P hP p.1 p.2) Q q,
      Fintype.sum_prod_type, Fin.sum_univ_one]
    rfl
  have hrow : A.mulVec u = 0 := by
    funext k
    have h0 : pderiv ((1 : Fin 2), k) (ev ![pt C d 0] Q) = 0 := by
      rw [hchain _ (coordinate_point_constantCoeff 0)]
      exact Finset.sum_eq_zero fun b _ => by simp [pt]
    have h1 : pderiv ((1 : Fin 2), k) (ev ![pt C d 1] Q) = ev ![pt C d 1] (u k) := by
      rw [hchain _ (coordinate_point_constantCoeff 1), Finset.sum_eq_single k]
      · simp [pt]
      · intro b _ hb
        rw [show pt C d 1 b = X ((1 : Fin 2), b) from rfl, pderiv_X_of_ne (by simp [hb]), mul_zero]
      · simp
    have D := congrArg (fun g => ev (n := 1) ![pt C d 0, 0] (pderiv (R := C) ((1 : Fin 2), k) g)) hQ
    rw [map_add (f := _), h0, h1, zero_add, hchain G.F G.const] at D
    rw [ev_sum constant_zero_first_zero] at D
    simp only [PartialDerivEval.ev_mul constant_zero_first_zero, eval_group_law_at_zero G] at D
    rw [eval_eval_single (z0_1 (pt C d 1) (coordinate_point_constantCoeff 1)) constant_zero_first_zero (a' := (0 : Pt C 1 d)) (fun j => ev_X constant_zero_first_zero 1 j), ev_zero_pt,
      show u k = pderiv ((0 : Fin 1), k) Q from rfl, cc_pderiv, hlin k, map_zero] at D
    change (∑ b, A k b * u b) = 0
    change (∑ b, u b * A k b) = 0 at D
    simpa only [mul_comm (A k _) (u _)] using D
  have hd : u = 0 := by
    have h := congrArg (fun v => (A⁻¹).mulVec v) hrow
    change (A⁻¹).mulVec (A.mulVec u) = (A⁻¹).mulVec 0 at h
    rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hdet, Matrix.one_mulVec, Matrix.mulVec_zero] at h
  apply pderiv.ext
  · intro q
    obtain ⟨q1, q2⟩ := q
    fin_cases q1
    rw [map_zero]
    exact congrFun hd q2
  · rw [hc, map_zero]

def linM (φ : Pt C 1 d) (i j : Fin d) : C := coeff (Finsupp.single ((0 : Fin 1), j) 1) (φ i)

theorem linN_coeff {lg : Pt C 1 d} (hlin : LinN lg) (j b : Fin d) :
    coeff (Finsupp.single ((0 : Fin 1), b) 1) (lg j) = if b = j then 1 else 0 := by
  rw [hlin j _ (by rw [Finsupp.degree_single]), coeff_X]
  by_cases h : b = j
  · subst h; simp
  · rw [if_neg h, if_neg]
    intro e
    exact h (congrArg Prod.snd ((Finsupp.single_left_inj one_ne_zero).mp e))

theorem log_endo (G : FGLaw C d) (lg : Pt C 1 d) (hlin : LinN lg)
    (hadd : ∀ i, ev (n := 2) ![addOf G.F (pt C d 0) (pt C d 1)] (lg i) =
      ev (n := 2) ![pt C d 0] (lg i) + ev (n := 2) ![pt C d 1] (lg i))
    (φ : Pt C 1 d) (hφ0 : ∀ i, constantCoeff (φ i) = 0)
    (hφ : comp1 φ (addOf G.F (pt C (n := 2) d 0) (pt C (n := 2) d 1)) =
      addOf G.F (comp1 φ (pt C (n := 2) d 0)) (comp1 φ (pt C (n := 2) d 1)))
    (i : Fin d) : comp1 lg φ i = ∑ j, MvPowerSeries.C (linM φ i j) * lg j := by
  have haddF : addOf G.F (pt C d 0) (pt C d 1) = (G.F : Pt C 2 d) := funext fun j => eval_points_two (G.F j)
  have hF : ∀ j, ev (n := 2) ![G.F] (lg j) = ev (n := 2) ![pt C d 0] (lg j) + ev (n := 2) ![pt C d 1] (lg j) := by
    intro j; rw [← haddF]; exact hadd j
  have hφ1 : Z0 (![φ] : Fin 1 → Pt C 1 d) := z0_1 φ hφ0
  have hFz : Z0 (![G.F] : Fin 1 → Pt C 2 d) := z0_1 G.F G.const
  have hP0 : Z0 (![pt C d 0] : Fin 1 → Pt C 2 d) := z0_1 _ (coordinate_point_constantCoeff 0)
  have hP1 : Z0 (![pt C d 1] : Fin 1 → Pt C 2 d) := z0_1 _ (coordinate_point_constantCoeff 1)
  set A : Pt C 2 d := comp1 φ (pt C (n := 2) d 0) with hA
  set B : Pt C 2 d := comp1 φ (pt C (n := 2) d 1) with hB
  have hA0 : ∀ j, constantCoeff (A j) = 0 := fun j => const_ev hP0 (hφ0 j)
  have hB0 : ∀ j, constantCoeff (B j) = 0 := fun j => const_ev hP1 (hφ0 j)
  have hAB : Z0 (![A, B] : Fin 2 → Pt C 2 d) := by
    intro k j; fin_cases k
    · exact hA0 j
    · exact hB0 j

  have hlgAB : ∀ j, ev (n := 2) ![addOf G.F A B] (lg j) = ev (n := 2) ![A] (lg j) + ev (n := 2) ![B] (lg j) := by
    intro j
    have h := congrArg (ev (n := 2) ![A, B]) (hF j)
    have hFc : ∀ k, constantCoeff (G.F k) = 0 := G.const
    rw [ev_add hAB, eval_eval_single hFz hAB (a' := addOf G.F A B) (fun k => rfl),
      eval_eval_single hP0 hAB (a' := A) (fun k => ev_X hAB 0 k),
      eval_eval_single hP1 hAB (a' := B) (fun k => ev_X hAB 1 k)] at h
    exact h

  have hcomp : ev (n := 2) ![G.F] (comp1 lg φ i) =
      ev (n := 2) ![pt C d 0] (comp1 lg φ i) + ev (n := 2) ![pt C d 1] (comp1 lg φ i) := by
    have e1 : ev (n := 2) ![G.F] (comp1 lg φ i) = ev (n := 2) ![comp1 φ G.F] (lg i) :=
      eval_eval_single hφ1 hFz (a' := comp1 φ G.F) (fun k => rfl) (lg i)
    have e2 : comp1 φ G.F = addOf G.F A B :=
      calc comp1 φ G.F = comp1 φ (addOf G.F (pt C d 0) (pt C d 1)) := by rw [haddF]
        _ = addOf G.F A B := hφ
    have e3 : ev (n := 2) ![pt C d 0] (comp1 lg φ i) = ev (n := 2) ![A] (lg i) :=
      eval_eval_single hφ1 hP0 (a' := A) (fun k => rfl) (lg i)
    have e4 : ev (n := 2) ![pt C d 1] (comp1 lg φ i) = ev (n := 2) ![B] (lg i) :=
      eval_eval_single hφ1 hP1 (a' := B) (fun k => rfl) (lg i)
    rw [e1, e2, e3, e4, hlgAB]
  have hQ := add_zero_of G (comp1 lg φ i - ∑ j, MvPowerSeries.C (linM φ i j) * lg j) (by
      rw [ev_sub hFz, ev_sub hP0, ev_sub hP1, ev_sum hFz, ev_sum hP0, ev_sum hP1, hcomp]
      simp only [PartialDerivEval.ev_mul hFz, PartialDerivEval.ev_mul hP0,
        PartialDerivEval.ev_mul hP1, PartialDerivEval.ev_C, hF, mul_add, Finset.sum_add_distrib]
      ring)
    (by
      intro k

      rw [map_sub, map_sum]
      simp only [coeff_C_mul, linN_coeff hlin, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]

      rw [← cc_pderiv, show comp1 lg φ i = ev ![φ] (lg i) from rfl]
      have hchain :
          pderiv ((0 : Fin 1), k) (ev ![φ] (lg i)) =
            ∑ b, ev ![φ] (pderiv ((0 : Fin 1), b) (lg i)) * pderiv ((0 : Fin 1), k) (φ b) := by
        unfold ev
        rw [Formalism.G.LogCR.pderiv_subst
          (a := fun p : Fin 1 × Fin d => (![φ] : Fin 1 → Pt C 1 d) p.1 p.2)
          (fun p => hφ1 p.1 p.2),
          Fintype.sum_prod_type, Fin.sum_univ_one]
        rfl

      rw [hchain, map_sum]
      simp only [map_mul, constantCoeff_ev hφ1, cc_pderiv, linN_coeff hlin, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      unfold linM
      ring)
    (by

      rw [map_sub, map_sum, show comp1 lg φ i = ev ![φ] (lg i) from rfl, constantCoeff_ev hφ1, linN_const hlin]
      simp [linN_const hlin])
  exact sub_eq_zero.mp hQ

end OActLog

end Formalism.L2.FormalSeriesBounds
end
end

section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

def IsIU (V : VF C) {σ : Type} (U : MvPowerSeries σ C) : Prop :=
  IntS V U ∧ V.v (MvPowerSeries.constantCoeff U) = 0

theorem IsIU.one {σ : Type} : IsIU V (1 : MvPowerSeries σ C) := by
  refine ⟨fun μ => ?_, ?_⟩
  · unfold VF.Ge
    rw [MvPowerSeries.coeff_one]
    split_ifs
    · rw [AddValuation.map_one]; exact le_rfl
    · rw [AddValuation.map_zero]; exact le_top
  · rw [map_one, AddValuation.map_one]

theorem IsIU.mul {σ : Type} {U U' : MvPowerSeries σ C} (h : IsIU V U) (h' : IsIU V U') : IsIU V (U * U') :=
  ⟨IntS.mul h.1 h'.1, by rw [map_mul, AddValuation.map_mul, h.2, h'.2, add_zero]⟩

section Defs

variable (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o))

end Defs

end Formalism.L2.FormalSeriesBounds
end
end

section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ RowTiePE0

namespace LimTy

variable {C : Type} [Field C] {V : VF C}

theorem tendsS_sum {σ ι : Type} (S : Finset ι) {f : ι → ℕ → MvPowerSeries σ C} {F : ι → MvPowerSeries σ C}
    (h : ∀ i ∈ S, TendsS V (f i) (F i)) : TendsS V (fun k => ∑ i ∈ S, f i k) (∑ i ∈ S, F i) := by
  intro μ

  simp only [map_sum]
  exact Tends.sum S (fun i hi => h i hi μ)

theorem tendsS_smul {σ : Type} (c : C) {f : ℕ → MvPowerSeries σ C} {F : MvPowerSeries σ C}
    (h : TendsS V f F) : TendsS V (fun k => c • f k) (c • F) := by
  intro μ
  first
    | simp only [map_smul, smul_eq_mul]
    | simp only [MvPowerSeries.coeff_smul]
  exact (tends_const c).mul (h μ)

theorem tendsS_ite {σ : Type} (P : Prop) [Decidable P] {f : ℕ → MvPowerSeries σ C} {F : MvPowerSeries σ C}
    (h : TendsS V f F) : TendsS V (fun k => if P then f k else 0) (if P then F else 0) := by
  split_ifs
  · exact h
  · exact TendsS.const 0

theorem coeff_tyS_mv (l : ℕ) (b : ℕ → C) (μ : Unit →₀ ℕ) :
    MvPowerSeries.coeff μ (tyS l b) = ∑ s ∈ Finset.range (μ () + 1), if l ^ s = μ () then b s else 0 := rfl

theorem tendsS_tyS (l : ℕ) {a : ℕ → ℕ → C} {a' : ℕ → C} (h : ∀ s, Tends V (fun k => a k s) (a' s)) :
    TendsS V (fun k => tyS l (a k)) (tyS l a') := by
  intro μ
  simp only [coeff_tyS_mv]
  refine Tends.sum _ (fun s _ => ?_)
  split_ifs
  · exact h s
  · exact tends_const 0

theorem tendsP {f : ℕ → PowerSeries C} {F : PowerSeries C} (h : TendsS V f F) (n : ℕ) :
    Tends V (fun k => PowerSeries.coeff n (f k)) (PowerSeries.coeff n F) :=
  h (Finsupp.single () n)

private theorem eq_zero_of_tends_const_zero {y : C} (h : Tends V (fun _ => (0 : C)) y) : y = 0 := by
  by_contra hy
  have hne : V.v y ≠ ⊤ := fun ht => hy ((AddValuation.top_iff V.v).mp ht)
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hne
  obtain ⟨n0, hn0⟩ := h (r + 1)
  have h1 : ((r + 1 : ℝ) : WithTop ℝ) ≤ V.v (y - 0) := hn0 n0 le_rfl
  rw [sub_zero, ← hr] at h1
  have h2 := WithTop.coe_le_coe.mp h1
  linarith

private theorem ge_zero_of_tends_of_forall_ge_zero {s : ℕ → C} {y : C} (h : Tends V s y) (hs : ∀ k, V.Ge 0 (s k)) :
    V.Ge 0 y := by
  obtain ⟨n0, hn0⟩ := h 0
  have h1 : ((0 : ℝ) : WithTop ℝ) ≤ V.v (y - s n0) := hn0 n0 le_rfl
  have h2 : ((0 : ℝ) : WithTop ℝ) ≤ V.v (s n0) := hs n0
  have e : y = (y - s n0) + s n0 := by ring
  show ((0 : ℝ) : WithTop ℝ) ≤ V.v y
  rw [e]
  exact le_trans (le_min h1 h2) (V.v.map_add _ _)

theorem isCv_lim {σ : Type} {γ : ℕ → σ → PowerSeries C} {Γ : σ → PowerSeries C}
    (h : ∀ i, TendsS V (fun k => γ k i) (Γ i)) (hc : ∀ k, IsCv V (γ k)) : IsCv V Γ := by
  intro i
  have hcoef : ∀ n, Tends V (fun k => PowerSeries.coeff n (γ k i)) (PowerSeries.coeff n (Γ i)) :=
    fun n => tendsP (h i) n
  refine ⟨?_, fun n => ge_zero_of_tends_of_forall_ge_zero (hcoef n) (fun k => (hc k i).2 n)⟩
  have e : ∀ k, PowerSeries.coeff 0 (γ k i) = 0 := fun k => by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact (hc k i).1
  have h0 := hcoef 0
  simp only [e] at h0
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact eq_zero_of_tends_const_zero h0

theorem constantCoeff_lin {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type}
    (X : RawChart C d I κ) (l : ℕ) (hl : 2 ≤ l) (g : Fin 2) (b : I g → ℕ → C) (i : κ) :
    MvPowerSeries.constantCoeff (∑ c : I g, X.u g c i • tyS l (b c)) = 0 := by

  rw [map_sum]
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  first
    | rw [map_smul, coeff_tyS_mv]
    | rw [MvPowerSeries.coeff_smul, coeff_tyS_mv]
  simp

private theorem hasSubst_of_constantCoeff_eq_zero' {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) : MvPowerSeries.HasSubst a := by
  first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero ha
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun s => by rw [ha s]; exact IsNilpotent.zero)
    | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun s => by rw [ha s]; exact IsNilpotent.zero)

theorem lim_mem {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)
    (hl : 2 ≤ V.l)
    (hlg0 : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0) (hex0 : ∀ i, MvPowerSeries.constantCoeff (X.ex i) = 0)
    (hlgex : ∀ i, MvPowerSeries.subst X.ex (X.lg i) = MvPowerSeries.X i)
    (hexlg : ∀ i, MvPowerSeries.subst X.lg (X.ex i) = MvPowerSeries.X i)
    (g : Fin 2) (x : ℕ → ℕ → I g ⊕ JJ I g → C) (x' : ℕ → I g ⊕ JJ I g → C)
    (hx : ∀ k, x k ∈ X.TySet V g) (hlim : VLim V x x') : x' ∈ X.TySet V g := by
  classical
  unfold RawChart.TySet at hx ⊢
  simp only [Set.mem_setOf_eq] at hx ⊢
  choose γk lamk hγk hlamk hA hB using hx
  obtain ⟨T, hTdef⟩ : ∃ T : ℕ → κ → PowerSeries C,
      T = fun k i => ∑ c : I g, X.u g c i • tyS V.l (fun s => x k s (Sum.inl c)) := ⟨_, rfl⟩
  obtain ⟨T', hT'def⟩ : ∃ T' : κ → PowerSeries C,
      T' = fun i => ∑ c : I g, X.u g c i • tyS V.l (fun s => x' s (Sum.inl c)) := ⟨_, rfl⟩
  have hT0 : ∀ k i, MvPowerSeries.constantCoeff (T k i) = 0 := by
    intro k i
    rw [hTdef]
    exact constantCoeff_lin X V.l hl g (fun c s => x k s (Sum.inl c)) i
  have hT'0 : ∀ i, MvPowerSeries.constantCoeff (T' i) = 0 := by
    intro i
    rw [hT'def]
    exact constantCoeff_lin X V.l hl g (fun c s => x' s (Sum.inl c)) i
  have hTlim : ∀ i, TendsS V (fun k => T k i) (T' i) := by
    intro i
    simp only [hTdef, hT'def]
    exact tendsS_sum Finset.univ (fun c _ => tendsS_smul (X.u g c i)
      (tendsS_tyS (a := fun k s => x k s (Sum.inl c)) (a' := fun s => x' s (Sum.inl c)) V.l
        (fun s w => hlim w s (Sum.inl c))))
  have hHSlg : MvPowerSeries.HasSubst X.lg := hasSubst_of_constantCoeff_eq_zero' hlg0
  have hHSex : MvPowerSeries.HasSubst X.ex := hasSubst_of_constantCoeff_eq_zero' hex0
  have hHS : ∀ k, MvPowerSeries.HasSubst (γk k) := fun k =>
    hasSubst_of_constantCoeff_eq_zero' (fun i => (hγk k i).1)
  have hHST' : MvPowerSeries.HasSubst T' := hasSubst_of_constantCoeff_eq_zero' hT'0
  have hγeq : ∀ k i, γk k i = MvPowerSeries.subst (T k) (X.ex i) := by
    intro k i
    have e1 : T k = fun j => MvPowerSeries.subst (γk k) (X.lg j) := by
      funext j
      rw [hTdef]
      exact (hA k j).symm
    rw [e1, ← MvPowerSeries.subst_comp_subst_apply hHSlg (hHS k), hexlg, MvPowerSeries.subst_X (hHS k)]
  obtain ⟨γ', hγ'def⟩ : ∃ γ' : κ → PowerSeries C, γ' = fun i => MvPowerSeries.subst T' (X.ex i) :=
    ⟨_, rfl⟩
  have hγlim : ∀ i, TendsS V (fun k => γk k i) (γ' i) := by
    intro i
    simp only [hγeq, hγ'def]
    exact TendsS.subst (fun k j => hT0 k j) hT'0 hTlim (TendsS.const _)
  have hγ' : IsCv V γ' := isCv_lim hγlim hγk
  have hγ'0 : ∀ i, MvPowerSeries.constantCoeff (γ' i) = 0 := fun i => (hγ' i).1
  have hrel : ∀ i, alongCv γ' (X.lg i) = T' i := by
    intro i
    unfold alongCv
    rw [hγ'def, ← MvPowerSeries.subst_comp_subst_apply hHSex hHST', hlgex, MvPowerSeries.subst_X hHST']
  obtain ⟨lam', hlam'def⟩ : ∃ lam' : JJ I g → PowerSeries C, lam' = fun q =>
      tyS V.l (fun s => x' s (Sum.inr q)) + alongCv γ' (X.sg (X.u (1 - g) q)) -
        ∑ c : I g, (if X.ty g c = X.ty (1 - g) q then
          X.sg1 (X.u g c) (X.u (1 - g) q) • tyS V.l (fun s => x' s (Sum.inl c)) else 0) := ⟨_, rfl⟩
  have hlamlim : ∀ q, TendsS V (fun k => lamk k q) (lam' q) := by
    intro q
    have e : ∀ k, lamk k q = tyS V.l (fun s => x k s (Sum.inr q)) + alongCv (γk k) (X.sg (X.u (1 - g) q)) -
        ∑ c : I g, (if X.ty g c = X.ty (1 - g) q then
          X.sg1 (X.u g c) (X.u (1 - g) q) • tyS V.l (fun s => x k s (Sum.inl c)) else 0) := by
      intro k
      rw [hB k q]
      ring
    simp only [e, hlam'def]
    refine TendsS.sub (TendsS.add ?_ ?_) ?_
    · exact tendsS_tyS (a := fun k s => x k s (Sum.inr q)) (a' := fun s => x' s (Sum.inr q)) V.l
        (fun s w => hlim w s (Sum.inr q))
    · unfold alongCv
      exact TendsS.subst (fun k j => (hγk k j).1) hγ'0 hγlim (TendsS.const _)
    · refine tendsS_sum _ (fun c _ => ?_)
      split_ifs
      · exact tendsS_smul _ (tendsS_tyS (a := fun k s => x k s (Sum.inl c))
          (a' := fun s => x' s (Sum.inl c)) V.l (fun s w => hlim w s (Sum.inl c)))
      · exact TendsS.const 0
  refine ⟨γ', lam', hγ', isCv_lim hlamlim hlamk, fun i => ?_, fun q => ?_⟩
  · rw [hrel i, hT'def]
  · simp only [hlam'def]
    ring

end LimTy

end Formalism.L2.FormalSeriesBounds
end
end
