module

public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.Bundle005
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.Basify
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

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

theorem nb_sum_mod_div {n : ℕ} (f : Fin n → ℕ) (P : ℕ) : ∑ c, f c = ∑ c, f c % P + P * ∑ c, f c / P := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun c _ => (Nat.mod_add_div _ _).symm

theorem nb_key {n : ℕ} (P a : ℕ) (f : Fin n → ℕ) (B : ℕ) (h : P * a + ∑ c, f c = B) :
    B = P * (a + ∑ c, f c / P) + ∑ c, f c % P := by
  rw [← h, nb_sum_mod_div f P]
  ring

theorem nb_q_le (Q P r a : ℕ) (hr : r < P) (h : Q * P ≤ a) : Q ≤ a - r := by
  rcases Q with _ | q
  · exact Nat.zero_le _
  · have hP : 1 ≤ P := by omega
    have hq : q ≤ q * P := Nat.le_mul_of_pos_right q hP
    have : (q + 1) * P = q * P + P := by ring
    omega

theorem nb_div_le (a P n : ℕ) (hP : 0 < P) (h : a < (n + 1) * P) : a / P ≤ n :=
  Nat.lt_succ_iff.1 ((Nat.div_lt_iff_lt_mul hP).2 h)

section NB

variable (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (ju : Fin (X.seg C0 CE1 CE2 j).t → ℕ) (jp : ℕ)
  (du : Fin (2 * segS X.TT j + 1) → ℕ) (A : MonH X)

theorem nb_Ppos (hp : 0 < X.p) (i : Fin (segS X.TT j)) : 0 < (X.seg C0 CE1 CE2 j).P X.p i := by
  unfold SegData.P
  exact pow_pos hp _

theorem nb_coarseA (hp : 0 < X.p)
    (dz : ∀ i : Fin (segS X.TT j), (X.seg C0 CE1 CE2 j).P X.p i * (jE (X.seg C0 CE1 CE2 j) ju i.val + du (chW i)) +
      ∑ c, A ((topOdd X j i, true), c) = (X.seg C0 CE1 CE2 j).bTop i) (i : Fin (segS X.TT j)) :
    coarseA X.p (X.seg C0 CE1 CE2 j) (segmentBlockOfMonomial C0 CE1 CE2 X j ju jp du A) i =
      jE (X.seg C0 CE1 CE2 j) ju i.val + du (chW i) + z0A C0 CE1 CE2 X j A i + ∑ c, ezA C0 CE1 CE2 X j A i c := by
  have hP := nb_Ppos C0 CE1 CE2 X j hp i
  have h := nb_key _ _ (fun c => A ((topOdd X j i, true), c)) _ (dz i)
  show ((X.seg C0 CE1 CE2 j).bTop i - ∑ c, A ((topOdd X j i, true), c) % (X.seg C0 CE1 CE2 j).P X.p i) /
    (X.seg C0 CE1 CE2 j).P X.p i = _
  rw [h, Nat.add_sub_cancel, Nat.mul_div_cancel_left _ hP, Fin.sum_univ_succ]
  unfold z0A ezA
  ring

theorem nb_coarseC (hp : 0 < X.p)
    (dy : ∀ i : Fin (segS X.TT j), (X.seg C0 CE1 CE2 j).P X.p i * (jE (X.seg C0 CE1 CE2 j) ju i.val + du (chE i)) +
      ∑ c, A ((topOdd X j i, false), c) = segATop X.TT X.aT j i) (i : Fin (segS X.TT j)) :
    coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segmentBlockOfMonomial C0 CE1 CE2 X j ju jp du A) i =
      jE (X.seg C0 CE1 CE2 j) ju i.val + du (chE i) + y0A C0 CE1 CE2 X j A i + ∑ c, eyA C0 CE1 CE2 X j A i c := by
  have hP := nb_Ppos C0 CE1 CE2 X j hp i
  have h := nb_key _ _ (fun c => A ((topOdd X j i, false), c)) _ (dy i)
  show (segATop X.TT X.aT j i - ∑ c, A ((topOdd X j i, false), c) % (X.seg C0 CE1 CE2 j).P X.p i) /
    (X.seg C0 CE1 CE2 j).P X.p i = _
  rw [h, Nat.add_sub_cancel, Nat.mul_div_cancel_left _ hP, Fin.sum_univ_succ]
  unfold y0A eyA
  ring

theorem nb_digits (hp : 0 < X.p)
    (dz : ∀ i : Fin (segS X.TT j), (X.seg C0 CE1 CE2 j).P X.p i * (jE (X.seg C0 CE1 CE2 j) ju i.val + du (chW i)) +
      ∑ c, A ((topOdd X j i, true), c) = (X.seg C0 CE1 CE2 j).bTop i)
    (dy : ∀ i : Fin (segS X.TT j), (X.seg C0 CE1 CE2 j).P X.p i * (jE (X.seg C0 CE1 CE2 j) ju i.val + du (chE i)) +
      ∑ c, A ((topOdd X j i, false), c) = segATop X.TT X.aT j i) :
    DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segmentBlockOfMonomial C0 CE1 CE2 X j ju jp du A) := by
  refine ⟨fun i c => ⟨Nat.mod_lt _ (nb_Ppos C0 CE1 CE2 X j hp i), Nat.mod_lt _ (nb_Ppos C0 CE1 CE2 X j hp i)⟩,
    fun i => ?_, fun i => ?_⟩
  · have h := nb_key _ _ (fun c => A ((topOdd X j i, true), c)) _ (dz i)
    show ∑ c, A ((topOdd X j i, true), c) % (X.seg C0 CE1 CE2 j).P X.p i ≤ (X.seg C0 CE1 CE2 j).bTop i ∧
      (X.seg C0 CE1 CE2 j).P X.p i ∣
        (X.seg C0 CE1 CE2 j).bTop i - ∑ c, A ((topOdd X j i, true), c) % (X.seg C0 CE1 CE2 j).P X.p i
    rw [h, Nat.add_sub_cancel]
    exact ⟨Nat.le_add_left _ _, Dvd.intro _ rfl⟩
  · have h := nb_key _ _ (fun c => A ((topOdd X j i, false), c)) _ (dy i)
    show ∑ c, A ((topOdd X j i, false), c) % (X.seg C0 CE1 CE2 j).P X.p i ≤ segATop X.TT X.aT j i ∧
      (X.seg C0 CE1 CE2 j).P X.p i ∣
        segATop X.TT X.aT j i - ∑ c, A ((topOdd X j i, false), c) % (X.seg C0 CE1 CE2 j).P X.p i
    rw [h, Nat.add_sub_cancel]
    exact ⟨Nat.le_add_left _ _, Dvd.intro _ rfl⟩

theorem nb_oEff (i : Fin (segS X.TT j)) :
    oEff (X.seg C0 CE1 CE2 j) (segmentBlockOfMonomial C0 CE1 CE2 X j ju jp du A) i =
      jE (X.seg C0 CE1 CE2 j) ju i.val + du (chW i) + y0A C0 CE1 CE2 X j A i + ∑ c, ezA C0 CE1 CE2 X j A i c := by
  simp only [oEff, segmentBlockOfMonomial]
  split_ifs with h
  · have h0 : jE (X.seg C0 CE1 CE2 j) ju i.val = 0 := by
      unfold jE
      rw [dite_eq_right (by omega)]
    rw [h0]
    ring
  · rfl

theorem nb_ord :
    blockOrd X.p (X.seg C0 CE1 CE2 j) (segmentBlockOfMonomial C0 CE1 CE2 X j ju jp du A) = nuSeg C0 CE1 CE2 X j ju jp du A := by
  unfold blockOrd nuSeg
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [nb_oEff, Fin.sum_univ_succ]
  have e1 := nb_sum_mod_div (fun c : Fin X.m => A ((topOdd X j i, true), c.succ)) ((X.seg C0 CE1 CE2 j).P X.p i)
  have e2 := Nat.mod_add_div (A ((topOdd X j i, false), 0)) ((X.seg C0 CE1 CE2 j).P X.p i)
  simp only [Fin.succ_ne_zero, if_false, if_true, segmentBlockOfMonomial, y0A, ezA] at e1 e2 ⊢
  simp only [Fin.val_zero, Fin.val_succ, Nat.add_one_ne_zero, if_true, if_false, zero_add]
  linarith

theorem nb_ez_le (hp : 0 < X.p) (b : SegBlock (segS X.TT j) X.m)
    (hd : DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b) (Qe : ℕ) (i : Fin (segS X.TT j))
    (h : ∑ c : Fin X.m, (A ((topOdd X j i, true), c.succ) - b.rz i c.succ) ≤ Qe) :
    ∑ c, ezA C0 CE1 CE2 X j A i c ≤ Qe := by
  obtain ⟨hlt, -, -⟩ := hd
  refine le_trans (Finset.sum_le_sum fun c _ => ?_) h
  exact nb_q_le _ _ _ _ (hlt i c.succ).1 (Nat.div_mul_le_self _ _)

theorem block_y_zero_le_of_bound (hp : 0 < X.p) (b : SegBlock (segS X.TT j) X.m)
    (hd : DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b) (Qe : ℕ) (hQ : 1 ≤ Qe) (i : Fin (segS X.TT j)) (t : ℕ)
    (h : A ((topOdd X j i, false), 0) ≤ b.ry i 0 + (X.seg C0 CE1 CE2 j).P X.p i * t + Qe) :
    y0A C0 CE1 CE2 X j A i ≤ t + Qe := by
  have hP : 0 < (X.seg C0 CE1 CE2 j).P X.p i := nb_Ppos C0 CE1 CE2 X j hp i
  have hr := (hd.1 i 0).2
  apply nb_div_le _ _ _ hP
  have : Qe ≤ Qe * (X.seg C0 CE1 CE2 j).P X.p i := Nat.le_mul_of_pos_right Qe hP
  nlinarith

theorem block_y_zero_le_z_zero (hp : 0 < X.p) (b : SegBlock (segS X.TT j) X.m)
    (hd : DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b) (Qe : ℕ) (hQ : 1 ≤ Qe) (i : Fin (segS X.TT j)) (D : ℕ)
    (hD : 1 + 2 * Qe ≤ D)
    (h1 : b.rz i 0 + (X.seg C0 CE1 CE2 j).P X.p i * D ≤ A ((topOdd X j i, true), 0) + Qe)
    (h2 : A ((topOdd X j i, false), 0) ≤ b.ry i 0 + Qe) :
    y0A C0 CE1 CE2 X j A i ≤ z0A C0 CE1 CE2 X j A i := by
  have hP : 0 < (X.seg C0 CE1 CE2 j).P X.p i := nb_Ppos C0 CE1 CE2 X j hp i
  have hr := (hd.1 i 0).2
  have hq : Qe ≤ Qe * (X.seg C0 CE1 CE2 j).P X.p i := Nat.le_mul_of_pos_right Qe hP
  have a1 : y0A C0 CE1 CE2 X j A i ≤ Qe := by
    apply nb_div_le _ _ _ hP
    nlinarith
  have a2 : Qe ≤ z0A C0 CE1 CE2 X j A i := by
    unfold z0A
    rw [Nat.le_div_iff_mul_le hP]
    nlinarith
  omega

theorem nb_coarseA_ge (hp : 0 < X.p) (b : SegBlock (segS X.TT j) X.m) (i : Fin (segS X.TT j)) :
    coarseA X.p (X.seg C0 CE1 CE2 j) b i ≤
      coarseA X.p (X.seg C0 CE1 CE2 j) (segmentBlockOfMonomial C0 CE1 CE2 X j ju jp du A) i + (X.m + 1) := by
  have hP : 0 < (X.seg C0 CE1 CE2 j).P X.p i := nb_Ppos C0 CE1 CE2 X j hp i
  set P := (X.seg C0 CE1 CE2 j).P X.p i with hPdef
  set B := (X.seg C0 CE1 CE2 j).bTop i
  have hy : ∑ c : Fin (X.m + 1), (segmentBlockOfMonomial C0 CE1 CE2 X j ju jp du A).rz i c ≤ (X.m + 1) * P := by
    calc _ ≤ ∑ _c : Fin (X.m + 1), P := Finset.sum_le_sum fun c _ => by
            simp only [segmentBlockOfMonomial]
            exact (Nat.mod_lt _ hP).le
      _ = (X.m + 1) * P := by simp
  unfold coarseA
  rw [← hPdef]
  calc (B - ∑ c, b.rz i c) / P ≤ B / P := Nat.div_le_div_right (Nat.sub_le _ _)
    _ ≤ (B - ∑ c, (segmentBlockOfMonomial C0 CE1 CE2 X j ju jp du A).rz i c + (X.m + 1) * P) / P :=
        Nat.div_le_div_right (by omega)
    _ = _ := Nat.add_mul_div_right _ _ hP

end NB

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

section Glue

variable {C0 Cde CE1 CE2 : ℝ} {X : Loc} [NeZero X.m] [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] [Algebra (WF X.p X.n') O] {w : O} {mu : ℝ} {β : GlobalTheory X}
  {L : LvDat C0 CE1 CE2 mu X β} {G : ∀ j, MvPolynomial (Fin (2 * segS X.TT j + 1) × Fin X.m) (KK O)} {Std : MonH X}

abbrev PreSys.κ (P : PreSys C0 CE1 CE2 X O w mu β L G Std) : Type :=
  (Σ j, P.ιC j) ⊕ ((Σ j, Fin (BDk C0 CE1 CE2 mu X β j).T.t) ⊕ P.ιM)

def PreSys.mult (P : PreSys C0 CE1 CE2 X O w mu β L G Std) : P.κ → ℕ :=
  Sum.elim (fun _ => 1) (Sum.elim (fun x => L.lv x.1 x.2) P.multM)

def PreSys.f (P : PreSys C0 CE1 CE2 X O w mu β L G Std) : P.κ → RHH O X :=
  Sum.elim (fun x => P.fC x.1 x.2) (Sum.elim (fun x => P.fH x.1 x.2) P.fM)

def PreSys.sg (P : PreSys C0 CE1 CE2 X O w mu β L G Std) : P.κ → RHH O X :=
  Sum.elim (fun x => P.sgC x.1 x.2) (Sum.elim (fun x => P.sgH x.1 x.2) (fun a => monomial (P.aM a) 1))

def PreSys.od (P : PreSys C0 CE1 CE2 X O w mu β L G Std) : P.κ → ℕ :=
  Sum.elim (fun x => P.oC x.1 x.2) (Sum.elim (fun x => P.oH x.1 x.2) P.oM)

def PreSys.dg (P : PreSys C0 CE1 CE2 X O w mu β L G Std) : P.κ → X.TT × Bool → ℕ :=
  Sum.elim (fun x => P.dgC x.1 x.2) (Sum.elim (fun x => P.dgH x.1 x.2) P.dgM)

theorem PreSys.prod_κ (P : PreSys C0 CE1 CE2 X O w mu β L G Std) (F : P.κ → RHH O X) :
    ∏ a, F a = (∏ j, ∏ a, F (Sum.inl ⟨j, a⟩)) * ((∏ j, ∏ i, F (Sum.inr (Sum.inl ⟨j, i⟩))) * ∏ a, F (Sum.inr (Sum.inr a))) := by
  simp only [Fintype.prod_sum_type, Fintype.prod_sigma]

theorem PreSys.sum_κ (P : PreSys C0 CE1 CE2 X O w mu β L G Std) (F : P.κ → ℕ) :
    ∑ a, F a = (∑ j, ∑ a, F (Sum.inl ⟨j, a⟩)) + ((∑ j, ∑ i, F (Sum.inr (Sum.inl ⟨j, i⟩))) + ∑ a, F (Sum.inr (Sum.inr a))) := by
  simp only [Fintype.sum_sum_type, Fintype.sum_sigma]

theorem sum_mul_le {κ : Type} [Fintype κ] (u d : κ → ℕ) (Q : ℕ) (h : ∀ a, d a ≤ Q) : ∑ a, u a * d a ≤ (∑ a, u a) * Q := by
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun a _ => Nat.mul_le_mul_left _ (h a)

theorem PreSys.sgNd (P : PreSys C0 CE1 CE2 X O w mu β L G Std) (a : P.κ) : HomW (ndHom X) (P.od a) (P.sg a) := by
  rcases a with ⟨j, i⟩ | ⟨j, i⟩ | a
  · exact P.homC j i
  · exact P.homH j i
  · show HomW (ndHom X) (P.oM a) (monomial (P.aM a) (1 : KK O))
    intro m hm
    have hm' := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hm)
    subst hm'
    exact P.homM a

theorem PreSys.sgMd (P : PreSys C0 CE1 CE2 X O w mu β L G Std) (a : P.κ) :
    P.sg a ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (P.dg a) := by
  rcases a with ⟨j, i⟩ | ⟨j, i⟩ | a
  · exact P.polC j i
  · exact P.polH j i
  · show monomial (P.aM a) (1 : KK O) ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (P.dgM a)
    rw [Pol, MvPolynomial.mem_restrictSupport_iff]
    intro m hm
    have hm' := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset (Finset.mem_coe.mp hm))
    subst hm'
    exact P.polM a

theorem PreSys.dgQ (P : PreSys C0 CE1 CE2 X O w mu β L G Std) (a : P.κ) (l : X.TT × Bool) : P.dg a l ≤ X.p ^ X.G' := by
  rcases a with ⟨j, i⟩ | ⟨j, i⟩ | a
  · exact P.dgCQ j i l
  · exact P.dgHQ j i l
  · exact P.dgMQ a l

theorem PreSys.dgY (P : PreSys C0 CE1 CE2 X O w mu β L G Std) (a : P.κ) (j' : Fin (numSeg X.TT)) :
    P.dg a (topEnd X j', false) = 0 := by
  rcases a with ⟨j, i⟩ | ⟨j, i⟩ | a
  · exact P.dgCY j i j'
  · exact P.dgHY j i j'
  · exact P.dgMY a j'

theorem PreSys.ordκ (P : PreSys C0 CE1 CE2 X O w mu β L G Std) :
    P.oR + ∑ a, P.mult a * P.od a = ordFam C0 CE1 CE2 X β := by
  rw [P.sum_κ]
  simp only [PreSys.mult, PreSys.od, Sum.elim_inl, Sum.elim_inr, one_mul]
  exact P.ordEq

theorem PreSys.degκ (P : PreSys C0 CE1 CE2 X O w mu β L G Std) (l : X.TT × Bool) :
    P.dR l + ∑ a, P.mult a * P.dg a l = hhDegs X.TT X.aT X.bT l := by
  rw [P.sum_κ]
  simp only [PreSys.mult, PreSys.dg, Sum.elim_inl, Sum.elim_inr, one_mul]
  exact P.degEq l

theorem PreSys.fprod (P : PreSys C0 CE1 CE2 X O w mu β L G Std) :
    ∏ a, P.f a ^ P.mult a = (∏ j, ∏ a, P.fC j a) * ((∏ j, ∏ i, P.fH j i ^ L.lv j i) * ∏ a, P.fM a ^ P.multM a) := by
  rw [P.prod_κ]
  simp only [PreSys.f, PreSys.mult, Sum.elim_inl, Sum.elim_inr, pow_one]

theorem PreSys.symκ (P : PreSys C0 CE1 CE2 X O w mu β L G Std)
    (hStd : (monomial Std (1 : KK O) : RHH O X) = ∏ j, L.stdPoly O j) :
    P.sgR * ∏ a, P.sg a ^ P.mult a = symFam (KK O) X.p C0 CE1 CE2 X β (fun j => L.word O j (G j)) := by
  have hsym : symFam (KK O) X.p C0 CE1 CE2 X β (fun j => L.word O j (G j)) =
      (∏ j, L.head O j (L.lv j) (G j)) * monomial Std 1 := by
    rw [hStd, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun j _ => L.ioBlock_word O j (G j))
  have h1 := P.ident (fun _ _ => 1) L.lv P.multM 0
  have h2 : P.R + ((∑ j, ∑ a, (1 : ℕ) • P.pl j a) + ∑ a, P.multM a • P.aM a) + 0 = Std := by
    refine Eq.trans ?_ P.stdEq.symm
    simp
  have h3 : ∀ j, ∏ a, P.Kc j a ^ (1 : ℕ) = G j := fun j => by simp [P.Kprod j]
  rw [h2] at h1
  simp only [h3] at h1
  rw [hsym, ← h1, P.prod_κ]
  simp [PreSys.mult, PreSys.sg]

end Glue

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

section

variable {C0 CE1 CE2 mu : ℝ} {X : Loc} [NeZero X.m] {β : GlobalTheory X}

def tgStdE (L : LvDat C0 CE1 CE2 mu X β) : TgPlace X → Bool → Fin (X.m + 1) → ℕ
  | ⟨j, some i⟩, true, c => (β j).rz i c + (if c = 0 then (X.seg C0 CE1 CE2 j).P X.p i *
      (coarseA X.p (X.seg C0 CE1 CE2 j) (β j) i -
        (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then (β j).w i else (β j).o i)) else 0)
  | ⟨j, some i⟩, false, c => (β j).ry i c + (if c = 0 then (X.seg C0 CE1 CE2 j).P X.p i *
      (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then (β j).sg i else 0) else 0)
  | ⟨j, none⟩, true, c => if c = 0 then segAPlus X.TT X.aT j - (β j).oPlus else 0
  | ⟨j, none⟩, false, c => Fin.cases 0 (L.γ j) c

def tgStdX (h2 : 2 ≤ numSeg X.TT) (L : LvDat C0 CE1 CE2 mu X β) : MonH X :=
  Finsupp.equivFunOnFinite.symm fun v => tgStdE L ((Equiv.ofBijective _ (tgTop_bij X h2)).symm v.1.1) v.1.2 v.2

theorem tgStdX_at (h2 : 2 ≤ numSeg X.TT) (L : LvDat C0 CE1 CE2 mu X β) (pl : TgPlace X) (b : Bool) (c : Fin (X.m + 1)) :
    tgStdX h2 L ((tgTop X pl, b), c) = tgStdE L pl b c := by
  unfold tgStdX
  rw [Finsupp.equivFunOnFinite_symm_apply_apply]
  show tgStdE L ((Equiv.ofBijective _ (tgTop_bij X h2)).symm (tgTop X pl)) b c = _
  rw [Equiv.ofBijective_symm_apply_apply]

variable (O : Type) [CommRing O] [IsDomain O]

theorem tg_ioD_Z (j : Fin (numSeg X.TT)) (l : Fin (X.seg C0 CE1 CE2 j).t) :
    ioD O C0 CE1 CE2 mu X β j (MvPolynomial.X (scalZ (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t (Fin.castSucc l))) =
      MvPolynomial.X ((topOdd X j (uTop (X.seg C0 CE1 CE2 j) l), true), 0) ^
        (X.seg C0 CE1 CE2 j).P X.p (uTop (X.seg C0 CE1 CE2 j) l) := by
  have h := MvPolynomial.aeval_X (R := KK O) (fun v => (MvPolynomial.X (symVar C0 CE1 CE2 X j v) : RHH O X) ^
    symLev X.p C0 CE1 CE2 X j v) (Sum.inr (Fin.castSucc l, false))
  rw [sv_Z, sl_Z] at h
  exact h

theorem ioD_variable_last_eq_top_end (j : Fin (numSeg X.TT)) :
    ioD O C0 CE1 CE2 mu X β j (MvPolynomial.X (scalZ (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t
      (Fin.last (BDk C0 CE1 CE2 mu X β j).T.t))) = MvPolynomial.X ((topEnd X j, true), 0) := by
  have h := MvPolynomial.aeval_X (R := KK O) (fun v => (MvPolynomial.X (symVar C0 CE1 CE2 X j v) : RHH O X) ^
    symLev X.p C0 CE1 CE2 X j v) (Sum.inr (Fin.last _, false))
  rw [symbol_variable_last, symbol_level_last, pow_one] at h
  exact h

theorem tg_ioD_xi (j : Fin (numSeg X.TT)) (c : Fin X.m) :
    ioD O C0 CE1 CE2 mu X β j (MvPolynomial.X (xiVar (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t c)) =
      MvPolynomial.X ((topEnd X j, false), c.succ) := by
  have h := MvPolynomial.aeval_X (R := KK O) (fun v => (MvPolynomial.X (symVar C0 CE1 CE2 X j v) : RHH O X) ^
    symLev X.p C0 CE1 CE2 X j v) (Sum.inl (Fin.last (2 * segS X.TT j + 1), c))
  rw [sv_xi, sl_xi, pow_one] at h
  exact h

theorem prod_pow_ite_zero_eq {M : Type} [CommMonoid M] {k : ℕ} (f : Fin (k + 1) → M) (a : ℕ) :
    ∏ c, f c ^ (if c = 0 then a else 0) = f 0 ^ a := by
  rw [Finset.prod_eq_single 0]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem tg_stdPoly_eq (h2 : 2 ≤ numSeg X.TT) (L : LvDat C0 CE1 CE2 mu X β) (j : Fin (numSeg X.TT)) :
    L.stdPoly O j = segMon O X j (tgStdX h2 L) := by
  have hz : ∀ i c, tgStdX h2 L ((topOdd X j i, true), c) = tgStdE L ⟨j, some i⟩ true c :=
    fun i c => tgStdX_at h2 L ⟨j, some i⟩ true c
  have hy : ∀ i c, tgStdX h2 L ((topOdd X j i, false), c) = tgStdE L ⟨j, some i⟩ false c :=
    fun i c => tgStdX_at h2 L ⟨j, some i⟩ false c
  have hx : ∀ c, tgStdX h2 L ((topEnd X j, true), c) = tgStdE L ⟨j, none⟩ true c :=
    fun c => tgStdX_at h2 L ⟨j, none⟩ true c
  have hx' : ∀ c, tgStdX h2 L ((topEnd X j, false), c) = tgStdE L ⟨j, none⟩ false c :=
    fun c => tgStdX_at h2 L ⟨j, none⟩ false c
  unfold segMon LvDat.stdPoly
  simp only [hz, hy, hx, hx', tgStdE, map_mul, map_prod, map_pow, ioD_variable_last_eq_top_end, tg_ioD_xi]
  have e1 : ∏ l : Fin (BDk C0 CE1 CE2 mu X β j).T.t,
      (ioD O C0 CE1 CE2 mu X β j (MvPolynomial.X (scalZ (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t
        (Fin.castSucc l)))) ^ (BDk C0 CE1 CE2 mu X β j).T.z l =
      ∏ i : Fin (segS X.TT j), if (X.seg C0 CE1 CE2 j).sigma ≤ i.val then
        ((MvPolynomial.X ((topOdd X j i, true), 0) : RHH O X) ^ (X.seg C0 CE1 CE2 j).P X.p i) ^
          (coarseA X.p (X.seg C0 CE1 CE2 j) (β j) i - (β j).o i) else 1 := by
    rw [← tg_prod_uTop (X.seg C0 CE1 CE2 j) (fun i => ((MvPolynomial.X ((topOdd X j i, true), 0) : RHH O X) ^
      (X.seg C0 CE1 CE2 j).P X.p i) ^ (coarseA X.p (X.seg C0 CE1 CE2 j) (β j) i - (β j).o i))]
    refine Finset.prod_congr rfl fun l _ => ?_
    exact congrArg (fun y => y ^ (BDk C0 CE1 CE2 mu X β j).T.z l) (tg_ioD_Z (mu := mu) (β := β) O j l)
  rw [e1]
  have e2 : ∏ c : Fin (X.m + 1), ((MvPolynomial.X ((topEnd X j, true), c) : RHH O X) ^
        (if c = 0 then segAPlus X.TT X.aT j - (β j).oPlus else 0) *
      MvPolynomial.X ((topEnd X j, false), c) ^ (Fin.cases 0 (L.γ j) c : ℕ)) =
      MvPolynomial.X ((topEnd X j, true), 0) ^ (segAPlus X.TT X.aT j - (β j).oPlus) *
        ∏ c : Fin X.m, MvPolynomial.X ((topEnd X j, false), c.succ) ^ L.γ j c := by
    rw [Finset.prod_mul_distrib, prod_pow_ite_zero_eq (fun c => (MvPolynomial.X ((topEnd X j, true), c) : RHH O X)),
      Fin.prod_univ_succ]
    simp
  rw [e2]
  have e3 : ∀ i : Fin (segS X.TT j), ∏ c : Fin (X.m + 1),
      ((MvPolynomial.X ((topOdd X j i, true), c) : RHH O X) ^ ((β j).rz i c + (if c = 0 then (X.seg C0 CE1 CE2 j).P X.p i *
        (coarseA X.p (X.seg C0 CE1 CE2 j) (β j) i -
          (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then (β j).w i else (β j).o i)) else 0)) *
      MvPolynomial.X ((topOdd X j i, false), c) ^ ((β j).ry i c + (if c = 0 then (X.seg C0 CE1 CE2 j).P X.p i *
        (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then (β j).sg i else 0) else 0))) =
      (∏ c : Fin (X.m + 1), ((MvPolynomial.X ((topOdd X j i, true), c) : RHH O X) ^ (β j).rz i c *
        MvPolynomial.X ((topOdd X j i, false), c) ^ (β j).ry i c)) *
      ((if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then
        (MvPolynomial.X ((topOdd X j i, true), 0) : RHH O X) ^ ((X.seg C0 CE1 CE2 j).P X.p i *
            (coarseA X.p (X.seg C0 CE1 CE2 j) (β j) i - (β j).w i)) *
          MvPolynomial.X ((topOdd X j i, false), 0) ^ ((X.seg C0 CE1 CE2 j).P X.p i * (β j).sg i) else 1) *
       (if (X.seg C0 CE1 CE2 j).sigma ≤ i.val then
        ((MvPolynomial.X ((topOdd X j i, true), 0) : RHH O X) ^ (X.seg C0 CE1 CE2 j).P X.p i) ^
          (coarseA X.p (X.seg C0 CE1 CE2 j) (β j) i - (β j).o i) else 1)) := by
    intro i
    simp only [pow_add]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      prod_pow_ite_zero_eq (fun c => (MvPolynomial.X ((topOdd X j i, true), c) : RHH O X)),
      prod_pow_ite_zero_eq (fun c => (MvPolynomial.X ((topOdd X j i, false), c) : RHH O X)), Finset.prod_mul_distrib]
    by_cases hi : (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma
    · rw [if_pos hi, if_pos hi, if_pos hi, if_neg (by omega)]
      ring
    · rw [if_neg hi, if_neg hi, if_neg hi, if_pos (by omega), mul_zero, pow_zero, ← pow_mul]
      ring
  rw [Finset.prod_congr rfl fun i _ => e3 i, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  unfold digitMon sTopMon
  show _ * _ * (_ * MvPolynomial.X ((topEnd X j, true), 0) ^ (segAPlus X.TT X.aT j - (β j).oPlus) * _) = _
  ring

theorem tg_std_eq (h2 : 2 ≤ numSeg X.TT) (L : LvDat C0 CE1 CE2 mu X β) (Std : MonH X)
    (h : (monomial Std (1 : KK O) : RHH O X) = ∏ j, L.stdPoly O j) : Std = tgStdX h2 L := by
  have e : (monomial Std (1 : KK O) : RHH O X) = monomial (tgStdX h2 L) 1 := by
    rw [h, tg_mono_split O X h2]
    exact Finset.prod_congr rfl fun j _ => tg_stdPoly_eq O h2 L j
  exact MvPolynomial.monomial_left_injective (one_ne_zero) e

end

end Formalism.MainNotions.ColumnSystems.Pf
end
end
