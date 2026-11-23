module

public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle003
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle010
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle007
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.OtherEFree
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle005
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.WeightWLet
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.BFTrueDeg
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle006
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Kummer
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.SymVarInlFst
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.BitVec

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.CovariantDegrees

theorem op_single_add {K σ : Type} [Field K] (a : σ) (b : ℕ) (f : σ →₀ ℕ) (ha : a ∉ f.support) (u : MvPolynomial σ K) :
    monomial (Finsupp.single a b + f) (1 : K) * divDer (Finsupp.single a b + f) u =
      cth a b (monomial f (1 : K) * divDer f u) := by
  classical
  ext μ
  rw [eig_one, coeff_cth, eig_one]
  have hd : Disjoint (Finsupp.single a b).support f.support := by
    refine Finset.disjoint_of_subset_left Finsupp.support_single_subset ?_
    rw [Finset.disjoint_singleton_left]
    exact ha
  rw [Finsupp.prod_add_index_of_disjoint hd, Finsupp.prod_single_index (by simp)]
  push_cast
  ring

section GlobalTheory

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero (KK O)] {N r : ℕ} [NeZero r]

theorem op_SSt (D7 : Formalism.BasicNotions.D7) {D : BlockData N} (hT : TieOK D) (ν : BVar N r D.T.t →₀ ℕ) :
    (∀ v ∈ ν.support, OddV D v) → ∀ (thr thr' : Fin D.T.q → WithTop ℤ),
    (∀ k, thr k + (((ν.sum fun _ n => n : ℕ) : ℤ) : WithTop ℤ) ≤ thr' k) →
    ∀ u ∈ SSt O r D thr, monomial ν (1 : KK O) * divDer ν u ∈ SSt O r D thr' := by
  classical
  induction ν using Finsupp.induction with
  | zero =>
    intro _ thr thr' hthr u hu
    rw [divDer_zero]
    have : (monomial (0 : BVar N r D.T.t →₀ ℕ) (1 : KK O)) = 1 := rfl
    rw [this, one_mul]
    exact SSt_mono D (fun k => by simpa using hthr k) hu
  | single_add a b f ha hb ih =>
    intro hv thr thr' hthr u hu
    rw [op_single_add a b f ha]
    have hsum : ((Finsupp.single a b + f).sum fun _ n => n) = b + f.sum fun _ n => n := by
      rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
    have hsupp : (Finsupp.single a b + f).support = insert a f.support := by
      rw [Finsupp.support_add_eq, Finsupp.support_single _ hb]
      · rfl
      · rw [Finsupp.support_single _ hb, Finset.disjoint_singleton_left]
        exact ha
    have h1 := ih (fun v hvf => hv v (by rw [hsupp]; exact Finset.mem_insert_of_mem hvf)) thr
      (fun k => thr k + (((f.sum fun _ n => n : ℕ) : ℤ) : WithTop ℤ)) (fun _ => le_rfl) u hu
    refine cth_SSt D7 hT b (fun k => ?_) a (hv a (by rw [hsupp]; exact Finset.mem_insert_self _ _)) h1
    refine le_trans (le_of_eq ?_) (hthr k)
    rw [hsum, add_assoc]
    push_cast
    rw [add_comm ((b : ℕ) : WithTop ℤ)]

end GlobalTheory

theorem tieOK_blockBase (p : ℕ) {r s : ℕ} (S : SegData s) (aTop : Fin s → ℕ) (aPlus : ℕ) (b : SegBlock s r) :
    TieOK (blockBase p S aTop aPlus b) := by
  refine { lt := ?_, inj := ?_, sep := ?_, uW := ?_, vecE := ?_ }
  · intro i
    have := (uTop S i).2
    show 2 * ((uTop S i : Fin s) : ℕ) + 1 < 2 * s + 1
    omega
  · intro i i' h
    have h' : 2 * ((uTop S i : Fin s) : ℕ) = 2 * ((uTop S i' : Fin s) : ℕ) := h
    simp only [uTop] at h'
    exact Fin.ext (by omega)
  · intro i i' h
    have h' : 2 * ((uTop S i : Fin s) : ℕ) + 1 = 2 * ((uTop S i' : Fin s) : ℕ) := h
    omega
  · intro i
    have := (uTop S i).2
    constructor
    · show 2 * ((uTop S i : Fin s) : ℕ) ≠ 2 * s
      omega
    · show 2 * ((uTop S i : Fin s) : ℕ) + 1 ≠ 2 * s
      omega
  · intro i h
    show decide ((2 * ((uTop S i : Fin s) : ℕ) + 1) % 2 = 0) = false
    simp

theorem thr_shift (x : WithTop ℤ) (mm : ℝ) (n c4 : ℕ) (h : n ≤ c4) :
    x.map (fun y : ℤ => ⌊(y : ℝ) - mm⌋) + ((n : ℤ) : WithTop ℤ) ≤ x.map (fun y : ℤ => ⌊(y : ℝ) - (mm - (c4 : ℝ))⌋) := by
  cases x with
  | top => simp
  | coe y =>
    simp only [WithTop.map_coe]
    have e : (y : ℝ) - (mm - (c4 : ℝ)) = ((y : ℝ) - mm) + (c4 : ℝ) := by ring
    rw [e, Int.floor_add_natCast]
    have : ⌊(y : ℝ) - mm⌋ + (n : ℤ) ≤ ⌊(y : ℝ) - mm⌋ + (c4 : ℤ) := by omega
    exact_mod_cast this

theorem gThetaAt (D7 : Formalism.BasicNotions.D7) : GThetaAt := by
  intro C0 CE1 CE2 X _ O _ _ _ _ j b _ c T q hT mm u hu
  unfold gOp
  refine Submodule.sum_mem _ fun ν hν => Submodule.smul_mem _ _ ?_
  have hTie := tieOK_blockBase X.p (r := X.m) (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) b
  refine op_SSt (O := O) (r := X.m) D7 hTie ν ?_
    (fun k => (segmentCapacities X.p (X.seg C0 CE1 CE2 j) b k).map (fun y : ℤ => ⌊(y : ℝ) - mm⌋))
    (fun k => (segmentCapacities X.p (X.seg C0 CE1 CE2 j) b k).map (fun y : ℤ => ⌊(y : ℝ) - (mm - 4 * (c : ℝ))⌋)) ?_ u hu
  · intro v hv
    have h := (hT ν hν).2 v hv
    rcases v with ⟨a, c'⟩ | ⟨l, s⟩
    · have h' : (a : ℕ) < 2 * segS X.TT j := h
      constructor
      · intro e
        have := congrArg Fin.val e
        simp only [Fin.val_castSucc] at this
        have h2 : ((blockBase X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) b).uPos : ℕ) =
          2 * segS X.TT j := rfl
        omega
      · intro e
        have := congrArg Fin.val e
        simp only [Fin.val_last] at this
        omega
    · have h' : (l : ℕ) < (X.seg C0 CE1 CE2 j).t := h
      intro e
      have := congrArg Fin.val e
      have h2 : ((Fin.last (blockBase X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) b).T.t :
        Fin _) : ℕ) = (X.seg C0 CE1 CE2 j).t := rfl
      omega
  · intro k
    have := thr_shift (segmentCapacities X.p (X.seg C0 CE1 CE2 j) b k) mm (ν.sum fun _ n => n) (4 * c) (hT ν hν).1
    have e : (((4 * c : ℕ) : ℕ) : ℝ) = 4 * (c : ℝ) := by push_cast; ring
    rw [e] at this
    exact this

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

section

variable (C0 CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] (j : Fin (numSeg X.TT))

theorem symbol_variable_first_columns (b : SegBlock (segS X.TT j) X.m) (v : BV C0 CE1 CE2 X j) (h : mu0 C0 CE1 CE2 X j b v ≠ 0) :
    (symVar C0 CE1 CE2 X j v).2 = 0 ∨ (symVar C0 CE1 CE2 X j v).2 = Fin.succ 0 := by
  rcases v with ⟨a, c⟩ | ⟨l, bo⟩
  · right
    have hc : c = 0 := by
      by_contra hc
      exact h (by show mu0F C0 CE1 CE2 X j b (Sum.inl (a, c)) = 0; simp [mu0F, hc])
    subst hc
    simp only [symVar]
    split_ifs <;> rfl
  · left
    simp only [symVar]
    split_ifs <;> rfl

theorem card_supp_le (b : SegBlock (segS X.TT j) X.m) (x : X.TT × Bool) :
    open Classical in
    (Finset.univ.filter (fun v : BV C0 CE1 CE2 X j => (symVar C0 CE1 CE2 X j v).1 = x ∧
      mu0 C0 CE1 CE2 X j b v ≠ 0)).card ≤ 2 := by
  classical
  have hsub : (Finset.univ.filter (fun v : BV C0 CE1 CE2 X j => (symVar C0 CE1 CE2 X j v).1 = x ∧
      mu0 C0 CE1 CE2 X j b v ≠ 0)) ⊆
      (Finset.univ.filter (fun v : BV C0 CE1 CE2 X j => symVar C0 CE1 CE2 X j v = (x, 0))) ∪
      (Finset.univ.filter (fun v : BV C0 CE1 CE2 X j => symVar C0 CE1 CE2 X j v = (x, Fin.succ 0))) := by
    intro v hv
    obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hv).2
    rcases symbol_variable_first_columns C0 CE1 CE2 X j b v h2 with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, Prod.ext h1 h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, Prod.ext h1 h⟩)
  have hone : ∀ y, (Finset.univ.filter (fun v : BV C0 CE1 CE2 X j => symVar C0 CE1 CE2 X j v = y)).card ≤ 1 := by
    intro y
    refine Finset.card_le_one.2 fun v hv v' hv' => ?_
    exact symVar_inj C0 CE1 CE2 X j (((Finset.mem_filter.1 hv).2).trans ((Finset.mem_filter.1 hv').2).symm)
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ 1 + 1 := Nat.add_le_add (hone _) (hone _)

theorem cdeg_le_tdeg (hp : 0 < X.p) (b : SegBlock (segS X.TT j) X.m) (x : X.TT × Bool) :
    cdeg C0 CE1 CE2 X j b x ≤ tdeg C0 CE1 CE2 X j b x := by
  classical
  rw [← sum_fiber C0 CE1 CE2 X j b (mu0 C0 CE1 CE2 X j b) (leading_exponent_homogeneous C0 CE1 CE2 X j b) x]
  set μ0 := mu0 C0 CE1 CE2 X j b
  have hco : ∀ c : Fin (X.m + 1), (μ0.sum fun v n => Finsupp.single (symVar C0 CE1 CE2 X j v)
      (symLev X.p C0 CE1 CE2 X j v * n)) (x, c) =
      ∑ v : BV C0 CE1 CE2 X j, if symVar C0 CE1 CE2 X j v = (x, c) then symLev X.p C0 CE1 CE2 X j v * μ0 v else 0 := by
    intro c
    rw [Finsupp.sum_apply, Finsupp.sum_fintype _ _ (fun v => by simp)]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finsupp.single_apply]
  have hswap : (∑ c : Fin (X.m + 1), ∑ v : BV C0 CE1 CE2 X j,
      (if symVar C0 CE1 CE2 X j v = (x, c) then symLev X.p C0 CE1 CE2 X j v * μ0 v else 0)) =
      ∑ v : BV C0 CE1 CE2 X j, if (symVar C0 CE1 CE2 X j v).1 = x then symLev X.p C0 CE1 CE2 X j v * μ0 v else 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases h : (symVar C0 CE1 CE2 X j v).1 = x
    · rw [if_pos h, Finset.sum_eq_single (symVar C0 CE1 CE2 X j v).2]
      · rw [if_pos (Prod.ext h rfl : symVar C0 CE1 CE2 X j v = (x, (symVar C0 CE1 CE2 X j v).2))]
      · intro c _ hc
        rw [if_neg (fun e => hc (by rw [e]))]
      · intro hh; exact absurd (Finset.mem_univ _) hh
    · rw [if_neg h]
      exact Finset.sum_eq_zero fun c _ => if_neg (fun e => h (by rw [e]))
  calc (∑ v ∈ Finset.univ.filter (fun v : BV C0 CE1 CE2 X j => (symVar C0 CE1 CE2 X j v).1 = x), μ0 v)
      = ∑ v : BV C0 CE1 CE2 X j, if (symVar C0 CE1 CE2 X j v).1 = x then μ0 v else 0 := Finset.sum_filter _ _
    _ ≤ ∑ v : BV C0 CE1 CE2 X j, if (symVar C0 CE1 CE2 X j v).1 = x then symLev X.p C0 CE1 CE2 X j v * μ0 v else 0 := by
        refine Finset.sum_le_sum fun v _ => ?_
        split_ifs
        · exact Nat.le_mul_of_pos_left _ (symLev_pos C0 CE1 CE2 X hp j v)
        · exact le_rfl
    _ = ∑ c : Fin (X.m + 1), (μ0.sum fun v n => Finsupp.single (symVar C0 CE1 CE2 X j v)
          (symLev X.p C0 CE1 CE2 X j v * n)) (x, c) := by
        rw [Finset.sum_congr rfl fun c _ => hco c, hswap]
    _ ≤ tdeg C0 CE1 CE2 X j b x := by
        unfold tdeg multideg ioExp
        refine Finset.sum_le_sum fun c _ => ?_
        rw [Finsupp.add_apply]
        exact Nat.le_add_left _ _

end

theorem coarseMultAt_of {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ} (hO : OPlusAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) :
    CoarseMultAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  classical
  intro X _ hD1 hH hc j b hb
  have hp : 0 < X.p := hD1.1.pos
  have ho := hO X hD1 hH hc j b hb
  set μ0 := mu0 C0 CE1 CE2 X j b with hμ0
  let F : X.TT × Bool → Finset (BV C0 CE1 CE2 X j) :=
    fun x => Finset.univ.filter (fun v : BV C0 CE1 CE2 X j => (symVar C0 CE1 CE2 X j v).1 = x)
  let s : X.TT × Bool → Finset (BV C0 CE1 CE2 X j) := fun x => (F x).filter (fun v => μ0 v ≠ 0)
  have hfac : ∀ x, (cdeg C0 CE1 CE2 X j b x).factorial =
      (∏ v ∈ F x, (μ0 v).factorial) * Nat.multinomial (s x) μ0 := by
    intro x
    rw [← sum_fiber C0 CE1 CE2 X j b μ0 (leading_exponent_homogeneous C0 CE1 CE2 X j b) x]
    show (∑ v ∈ F x, μ0 v).factorial = _
    rw [← Finset.sum_filter_ne_zero, ← Finset.prod_filter_of_ne (p := fun v => μ0 v ≠ 0)
      (fun v _ hv h0 => hv (by rw [h0]; rfl))]
    exact (Nat.multinomial_spec _ _).symm
  have hE : expFact μ0 = ∏ x : X.TT × Bool, ∏ v ∈ F x, (μ0 v).factorial := by
    unfold expFact
    rw [Finsupp.prod_fintype _ _ (fun _ => rfl)]
    exact (Finset.prod_fiberwise Finset.univ (fun v => (symVar C0 CE1 CE2 X j v).1) (fun v => (μ0 v).factorial)).symm
  have hE0 : expFact μ0 ≠ 0 := by
    unfold expFact; exact Finsupp.prod_ne_zero_iff.2 fun _ _ => Nat.factorial_ne_zero _
  have hM0 : ∀ x ∈ (Finset.univ : Finset (X.TT × Bool)), Nat.multinomial (s x) μ0 ≠ 0 :=
    fun x _ => (Nat.multinomial_pos _ _).ne'
  rw [Finset.prod_congr rfl (fun x _ => hfac x), Finset.prod_mul_distrib, ← hE,
    Nat.factorization_mul hE0 (Finset.prod_ne_zero_iff.2 hM0), Finsupp.add_apply, Nat.factorization_prod hM0,
    Finsupp.finsetSum_apply]
  refine Nat.add_le_add_left ?_ _
  calc (∑ x : X.TT × Bool, (Nat.multinomial (s x) μ0).factorization X.p)
      ≤ ∑ x : X.TT × Bool, Nat.log X.p (cdeg C0 CE1 CE2 X j b x) := by
        refine Finset.sum_le_sum fun x _ => (multinomial_val X.p (s x) μ0).trans ?_
        have hc2 : (s x).card ≤ 2 := by
          have := card_supp_le C0 CE1 CE2 X j b x
          simp only [s, F, Finset.filter_filter]
          convert this
        rw [Finset.sum_filter_ne_zero]
        show ((s x).card - 1) * Nat.log X.p (∑ v ∈ F x, μ0 v) ≤ _
        rw [sum_fiber C0 CE1 CE2 X j b μ0 (leading_exponent_homogeneous C0 CE1 CE2 X j b) x]
        calc ((s x).card - 1) * Nat.log X.p (cdeg C0 CE1 CE2 X j b x) ≤ 1 * Nat.log X.p (cdeg C0 CE1 CE2 X j b x) :=
              Nat.mul_le_mul_right _ (by omega)
          _ = _ := one_mul _
    _ ≤ ∑ x : X.TT × Bool, Nat.log X.p (tdeg C0 CE1 CE2 X j b x) :=
        Finset.sum_le_sum fun x _ => Nat.log_mono_right (cdeg_le_tdeg C0 CE1 CE2 X j hp b x)
    _ = lgSeg X j := by
        rw [sum_tdeg C0 CE1 CE2 X j (Nat.log X.p) (Nat.log_zero_right _) b hb ho]
        unfold lgSeg
        rw [Finset.sum_add_distrib]

end Formalism.MainNotions.ColumnSystems.Pf
end
end
