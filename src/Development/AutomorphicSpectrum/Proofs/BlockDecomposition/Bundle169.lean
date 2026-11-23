module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BisimplicialActionSecondFactor
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle117
public import GroundTheory.LocalFields.Bundle008
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedKernelOfSmallBoxCharacter
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle161
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Bundle001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
public import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle157
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle005
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle158
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
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct GlobalTheory.CatCoh MainStatements.Hodge GlobalTheory.CompanionTheory.HodgeCx GlobalTheory.CompanionTheory.HopfLe

namespace GlobalTheory.CompanionTheory.HopfLe.DnCup

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C]

abbrev dl (n : ℕ) (i : Fin (n + 2)) : Fin (n + 1) →o Fin (n + 2) := (Fin.succAboveOrderEmb i).toOrderHom

def incl (n : ℕ) : Fin 3 →o Fin (n + 3) := ⟨Fin.castLE (by omega), fun _ _ h ↦ h⟩

private theorem sum_fin_add_two_eq_zero_add_sum_succ {M : Type*} [AddCommMonoid M] {m : ℕ} (f : Fin (m + 2) → M) :
    ∑ i, f i = f 0 + ∑ k : Fin (m + 1), f k.succ :=
  Fin.sum_univ_succ f

private theorem sum_fin_add_two_eq_zero_add_one_add_sum {M : Type*} [AddCommMonoid M] {m : ℕ} (f : Fin (m + 2) → M) :
    ∑ i, f i = f 0 + f 1 + ∑ k : Fin m, f k.succ.succ :=
  ((Fin.sum_univ_succ f).trans
    (congrArg _ (Fin.sum_univ_succ fun i : Fin (m + 1) => f i.succ))).trans (add_assoc _ _ _).symm

theorem dl_spec (n : ℕ) (i : Fin (n + 2)) (j : Fin (n + 1)) :
    ((j : ℕ) < i ∧ (dl n i j : ℕ) = j) ∨ ((i : ℕ) ≤ j ∧ (dl n i j : ℕ) = j + 1) := by
  have hv : GlobalTheory.CompanionTheory.HopfLe.DnCup.dl n i j = i.succAbove j := by
    simp only [OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
  rw [hv]
  rcases Nat.lt_or_ge (j : ℕ) i with h | h
  · left
    refine ⟨h, ?_⟩
    rw [Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_def, Fin.coe_castSucc]; exact h),
      Fin.coe_castSucc]
  · right
    refine ⟨h, ?_⟩
    rw [Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_def, Fin.coe_castSucc]; exact h),
      Fin.val_succ]

theorem front_val (n : ℕ) (j : Fin 2) : (front n j : ℕ) = j := rfl

theorem back_val (n : ℕ) (j : Fin (n + 1)) : (back n j : ℕ) = j + 1 := by
  have hv : GlobalTheory.CompanionTheory.HopfLe.back n j = Fin.succAbove 0 j := by
    simp only [GlobalTheory.CompanionTheory.HopfLe.back, OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
  rw [hv, Fin.succAbove_of_le_castSucc _ _ (by simp), Fin.val_succ]

theorem incl_val (n : ℕ) (j : Fin 3) : (incl n j : ℕ) = j := rfl

theorem dl_front_high (n : ℕ) (k : Fin (n + 1)) : (dl (n + 1) k.succ.succ).comp (front n) = front (n + 1) := by
  refine DFunLike.ext _ _ fun j => Fin.ext ?_
  have h1 := GlobalTheory.CompanionTheory.HopfLe.DnCup.front_val n j
  have h2 := GlobalTheory.CompanionTheory.HopfLe.DnCup.front_val (n + 1) j
  have h3 := GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_spec (n + 1) k.succ.succ (GlobalTheory.CompanionTheory.HopfLe.front n j)
  have hj := j.isLt
  simp only [OrderHom.comp_coe, Function.comp_apply, Fin.val_succ] at *
  omega

theorem dl_back_high (n : ℕ) (k : Fin (n + 1)) :
    (dl (n + 1) k.succ.succ).comp (back n) = (back (n + 1)).comp (dl n k.succ) := by
  refine DFunLike.ext _ _ fun j => Fin.ext ?_
  have h1 := GlobalTheory.CompanionTheory.HopfLe.DnCup.back_val n j
  have h2 := GlobalTheory.CompanionTheory.HopfLe.DnCup.back_val (n + 1) (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl n k.succ j)
  have h3 := GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_spec (n + 1) k.succ.succ (GlobalTheory.CompanionTheory.HopfLe.back n j)
  have h4 := GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_spec n k.succ j
  simp only [OrderHom.comp_coe, Function.comp_apply, Fin.val_succ] at *
  omega

theorem dl_back_zero (n : ℕ) : (dl (n + 1) 0).comp (back n) = (back (n + 1)).comp (dl n 0) := by
  refine DFunLike.ext _ _ fun j => Fin.ext ?_
  have h1 := GlobalTheory.CompanionTheory.HopfLe.DnCup.back_val n j
  have h2 := GlobalTheory.CompanionTheory.HopfLe.DnCup.back_val (n + 1) (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl n 0 j)
  have h3 := GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_spec (n + 1) 0 (GlobalTheory.CompanionTheory.HopfLe.back n j)
  have h4 := GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_spec n 0 j
  simp only [OrderHom.comp_coe, Function.comp_apply, Fin.val_zero] at *
  omega

theorem dl_back_one (n : ℕ) : (dl (n + 1) 1).comp (back n) = (back (n + 1)).comp (dl n 0) := by
  refine DFunLike.ext _ _ fun j => Fin.ext ?_
  have h1 := GlobalTheory.CompanionTheory.HopfLe.DnCup.back_val n j
  have h2 := GlobalTheory.CompanionTheory.HopfLe.DnCup.back_val (n + 1) (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl n 0 j)
  have h3 := GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_spec (n + 1) 1 (GlobalTheory.CompanionTheory.HopfLe.back n j)
  have h4 := GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_spec n 0 j
  simp only [OrderHom.comp_coe, Function.comp_apply, Fin.val_zero, Fin.val_one] at *
  omega

theorem dl_front_zero (n : ℕ) : (dl (n + 1) 0).comp (front n) = (incl n).comp (dl 1 0) := by
  refine DFunLike.ext _ _ fun j => Fin.ext ?_
  have h1 := GlobalTheory.CompanionTheory.HopfLe.DnCup.front_val n j
  have h2 := GlobalTheory.CompanionTheory.HopfLe.DnCup.incl_val n (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl 1 0 j)
  have h3 := GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_spec (n + 1) 0 (GlobalTheory.CompanionTheory.HopfLe.front n j)
  have h4 := GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_spec 1 0 j
  simp only [OrderHom.comp_coe, Function.comp_apply, Fin.val_zero] at *
  omega

theorem dl_front_one (n : ℕ) : (dl (n + 1) 1).comp (front n) = (incl n).comp (dl 1 1) := by
  refine DFunLike.ext _ _ fun j => Fin.ext ?_
  have h1 := GlobalTheory.CompanionTheory.HopfLe.DnCup.front_val n j
  have h2 := GlobalTheory.CompanionTheory.HopfLe.DnCup.incl_val n (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl 1 1 j)
  have h3 := GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_spec (n + 1) 1 (GlobalTheory.CompanionTheory.HopfLe.front n j)
  have h4 := GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_spec 1 1 j
  simp only [OrderHom.comp_coe, Function.comp_apply, Fin.val_one] at *
  omega

theorem front_eq_incl (n : ℕ) : front (n + 1) = (incl n).comp (dl 1 2) := by
  refine DFunLike.ext _ _ fun j => Fin.ext ?_
  have h1 := GlobalTheory.CompanionTheory.HopfLe.DnCup.front_val (n + 1) j
  have h2 := GlobalTheory.CompanionTheory.HopfLe.DnCup.incl_val n (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl 1 2 j)
  have h3 := GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_spec 1 2 j
  have h5 : ((2 : Fin (1 + 2)) : ℕ) = 2 := rfl
  have hj := j.isLt
  simp only [OrderHom.comp_coe, Function.comp_apply] at *
  omega

theorem bracket (F : C ⥤ CommAlgCat.{0} R) (n : ℕ) (y : Cn F 1) (hy : dn F 1 y = 0) :
    act F ((dl (n + 1) 0).comp (front n)) y - act F ((dl (n + 1) 1).comp (front n)) y
      + act F (front (n + 1)) y = 0 := by
  have hface : ∀ (m : ℕ) (j : Fin (m + 2)),
      MainStatements.Hodge.cof F m j = GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl m j) :=
    fun m j => GlobalTheory.CompanionTheory.HodgeCx.cof_eq F m j
  have hd : MainStatements.Hodge.dn F 1 y =
      GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl 1 0) y - GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl 1 1) y
        + GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl 1 2) y := by
    rw [MainStatements.Hodge.dn, LinearMap.sum_apply, Fin.sum_univ_three]
    simp only [LinearMap.smul_apply, hface, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero,
      pow_one, neg_one_sq, one_smul, neg_smul, sub_eq_add_neg]
    first | done | rfl
  rw [GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_front_zero, GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_front_one, GlobalTheory.CompanionTheory.HopfLe.DnCup.front_eq_incl,
    GlobalTheory.CompanionTheory.HodgeCx.act_comp, GlobalTheory.CompanionTheory.HodgeCx.act_comp, GlobalTheory.CompanionTheory.HodgeCx.act_comp,
    ← map_sub, ← map_add, ← hd, hy, map_zero]

theorem coboundary_cup1 (F : C ⥤ CommAlgCat.{0} R) {n : ℕ} (y : Cn F 1) (z : Cn F n) (hy : dn F 1 y = 0) :
    dn F (n + 1) (cup1 F y z) = - cup1 F y (dn F n z) := by
  have hface : ∀ (m : ℕ) (j : Fin (m + 2)),
      MainStatements.Hodge.cof F m j = GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl m j) :=
    fun m j => GlobalTheory.CompanionTheory.HodgeCx.cof_eq F m j
  have hcup : ∀ i : Fin (n + 1 + 2), MainStatements.Hodge.cof F (n + 1) i (GlobalTheory.CompanionTheory.HopfLe.cup1 F y z) =
      GlobalTheory.CompanionTheory.HodgeCx.act F ((GlobalTheory.CompanionTheory.HopfLe.DnCup.dl (n + 1) i).comp (GlobalTheory.CompanionTheory.HopfLe.front n)) y *
        GlobalTheory.CompanionTheory.HodgeCx.act F ((GlobalTheory.CompanionTheory.HopfLe.DnCup.dl (n + 1) i).comp (GlobalTheory.CompanionTheory.HopfLe.back n)) z := by
    intro i
    rw [hface, GlobalTheory.CompanionTheory.HopfLe.cup1, GlobalTheory.CompanionTheory.HopfLe.act_mul,
      GlobalTheory.CompanionTheory.HodgeCx.act_comp F (GlobalTheory.CompanionTheory.HopfLe.front n),
      GlobalTheory.CompanionTheory.HodgeCx.act_comp F (GlobalTheory.CompanionTheory.HopfLe.back n)]
  have hback : ∀ {k : ℕ} (θ : Fin (k + 1) →o Fin (n + 1 + 1)) (w : MainStatements.Hodge.Cn F k),
      GlobalTheory.CompanionTheory.HodgeCx.act F ((GlobalTheory.CompanionTheory.HopfLe.back (n + 1)).comp θ) w =
        GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.back (n + 1)) (GlobalTheory.CompanionTheory.HodgeCx.act F θ w) :=
    fun θ w => GlobalTheory.CompanionTheory.HodgeCx.act_comp F θ (GlobalTheory.CompanionTheory.HopfLe.back (n + 1)) w
  have h' := eq_neg_iff_add_eq_zero.mpr (GlobalTheory.CompanionTheory.HopfLe.DnCup.bracket F n y hy)
  have key : GlobalTheory.CompanionTheory.HodgeCx.act F ((GlobalTheory.CompanionTheory.HopfLe.DnCup.dl (n + 1) 0).comp (GlobalTheory.CompanionTheory.HopfLe.front n)) y *
        GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.back (n + 1)) (GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl n 0) z) =
      GlobalTheory.CompanionTheory.HodgeCx.act F ((GlobalTheory.CompanionTheory.HopfLe.DnCup.dl (n + 1) 1).comp (GlobalTheory.CompanionTheory.HopfLe.front n)) y *
        GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.back (n + 1)) (GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl n 0) z) +
      -(GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.front (n + 1)) y *
        GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.back (n + 1)) (GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl n 0) z)) := by
    rw [← neg_mul, ← add_mul, ← h']
    congr 1
    abel
  have h0 : MainStatements.Hodge.cof F (n + 1) 0 (GlobalTheory.CompanionTheory.HopfLe.cup1 F y z) =
      GlobalTheory.CompanionTheory.HodgeCx.act F ((GlobalTheory.CompanionTheory.HopfLe.DnCup.dl (n + 1) 0).comp (GlobalTheory.CompanionTheory.HopfLe.front n)) y *
        GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.back (n + 1)) (GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl n 0) z) := by
    rw [hcup, GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_back_zero, hback]
  have h1 : MainStatements.Hodge.cof F (n + 1) 1 (GlobalTheory.CompanionTheory.HopfLe.cup1 F y z) =
      GlobalTheory.CompanionTheory.HodgeCx.act F ((GlobalTheory.CompanionTheory.HopfLe.DnCup.dl (n + 1) 1).comp (GlobalTheory.CompanionTheory.HopfLe.front n)) y *
        GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.back (n + 1)) (GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl n 0) z) := by
    rw [hcup, GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_back_one, hback]
  have hk : ∀ k : Fin (n + 1), MainStatements.Hodge.cof F (n + 1) k.succ.succ (GlobalTheory.CompanionTheory.HopfLe.cup1 F y z) =
      GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.front (n + 1)) y *
        GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.back (n + 1))
          (GlobalTheory.CompanionTheory.HodgeCx.act F (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl n k.succ) z) := by
    intro k
    rw [hcup, GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_back_high, hback]
    congr 1
    exact congrArg (fun θ : Fin 2 →o Fin (n + 1 + 2) => GlobalTheory.CompanionTheory.HodgeCx.act F θ y)
      (GlobalTheory.CompanionTheory.HopfLe.DnCup.dl_front_high n k)
  simp only [MainStatements.Hodge.dn, LinearMap.sum_apply, LinearMap.smul_apply]
  rw [sum_fin_add_two_eq_zero_add_one_add_sum (m := n + 1), sum_fin_add_two_eq_zero_add_sum_succ (m := n), h0, h1]
  simp only [hk]

  simp only [hface, GlobalTheory.CompanionTheory.HopfLe.cup1, map_add (f := _), map_neg, map_sum, map_smul, map_zsmul,
  mul_add, Finset.mul_sum, mul_smul_comm, Fin.val_zero, Fin.val_one, Fin.val_succ, pow_zero,
  pow_one, pow_succ, one_smul, neg_smul, mul_neg, mul_one, neg_neg, Finset.sum_neg_distrib]
  rw [key]
  abel

end GlobalTheory.CompanionTheory.HopfLe.DnCup
end
end

section

open CategoryTheory TensorProduct GlobalTheory.CatCoh MainStatements.Hodge GlobalTheory.CompanionTheory.HodgeCx GlobalTheory.CompanionTheory.HopfLe

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.HopfLe.PrismComb

def stepMap (q n : ℕ) : Fin (q + 2) →o Fin 2 :=
  ⟨fun x ↦ if (x : ℕ) < n then 0 else 1, fun a b h ↦ by
    have h' : (a : ℕ) ≤ b := h
    dsimp only
    split_ifs with h1 h2 h2
    · exact le_rfl
    · exact Fin.zero_le _
    · omega
    · exact le_rfl⟩

theorem th_apply (q : ℕ) (i : Fin (q + 1)) (x : Fin (q + 2)) :
    th q i x = if (x : ℕ) ≤ i then 0 else 1 := by
  change (if x ≤ i.castSucc then (0 : Fin 2) else 1) = _
  simp only [Fin.le_def, Fin.val_castSucc]

theorem val_succAbove {n : ℕ} (j : Fin (n + 1)) (x : Fin n) :
    ((j.succAbove x : Fin (n + 1)) : ℕ) = if (x : ℕ) < j then (x : ℕ) else x + 1 := by
  unfold Fin.succAbove
  simp only [Fin.lt_def, Fin.val_castSucc]
  split_ifs <;> simp

theorem val_predAbove {n : ℕ} (i : Fin n) (x : Fin (n + 1)) :
    ((Fin.predAbove i x : Fin n) : ℕ) = if (i : ℕ) < x then (x : ℕ) - 1 else x := by
  unfold Fin.predAbove
  simp only [Fin.lt_def, Fin.val_castSucc]
  split_ifs <;> simp

theorem val_sg (q : ℕ) (i : Fin (q + 1)) (x : Fin (q + 2)) :
    ((sg q i x : Fin (q + 1)) : ℕ) = if (i : ℕ) < x then (x : ℕ) - 1 else x :=
  val_predAbove i x

theorem th_diag (q : ℕ) (i : Fin (q + 2)) :
    (th (q + 1) i).comp (Fin.succAboveOrderEmb i.castSucc).toOrderHom = stepMap q i := by
  ext x
  have e : ((th (q + 1) i).comp (Fin.succAboveOrderEmb i.castSucc).toOrderHom) x =
      th (q + 1) i (i.castSucc.succAbove x) := rfl
  rw [e, th_apply]
  change _ = ((if (x : ℕ) < i then (0 : Fin 2) else 1 : Fin 2) : ℕ)
  rw [val_succAbove]
  simp only [Fin.val_castSucc]
  split_ifs <;> first | rfl | omega

theorem th_next (q : ℕ) (i : Fin (q + 2)) :
    (th (q + 1) i).comp (Fin.succAboveOrderEmb i.succ).toOrderHom = stepMap q (i + 1) := by
  ext x
  have e : ((th (q + 1) i).comp (Fin.succAboveOrderEmb i.succ).toOrderHom) x =
      th (q + 1) i (i.succ.succAbove x) := rfl
  rw [e, th_apply]
  change _ = ((if (x : ℕ) < i + 1 then (0 : Fin 2) else 1 : Fin 2) : ℕ)
  rw [val_succAbove]
  simp only [Fin.val_succ]
  split_ifs <;> first | rfl | omega

theorem sg_diag (q : ℕ) (i : Fin (q + 2)) :
    (sg (q + 1) i).comp (Fin.succAboveOrderEmb i.castSucc).toOrderHom = OrderHom.id := by
  ext x
  have e : ((sg (q + 1) i).comp (Fin.succAboveOrderEmb i.castSucc).toOrderHom) x =
      sg (q + 1) i (i.castSucc.succAbove x) := rfl
  rw [e, val_sg, val_succAbove]
  simp only [Fin.val_castSucc, OrderHom.id_coe, id_eq]
  split_ifs <;> omega

theorem sg_next (q : ℕ) (i : Fin (q + 2)) :
    (sg (q + 1) i).comp (Fin.succAboveOrderEmb i.succ).toOrderHom = OrderHom.id := by
  ext x
  have e : ((sg (q + 1) i).comp (Fin.succAboveOrderEmb i.succ).toOrderHom) x =
      sg (q + 1) i (i.succ.succAbove x) := rfl
  rw [e, val_sg, val_succAbove]
  simp only [Fin.val_succ, OrderHom.id_coe, id_eq]
  split_ifs <;> omega

theorem stepMap_zero (q : ℕ) : stepMap q 0 = cst (q + 1) 1 := by
  ext x
  simp [stepMap, cst]
  rfl

theorem stepMap_top (q : ℕ) : stepMap q (q + 2) = cst (q + 1) 0 := by
  ext x
  have := x.2
  simp [stepMap, cst, this]
  rfl

theorem th_off (q : ℕ) (i : Fin (q + 2)) (k : Fin (q + 1)) :
    (th (q + 1) i).comp (Fin.succAboveOrderEmb (i.castSucc.succAbove (i.succAbove k))).toOrderHom =
      th q (Fin.predAbove k i) := by
  ext x
  have e : ((th (q + 1) i).comp
      (Fin.succAboveOrderEmb (i.castSucc.succAbove (i.succAbove k))).toOrderHom) x =
      th (q + 1) i ((i.castSucc.succAbove (i.succAbove k)).succAbove x) := rfl
  rw [e, th_apply, th_apply]
  congr 2
  simp only [val_succAbove, val_predAbove, Fin.val_castSucc, eq_iff_iff]
  split_ifs <;> omega

theorem sg_off (q : ℕ) (i : Fin (q + 2)) (k : Fin (q + 1)) :
    (sg (q + 1) i).comp (Fin.succAboveOrderEmb (i.castSucc.succAbove (i.succAbove k))).toOrderHom =
      (Fin.succAboveOrderEmb (i.succAbove k)).toOrderHom.comp (sg q (Fin.predAbove k i)) := by
  ext x
  have e : ((sg (q + 1) i).comp
      (Fin.succAboveOrderEmb (i.castSucc.succAbove (i.succAbove k))).toOrderHom) x =
      sg (q + 1) i ((i.castSucc.succAbove (i.succAbove k)).succAbove x) := rfl
  have e' : ((Fin.succAboveOrderEmb (i.succAbove k)).toOrderHom.comp (sg q (Fin.predAbove k i))) x =
      (i.succAbove k).succAbove (sg q (Fin.predAbove k i) x) := rfl
  rw [e, e']
  simp only [val_sg, val_succAbove, val_predAbove, Fin.val_castSucc]
  split_ifs <;> omega

theorem sign_off (q : ℕ) (i : Fin (q + 2)) (k : Fin (q + 1)) :
    ((-1 : ℤ) ^ ((i : ℕ) + ((i.castSucc.succAbove (i.succAbove k) : Fin (q + 3)) : ℕ))) =
      -((-1 : ℤ) ^ (((Fin.predAbove k i : Fin (q + 1)) : ℕ) + ((i.succAbove k : Fin (q + 2)) : ℕ))) := by
  simp only [val_succAbove, val_predAbove, Fin.val_castSucc]
  by_cases h : (k : ℕ) < i
  · obtain ⟨m, hm⟩ : ∃ m, (i : ℕ) = m + 1 := ⟨(i : ℕ) - 1, by omega⟩
    rw [if_pos h, if_pos h, if_pos (by omega), hm]
    simp [pow_add, pow_succ]
  · rw [if_neg h, if_neg (by omega), if_neg (by omega)]
    simp [pow_add, pow_succ]

def fwd (q : ℕ) (p : Fin (q + 2) × Fin (q + 1)) : Fin (q + 1) × Fin (q + 2) :=
  (Fin.predAbove p.2 p.1, p.1.succAbove p.2)

def bwd (q : ℕ) (p : Fin (q + 1) × Fin (q + 2)) : Fin (q + 2) × Fin (q + 1) :=
  (⟨if (p.2 : ℕ) ≤ p.1 then (p.1 : ℕ) + 1 else p.1, by have := p.1.2; split_ifs <;> omega⟩,
   ⟨if (p.2 : ℕ) ≤ p.1 then p.2 else (p.2 : ℕ) - 1, by have := p.1.2; have := p.2.2; split_ifs <;> omega⟩)

theorem bwd_fwd (q : ℕ) (p : Fin (q + 2) × Fin (q + 1)) : bwd q (fwd q p) = p := by
  refine Prod.ext (Fin.ext ?_) (Fin.ext ?_) <;>
  · simp only [bwd, fwd, val_succAbove, val_predAbove]
    split_ifs <;> omega

theorem fwd_bwd (q : ℕ) (p : Fin (q + 1) × Fin (q + 2)) : fwd q (bwd q p) = p := by
  refine Prod.ext (Fin.ext ?_) (Fin.ext ?_) <;>
  · simp only [bwd, fwd, val_succAbove, val_predAbove]
    split_ifs <;> omega

theorem prism_faces {A : Type} [AddCommGroup A] (q : ℕ)
    (B : (Fin (q + 2) →o Fin 2) → (Fin (q + 2) →o Fin (q + 2)) → A) :
    ∑ i : Fin (q + 2), ∑ j : Fin (q + 3), ((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ))) •
        B ((th (q + 1) i).comp (Fin.succAboveOrderEmb j).toOrderHom)
          ((sg (q + 1) i).comp (Fin.succAboveOrderEmb j).toOrderHom) =
      B (cst (q + 1) 1) OrderHom.id - B (cst (q + 1) 0) OrderHom.id -
        ∑ j : Fin (q + 2), ∑ i : Fin (q + 1), ((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ))) •
          B (th q i) ((Fin.succAboveOrderEmb j).toOrderHom.comp (sg q i)) := by
  have h1 : ∀ i : Fin (q + 2), ∑ j : Fin (q + 3), ((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ))) •
        B ((th (q + 1) i).comp (Fin.succAboveOrderEmb j).toOrderHom)
          ((sg (q + 1) i).comp (Fin.succAboveOrderEmb j).toOrderHom) =
      (B (stepMap q i) OrderHom.id - B (stepMap q (i + 1)) OrderHom.id) -
        ∑ k : Fin (q + 1), ((-1 : ℤ) ^ (((Fin.predAbove k i : Fin (q + 1)) : ℕ) +
            ((i.succAbove k : Fin (q + 2)) : ℕ))) •
          B (th q (Fin.predAbove k i))
            ((Fin.succAboveOrderEmb (i.succAbove k)).toOrderHom.comp (sg q (Fin.predAbove k i))) := by
    intro i
    rw [Fin.sum_univ_succAbove _ i.castSucc, Fin.sum_univ_succAbove _ i,
      Fin.succAbove_castSucc_self, th_diag, sg_diag, th_next, sg_next]
    have e1 : ((-1 : ℤ) ^ ((i : ℕ) + ((i.castSucc : Fin (q + 3)) : ℕ))) = 1 := by
      simp [Even.neg_one_pow, ← two_mul]
    have e2 : ((-1 : ℤ) ^ ((i : ℕ) + ((i.succ : Fin (q + 3)) : ℕ))) = -1 := by
      simp [← add_assoc, ← two_mul, pow_succ]
    rw [e1, e2, one_smul, neg_smul, one_smul]
    have e3 : ∀ k : Fin (q + 1),
        ((-1 : ℤ) ^ ((i : ℕ) + ((i.castSucc.succAbove (i.succAbove k) : Fin (q + 3)) : ℕ))) •
          B ((th (q + 1) i).comp
              (Fin.succAboveOrderEmb (i.castSucc.succAbove (i.succAbove k))).toOrderHom)
            ((sg (q + 1) i).comp
              (Fin.succAboveOrderEmb (i.castSucc.succAbove (i.succAbove k))).toOrderHom) =
        -(((-1 : ℤ) ^ (((Fin.predAbove k i : Fin (q + 1)) : ℕ) +
            ((i.succAbove k : Fin (q + 2)) : ℕ))) •
          B (th q (Fin.predAbove k i))
            ((Fin.succAboveOrderEmb (i.succAbove k)).toOrderHom.comp (sg q (Fin.predAbove k i)))) := by
      intro k
      rw [th_off, sg_off, sign_off, neg_smul]
    simp only [e3, Finset.sum_neg_distrib]
    abel
  have h2 : ∑ i : Fin (q + 2), (B (stepMap q i) OrderHom.id - B (stepMap q (i + 1)) OrderHom.id) =
      B (cst (q + 1) 1) OrderHom.id - B (cst (q + 1) 0) OrderHom.id := by
    rw [Fin.sum_univ_eq_sum_range (fun n ↦ B (stepMap q n) OrderHom.id - B (stepMap q (n + 1)) OrderHom.id),
      Finset.sum_range_sub', stepMap_zero, stepMap_top]
  have h3 : ∑ i : Fin (q + 2), ∑ k : Fin (q + 1),
        ((-1 : ℤ) ^ (((Fin.predAbove k i : Fin (q + 1)) : ℕ) + ((i.succAbove k : Fin (q + 2)) : ℕ))) •
          B (th q (Fin.predAbove k i))
            ((Fin.succAboveOrderEmb (i.succAbove k)).toOrderHom.comp (sg q (Fin.predAbove k i))) =
      ∑ j : Fin (q + 2), ∑ i : Fin (q + 1), ((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ))) •
          B (th q i) ((Fin.succAboveOrderEmb j).toOrderHom.comp (sg q i)) := by
    rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin (q + 2))))
        (t := (Finset.univ : Finset (Fin (q + 1)))) (f := fun j i ↦ ((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ))) •
          B (th q i) ((Fin.succAboveOrderEmb j).toOrderHom.comp (sg q i))),
      ← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
    exact Finset.sum_nbij' (fwd q) (bwd q) (fun _ _ ↦ Finset.mem_univ _) (fun _ _ ↦ Finset.mem_univ _)
      (fun p _ ↦ bwd_fwd q p) (fun p _ ↦ fwd_bwd q p) (fun _ _ ↦ rfl)
  simp only [h1, Finset.sum_sub_distrib] at h2 ⊢
  rw [h2, h3]

end GlobalTheory.CompanionTheory.HopfLe.PrismComb
end

section

open GlobalTheory.PRep GlobalTheory.BZMir GroundTheory.LocalField Matrix GlobalTheory.CompanionTheory.MirFourier

theorem _root_.GlobalTheory.T.twisted_kernel_of_small_box_character : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (Multiplicative (Fin n → k)) V), IsSmooth ρ → ∀ (v : V) (N J : ℤ), J ≤ N → (∀ x ∈ box k n N, ρ x v = v) → (∀ a : Fin n → k, (∀ i, a i ∈ valBall k (addCharConductor ψ - N)) → v ∈ twKer ρ (box k n J) (chiOn k ψ a (box k n J))) → v = 0 := by
  first | exact @GlobalTheory.CompanionTheory.MirFourier.FiniteInversion.fourier_finite | exact GlobalTheory.CompanionTheory.MirFourier.FiniteInversion.fourier_finite | (intros; apply GlobalTheory.CompanionTheory.MirFourier.FiniteInversion.fourier_finite <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.BasisBase

theorem sqC_zK : ∀ {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {I : Ideal A} (γ : DividedPowers I) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (l s : ℕ) (𝒱 : Set X.Opens) (a : A) (t u r : ℤ) (ht : t ≤ 0)
    (ha : (smO γ q l s 𝒱).LeC a (sFil _ t) (sFil _ 0)) (hb : (smO γ q l s 𝒱).LeC a (sFil _ u) (sFil _ r)) (j : ℕ)
    (x : HdR q j),
    ((smO γ q l s 𝒱).sqC a ha hb).pull j (GlobalTheory.CompanionTheory.BasisBase.zK q (TO q l s 𝒱) t u ht j x) =
      quoM (TS γ q l s 𝒱) r j (a • muB γ q l s 𝒱 j x) := by
  intro O A _ _ _ I γ X q l s 𝒱 a t u r ht ha hb j x
  obtain ⟨⟨f, hf⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [map_smul]
  change Submodule.Quotient.mk _ = a • Submodule.Quotient.mk _
  rw [← Submodule.Quotient.mk_smul]
  refine congrArg _ (Subtype.ext (funext fun c => ?_))
  refine Subtype.ext ?_
  exact congrArg (Ideal.Quotient.mk _) (Algebra.smul_def _ _).symm

end GlobalTheory.CompanionTheory.BasisBase
end

section

open ReciprocityTheory.Ty.Fin

theorem _root_.GlobalTheory.T.central_idempotent_properties : ReciprocityTheory.Ty.Fin.St.ZIdemFacts := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.zIdemFacts | exact GlobalTheory.CompanionTheory.TyFin.zIdemFacts | (intros; apply GlobalTheory.CompanionTheory.TyFin.zIdemFacts <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.basic_open_eval_surjective : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N), IsClosedImmersion i → ∀ {g : MvPolynomial (Fin (N + 1)) K} {e : ℕ} (hg : g ∈ grK K N e), 0 < e → Function.Surjective (evV i g (i ⁻¹ᵁ Proj.basicOpen (grK K N) g) le_rfl) := by
  first | exact @GlobalTheory.CompanionTheory.Geo.evV_surjective | exact GlobalTheory.CompanionTheory.Geo.evV_surjective | (intros; apply GlobalTheory.CompanionTheory.Geo.evV_surjective <;> assumption)
end
