module

public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.HookKeyOrderGeOne
public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.IdentityLiftWeightedHomog
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Lemma44IdentityOfRawTail
public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.NormalWeightCovectorZero
public import Formalism.SharpRestriction.GrowthBounds.WittFrameLocaliserOrders
public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.Bundle005
public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.Bundle002
public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.RestSegCoreOfNum
public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.TCGlue
public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.TCXNum
import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle009
public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.Bundle003
public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.ZeroOfMultideg
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.LemmaBAlt

section H

variable {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Algebra (WF X.p X.n') O]

def hTop (O : Type) [CommRing O] [IsDomain O] (X : Loc) (x : X.TT) : RHH O X := hKey O (X.m + 1) (x, true) (x, false)

def dgH {X : Loc} (x : X.TT) : X.TT × Bool → ℕ := fun l => dX (x, true) l + dX (x, false) l

def EhatT (O : Type) [CommRing O] [IsDomain O] (X : Loc) (x : X.TT) (P : ℕ) : RHH O X :=
  MvPolynomial.X ((x, true), 0) ^ P * MvPolynomial.X ((x, false), 0) ^ P +
    ∑ c : Fin X.m, MvPolynomial.X ((x, true), c.succ) ^ P * MvPolynomial.X ((x, false), c.succ) ^ P

theorem hTop_eq (x : X.TT) : hTop O X x = MvPolynomial.X ((x, true), 0) * MvPolynomial.X ((x, false), 0) +
    ∑ c : Fin X.m, MvPolynomial.X ((x, true), c.succ) * MvPolynomial.X ((x, false), c.succ) := by
  rw [hTop, hKey, Fin.sum_univ_succ]

theorem EhatT_one (x : X.TT) : EhatT O X x 1 = hTop O X x := by
  rw [EhatT, hTop_eq]
  simp only [pow_one]

private theorem X_true_mul_X_false_pow_mem_Pol (x : X.TT) (a : Fin (X.m + 1)) (P : ℕ) :
    (MvPolynomial.X ((x, true), a) * MvPolynomial.X ((x, false), a) : RHH O X) ^ P ∈
      Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (fun l => P * dgH x l) := by
  classical
  rw [show (MvPolynomial.X ((x, true), a) * MvPolynomial.X ((x, false), a) : RHH O X) ^ P =
      monomial (P • (Finsupp.single ((x, true), a) 1 + Finsupp.single ((x, false), a) 1)) 1 by
    rw [MvPolynomial.X, MvPolynomial.X, monomial_mul, monomial_pow, one_mul, one_pow]]
  rw [Pol, MvPolynomial.mem_restrictSupport_iff]
  intro m hm
  have hm' := support_monomial_subset hm
  rw [Finset.mem_singleton] at hm'
  subst hm'
  intro l
  simp only [multideg, dgH, dX, Finsupp.smul_apply, Finsupp.add_apply, Finsupp.single_apply, Prod.mk.injEq,
    smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum, mul_add]
  congr 1 <;> split_ifs with h <;> simp [h]

theorem hTop_pol (x : X.TT) : hTop O X x ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (dgH x) := by
  have e : hTop O X x = ∑ a : Fin (X.m + 1),
      (MvPolynomial.X ((x, true), a) * MvPolynomial.X ((x, false), a) : RHH O X) ^ 1 := by
    rw [hTop_eq, Fin.sum_univ_succ]
    simp only [pow_one]
  rw [e]
  refine Submodule.sum_mem _ (fun a _ => ?_)
  have h := X_true_mul_X_false_pow_mem_Pol (O := O) x a 1
  simp only [one_mul] at h
  exact h

theorem hTop_nd (x : X.TT) : IsWeightedHomogeneous (wN X) (hTop O X x) 1 := by
  rw [hTop_eq]
  have hpair : ∀ a : Fin (X.m + 1), IsWeightedHomogeneous (wN X)
      (MvPolynomial.X ((x, true), a) * MvPolynomial.X ((x, false), a) : RHH O X) 1 := by
    intro a
    have h1 := (isWeightedHomogeneous_X (KK O) (wN X) ((x, true), a)).mul
      (isWeightedHomogeneous_X (KK O) (wN X) ((x, false), a))
    have hw : wN X ((x, true), a) + wN X ((x, false), a) = 1 := by
      rcases Nat.lt_or_ge a.val 1 with h | h
      · have h' : ¬ 1 ≤ a.val := by omega
        simp [wN, h, h']
      · have h' : ¬ a.val < 1 := by omega
        simp [wN, h, h']
    rwa [hw] at h1
  refine (hpair 0).add (IsWeightedHomogeneous.sum _ _ _ (fun c _ => hpair c.succ))

private theorem X_mem_intSub' (v : VarH X) : (MvPolynomial.X v : RHH O X) ∈ intSub O (VarH X) := by
  classical
  change ∀ m, ∃ a : O, (MvPolynomial.X v : RHH O X).coeff m = algebraMap O (KK O) ((1 : O) ^ (0 : ℕ) * a)
  intro m
  rw [MvPolynomial.coeff_X']
  split_ifs
  · exact ⟨1, by simp⟩
  · exact ⟨0, by simp⟩

theorem hTop_int (x : X.TT) : hTop O X x ∈ intSub O (VarH X) := by
  rw [hTop_eq]
  exact add_mem (mul_mem (X_mem_intSub' _) (X_mem_intSub' _))
    (sum_mem fun c _ => mul_mem (X_mem_intSub' _) (X_mem_intSub' _))

theorem hTop_inA (x : X.TT) : InA (hTop O X x) := by
  have h := hTop_int (O := O) x
  change ∀ m, ∃ a : O, (hTop O X x).coeff m = algebraMap O (KK O) ((1 : O) ^ (0 : ℕ) * a) at h
  intro m
  obtain ⟨a, ha⟩ := h m
  exact ⟨a, by rw [ha, pow_zero, one_mul]⟩

theorem hTop_lift (w : O) (x : X.TT) : lift1 X O w (hTop O X x) = w • hTop O X x := by
  rw [identity_lift_normal_homog w (hTop_nd x), pow_one]

theorem hTop_ord (w : O) (x : X.TT) (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) (hg : IsGLW g) :
    InWjRg X.p X.n' O w 1 (hhLetters X.TT) g (hTop O X x) 1 := by
  exact hook_key_order_ge_one w (hhLetters X.TT) 1 g hg (x, true) (x, false) rfl rfl rfl

theorem softOK_hTop (w : O) (x : X.TT) : SoftOK w (hTop O X x) 1 (hTop O X x) (dgH x) := by
  exact
    { fac := IsFac.of_exact (e := 1) (r := 0) (hTop_inA x) (fun g hg => hTop_ord w x g hg) le_rfl (hTop_inA x)
        ((inA_iff_wj w).2 (wjSub w 0).zero_mem) (by
          have := hTop_lift w x
          rw [smul_zero, add_zero, pow_one]
          exact this)
      sgHom := ndHom_iff.2 (hTop_nd x)
      liftPol := identity_lift_mem_Pol _ (hTop_pol x)
      sgPol := hTop_pol x }

theorem EhatT_eq_sum (x : X.TT) (P : ℕ) :
    EhatT O X x P = ∑ a : Fin (X.m + 1), (MvPolynomial.X ((x, true), a) * MvPolynomial.X ((x, false), a) : RHH O X) ^ P := by
  rw [EhatT, Fin.sum_univ_succ]
  simp only [mul_pow]

theorem EhatT_int (x : X.TT) (P : ℕ) : EhatT O X x P ∈ intSub O (VarH X) := by
  rw [EhatT_eq_sum]
  exact sum_mem fun a _ => pow_mem (mul_mem (X_mem_intSub' _) (X_mem_intSub' _)) _

theorem EhatT_wh (wt : VarH X → ℕ) (n : ℕ) (x : X.TT) (P : ℕ) (h : ∀ a, wt ((x, true), a) + wt ((x, false), a) = n) :
    IsWeightedHomogeneous wt (EhatT O X x P) (P * n) := by
  rw [EhatT_eq_sum]
  refine IsWeightedHomogeneous.sum _ _ _ (fun a _ => ?_)
  have h1 := ((isWeightedHomogeneous_X (KK O) wt ((x, true), a)).mul
    (isWeightedHomogeneous_X (KK O) wt ((x, false), a))).pow P
  rwa [h a, smul_eq_mul] at h1

theorem hpow_congr (S : UniformizedDVR X.p O) (hS : S.SqP) (x : X.TT) (e : ℕ) :
    InWj S.w (hTop O X x ^ (X.p ^ e) - EhatT O X x (X.p ^ e)) 1 := by
  classical
  set D : MvPolynomial (VarH X) O :=
    (∑ a : Fin (X.m + 1), MvPolynomial.X ((x, true), a) * MvPolynomial.X ((x, false), a)) ^ (X.p ^ e) -
      ∑ a : Fin (X.m + 1), (MvPolynomial.X ((x, true), a) * MvPolynomial.X ((x, false), a)) ^ (X.p ^ e) with hDdef
  have hD : hTop O X x ^ (X.p ^ e) - EhatT O X x (X.p ^ e) = MvPolynomial.map (algebraMap O (KK O)) D := by
    rw [EhatT_eq_sum, ← EhatT_one, EhatT_eq_sum, hDdef]

    simp only [map_sub, map_pow, map_sum, map_mul, map_X, pow_one]
  rw [hD]
  apply Formalism.MainNotions.G.WittFrameLocaliserOrders.residue_zero_mem_order_one S
  have hp0 : ((X.p : ℕ) : IsLocalRing.ResidueField O) = 0 := by
    rw [← map_natCast (IsLocalRing.residue O), IsLocalRing.residue_eq_zero_iff]
    exact S.p_mem
  haveI : CharP (IsLocalRing.ResidueField O) X.p := (CharP.charP_iff_prime_eq_zero Fact.out).2 hp0
  rw [hDdef]

  simp only [map_sub, map_pow, map_sum, map_mul, map_X]
  rw [sum_pow_char_pow, sub_self]

theorem softH (S : UniformizedDVR X.p O) (hS : S.SqP) (x : X.TT) (e : ℕ) :
    SoftOK S.w (hTop O X x ^ (X.p ^ e)) (X.p ^ e) (EhatT O X x (X.p ^ e)) (fun l => X.p ^ e * dgH x l) := by
  exact
    { fac := by
        have := ((softOK_hTop S.w x).pow (X.p ^ e)).fac
        rw [mul_one] at this
        exact this.congr_sg (hpow_congr S hS x e) ((mem_intSub O _).1 (EhatT_int x _))
      sgHom := ndHom_iff.2 (by
        have := EhatT_wh (O := O) (wN X) 1 x (X.p ^ e) (wN_pair x)
        rwa [mul_one] at this)
      liftPol := ((softOK_hTop S.w x).pow (X.p ^ e)).liftPol
      sgPol := mem_Pol_iff.2 fun l => EhatT_wh (wL X l) _ x _ fun _ => rfl }

theorem softHseg (S : UniformizedDVR X.p O) (hS : S.SqP) (C0 CE1 CE2 : ℝ) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) :
    SoftOK S.w (hTop O X (topOdd X j i) ^ ((X.seg C0 CE1 CE2 j).P X.p i)) ((X.seg C0 CE1 CE2 j).P X.p i)
      (EhatT O X (topOdd X j i) ((X.seg C0 CE1 CE2 j).P X.p i))
      (fun l => (X.seg C0 CE1 CE2 j).P X.p i * dgH (topOdd X j i) l) := by
  exact softH S hS (topOdd X j i) _

end H

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section

namespace Formalism.MainNotions.ColumnSystems.Pf

theorem restTCore : RestTCore := restTCore_of_seg (restSegCore_of_num restNumCore)

end Formalism.MainNotions.ColumnSystems.Pf
end

section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.G.PolBridge

section Mono

variable {σ : Type} {K : Type} [CommRing K]

def IsMono (P : MvPolynomial σ K) : Prop := ∃ M : σ →₀ ℕ, P = monomial M 1

theorem IsMono.one : IsMono (1 : MvPolynomial σ K) := ⟨0, rfl⟩

theorem IsMono.X (v : σ) : IsMono (MvPolynomial.X v : MvPolynomial σ K) := ⟨Finsupp.single v 1, rfl⟩

theorem IsMono.mul {P Q : MvPolynomial σ K} (hP : IsMono P) (hQ : IsMono Q) : IsMono (P * Q) := by
  obtain ⟨a, rfl⟩ := hP
  obtain ⟨b, rfl⟩ := hQ
  exact ⟨a + b, by rw [monomial_mul, one_mul]⟩

theorem IsMono.pow {P : MvPolynomial σ K} (hP : IsMono P) (n : ℕ) : IsMono (P ^ n) := by
  obtain ⟨a, rfl⟩ := hP
  exact ⟨n • a, by rw [monomial_pow, one_pow]⟩

theorem IsMono.prod {ι : Type} (s : Finset ι) (P : ι → MvPolynomial σ K) (h : ∀ i ∈ s, IsMono (P i)) :
    IsMono (∏ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsMono.one (σ := σ) (K := K)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

end Mono

section Std

variable (O : Type) [CommRing O] [IsDomain O] {C0 CE1 CE2 mu : ℝ} {X : Loc} [NeZero X.m] {β : GlobalTheory X}

theorem ioDXmono (j : Fin (numSeg X.TT)) (v : BVar (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t) :
    IsMono (ioD O C0 CE1 CE2 mu X β j (MvPolynomial.X v)) := by
  have e : ioD O C0 CE1 CE2 mu X β j (MvPolynomial.X v) =
      (MvPolynomial.X (symVar C0 CE1 CE2 X j v) : RHH O X) ^ symLev X.p C0 CE1 CE2 X j v := aeval_X _ _
  rw [e]
  exact (IsMono.X _).pow _

theorem LvDat.stdPoly_mono (L : LvDat C0 CE1 CE2 mu X β) (j : Fin (numSeg X.TT)) : IsMono (L.stdPoly O j) := by
  unfold LvDat.stdPoly
  refine (IsMono.mul ?_ ?_).mul ?_
  · unfold digitMon
    exact IsMono.prod _ _ fun i _ => IsMono.prod _ _ fun c _ => ((IsMono.X _).pow _).mul ((IsMono.X _).pow _)
  · unfold sTopMon
    refine IsMono.prod _ _ fun i _ => ?_
    split_ifs
    · exact ((IsMono.X _).pow _).mul ((IsMono.X _).pow _)
    · exact IsMono.one
  · simp only [map_mul, map_prod, map_pow]
    exact ((IsMono.prod _ _ fun i _ => (ioDXmono O j _).pow _).mul ((ioDXmono O j _).pow _)).mul
      (IsMono.prod _ _ fun c _ => (ioDXmono O j _).pow _)

theorem LvDat.exists_std (L : LvDat C0 CE1 CE2 mu X β) :
    ∃ Std : MonH X, (monomial Std (1 : KK O) : RHH O X) = ∏ j, L.stdPoly O j := by
  obtain ⟨M, hM⟩ := IsMono.prod Finset.univ (fun j => L.stdPoly O j) fun j _ => L.stdPoly_mono O j
  exact ⟨M, hM.symm⟩

end Std

theorem cov_count (s : ℕ) : ∑ i : Fin (2 * s + 1), (if decide ((i : ℕ) % 2 = 0) = true then 0 else 1) ≤ s := by
  classical
  have h1 : ∑ i : Fin (2 * s + 1), (if decide ((i : ℕ) % 2 = 0) = true then 0 else 1) =
      (Finset.univ.filter fun i : Fin (2 * s + 1) => ¬ (i : ℕ) % 2 = 0).card := by
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : (i : ℕ) % 2 = 0 <;> simp [h]
  rw [h1]
  refine (Finset.card_le_card_of_injOn (t := Finset.range s) (fun i : Fin (2 * s + 1) => (i : ℕ) / 2) ?_ ?_).trans
    (by simp)
  · intro i hi
    have h2 : ¬ (i : ℕ) % 2 = 0 := by simpa using hi
    have h3 := i.2
    simp only [Finset.coe_range, Set.mem_Iio]
    omega
  · intro a ha b hb hab
    have h2 : ¬ (a : ℕ) % 2 = 0 := by simpa using ha
    have h3 : ¬ (b : ℕ) % 2 = 0 := by simpa using hb
    have h4 : (a : ℕ) / 2 = (b : ℕ) / 2 := hab
    apply Fin.ext
    omega

section Psi

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {N r : ℕ} [NeZero r]

theorem psi_facts {D : Formalism.BasicNotions.D7} (hA2 : Formalism.MainNotions.CovariantDegrees.HyperplaneRank D) (hA3 : Formalism.MainNotions.CovariantDegrees.DefiniteRankOne D) {p : ℕ} [Fact p.Prime]
    (S : UniformizedDVR p O) (LL : ChainLetters N) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (hJ : ∀ k, J k ≤ N)
    (x : Tx r LL) (hx : x ∈ sAll LL J M) :
    psiR (KK O) LL x ≠ 0 ∧ ∀ k, psiR (KK O) LL x ∈ YCond (KK O) (r := r) LL (J k) (M k) := by
  have hp : p.Prime := Fact.out
  have hKz : CharZero (KK O) := dvr_fraction_field_charZero S hp
  obtain ⟨hli, hspan⟩ := hA2 O N r (⟨LL.vec⟩ : Letters (Fin N)) LL.deg
  have hli' : LinearIndependent O (psiR (r := r) O LL) := hli
  have hrange : Submodule.span O (Set.range (psiR (r := r) O LL)) = Pol O r LL.deg := by
    rw [← hspan]
    congr 1
    ext G
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨x.1.1, x.1.2, x.2, rfl⟩
    · rintro ⟨P, I, h, rfl⟩; exact ⟨⟨(P, I), h⟩, rfl⟩
  have hfin : Finite (Tx r LL) := tx_finite LL hli' hrange
  obtain ⟨Bd, hBd⟩ := exists_bound (r := r) (Lt := (⟨LL.vec⟩ : Letters (Fin N))) (B := LL.deg)
  have hC1 := one_cond D LL hrange hspan (fun th M => (hA3 p O S N r _ LL.deg th M).1) Bd hBd J M hJ
  refine ⟨(psiK_li LL hli').ne_zero x, fun k => ?_⟩
  rw [← psiR_map]
  exact (hC1 k _ (psiK_mem LL hrange x).1).2 (Submodule.subset_span ⟨x, hx k, rfl⟩)

end Psi

theorem facSysAt_of {D : Formalism.BasicNotions.D7} (hA2 : Formalism.MainNotions.CovariantDegrees.HyperplaneRank D) (hA3 : Formalism.MainNotions.CovariantDegrees.DefiniteRankOne D)
    {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ} (hC : ColsAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc)
    (hP : PreAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) (hT : TCoreAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) :
    FacSysAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  intro X _ _ O _ _ _ _ S hSq hD1 hHI hCB mm hmm n hn1 hnc β hβ s hs
  have hp : X.p.Prime := Fact.out
  haveI hKz : CharZero (KK O) := dvr_fraction_field_charZero S hp
  simp only [colGens, Set.mem_setOf_eq] at hs
  choose lv jp hOK y hy γ hγ hx using hs
  let L : LvDat C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β := ⟨lv, jp, hOK, γ, hγ⟩
  have hs' : s = fun j => L.word O j (psiR (KK O) (L.LL j) (y j)) := funext fun j => hx j
  obtain ⟨Std, hStd⟩ := L.exists_std O
  have hfacts := fun j => psi_facts hA2 hA3 S (L.LL j) (BDk C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j).T.J
    (BDk C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j).T.thr (blockData_J_le _ _ _ _ _ _) (y j) (hy j)
  have CS := fun j => (hC X O S hSq hD1 hHI hCB mm hmm n hn1 hnc β hβ L j (y j) (hy j)).some
  obtain ⟨P⟩ := hP X O S hSq hD1 hHI hCB mm hmm n hn1 hnc β hβ L _ CS (fun j => (hfacts j).1) Std hStd
  rw [hs']
  exact ⟨P.toFacSys D hStd (hT X O S hSq hD1 hHI hCB mm hmm n hn1 hnc β hβ L Std hStd) (fun j => (hfacts j).1)
    (fun j => (hfacts j).2) (fun j => (cov_count (segS X.TT j)).trans (hHI.1.2.2.2.2.1 j).2)⟩

theorem restFacSys_of {D : Formalism.BasicNotions.D7} (hA : admitted D) (hC : RestCols) (hP : RestPre) (hT : RestTCore) : FacSysCondition :=
  TransportedAlt.mono (fun _ _ _ _ _ _ _ _ _ _ h =>
    facSysAt_of (D := D) hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hA.2.2.2.2.2.1 h.1.1 h.1.2 h.2) ((hC.and hP).and hT)

theorem rest_assumptions_of_three_interfaces {D : Formalism.BasicNotions.D7} (hA : admitted D) (hC : RestCols) (hP : RestPre) (hT : RestTCore) : RestAsmRT :=
  restAsmRT_of_facSys hA (restFacSys_of hA hC hP hT)

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

abbrev IM (X : Loc) := (Σ j : Fin (numSeg X.TT), Fin (segS X.TT j)) ⊕
  ((Σ j : Fin (numSeg X.TT), Fin (segS X.TT j) × Fin X.m) ⊕ ((Σ j : Fin (numSeg X.TT), Fin (segS X.TT j)) ⊕ Fin X.m))

def multMk (X : Loc) (β : GlobalTheory X) : IM X → ℕ
  | Sum.inl x => (β x.1).sg x.2
  | Sum.inr (Sum.inl x) => (β x.1).rz x.2.1 x.2.2.succ
  | Sum.inr (Sum.inr (Sum.inl x)) => (β x.1).ry x.2 0
  | Sum.inr (Sum.inr (Sum.inr _)) => X.c

def fMk (O : Type) [CommRing O] [IsDomain O] (C0 CE1 CE2 : ℝ) (X : Loc) : IM X → RHH O X
  | Sum.inl x => kSkey O X x.1 x.2 ^ (X.seg C0 CE1 CE2 x.1).P X.p x.2
  | Sum.inr (Sum.inl x) => kWkey O X x.1 x.2.1 x.2.2.succ
  | Sum.inr (Sum.inr (Sum.inl x)) => kSkey O X x.1 x.2
  | Sum.inr (Sum.inr (Sum.inr c)) => locC O X c.succ

def aMk (C0 CE1 CE2 : ℝ) (X : Loc) : IM X → MonH X
  | Sum.inl x => Finsupp.single ((topStart X x.1, true), 0) (X.p ^ segG X.TT x.1) +
      Finsupp.single ((topOdd X x.1 x.2, false), 0) ((X.seg C0 CE1 CE2 x.1).P X.p x.2)
  | Sum.inr (Sum.inl x) => Finsupp.single ((topOdd X x.1 x.2.1, true), x.2.2.succ) 1 +
      Finsupp.single ((topStart X x.1, true), 0) (X.p ^ (segDists X.TT x.1).get x.2.1)
  | Sum.inr (Sum.inr (Sum.inl x)) => Finsupp.single ((topStart X x.1, true), 0) (X.p ^ (segDists X.TT x.1).get x.2) +
      Finsupp.single ((topOdd X x.1 x.2, false), 0) 1
  | Sum.inr (Sum.inr (Sum.inr _)) => ∑ j : Fin (numSeg X.TT), Finsupp.single ((topStart X j, true), 0) (X.p ^ segG X.TT j - 1)

def oMk (C0 CE1 CE2 : ℝ) (X : Loc) : IM X → ℕ
  | Sum.inl x => (X.seg C0 CE1 CE2 x.1).P X.p x.2
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr (Sum.inl _)) => 1
  | Sum.inr (Sum.inr (Sum.inr _)) => 0

def dgMk (C0 CE1 CE2 : ℝ) (X : Loc) : IM X → X.TT × Bool → ℕ
  | Sum.inl x => fun l => (X.seg C0 CE1 CE2 x.1).P X.p x.2 * dgKS X x.1 x.2 l
  | Sum.inr (Sum.inl x) => dgKW X x.1 x.2.1
  | Sum.inr (Sum.inr (Sum.inl x)) => dgKS X x.1 x.2
  | Sum.inr (Sum.inr (Sum.inr _)) => dgLoc X

def bMk (C0 CE1 CE2 : ℝ) (X : Loc) (β : GlobalTheory X) (j : Fin (numSeg X.TT)) : MonH X :=
  Finsupp.single ((topStart X j, true), 0) (X.p ^ segG X.TT j * (∑ i : Fin (segS X.TT j), (β j).sg i) +
      (∑ i : Fin (segS X.TT j), X.p ^ (segDists X.TT j).get i * ((∑ c : Fin X.m, (β j).rz i c.succ) + (β j).ry i 0)) +
      X.c * (X.m * (X.p ^ segG X.TT j - 1))) +
    (∑ i : Fin (segS X.TT j), Finsupp.single ((topOdd X j i, false), 0)
      ((X.seg C0 CE1 CE2 j).P X.p i * (β j).sg i + (β j).ry i 0)) +
    ∑ i : Fin (segS X.TT j), ∑ c : Fin X.m, Finsupp.single ((topOdd X j i, true), c.succ) ((β j).rz i c.succ)

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

theorem pd_mul_P (X : Loc) (C0 CE1 CE2 : ℝ) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) :
    X.p ^ (segDists X.TT j).get i * (X.seg C0 CE1 CE2 j).P X.p i = X.p ^ segG X.TT j := by
  have hmem : (segDists X.TT j).get i ∈ segDists X.TT j := List.get_mem _ _
  have hlt : (segDists X.TT j).get i < segG X.TT j := by
    generalize (segDists X.TT j).get i = x at hmem ⊢
    unfold segDists at hmem
    rw [Finset.mem_sort, Finset.mem_image] at hmem
    obtain ⟨s, hs, rfl⟩ := hmem
    exact (Finset.mem_filter.mp hs).2.2.2
  simp only [Formalism.MainNotions.ColumnSystems.Loc.seg, SegData.P, segData]
  rw [← pow_add, Nat.add_sub_cancel' hlt.le]

theorem sgKS_powP {X : Loc} {O : Type} [CommRing O] [IsDomain O] (C0 CE1 CE2 : ℝ) (j : Fin (numSeg X.TT))
    (i : Fin (segS X.TT j)) :
    sgKS O X j i ^ ((X.seg C0 CE1 CE2 j).P X.p i) = MvPolynomial.X ((topStart X j, true), 0) ^ (X.p ^ segG X.TT j) *
      MvPolynomial.X ((topOdd X j i, false), 0) ^ ((X.seg C0 CE1 CE2 j).P X.p i) := by
  unfold sgKS
  rw [mul_pow, ← pow_mul, pd_mul_P X C0 CE1 CE2 j i]

end Formalism.MainNotions.ColumnSystems.Pf
end
end
