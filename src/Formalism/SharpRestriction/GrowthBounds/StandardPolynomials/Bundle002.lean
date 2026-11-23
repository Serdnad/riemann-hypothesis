module

public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.ColDef
public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.SymbolEq
public import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.LiftedColumnMultidegree
public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.MultidegAdd
import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.LiftSubstitutionCoeffDivisible
public import Formalism.SharpRestriction.GrowthBounds.PolBridge
import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle022
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CardEqChainSum
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

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.LemmaBAlt Formalism.MainNotions.ColumnSystems.Pf.Col

section

variable (C0 CE1 CE2 mu : ℝ) (X : Loc) (β : GlobalTheory X) (j : Fin (numSeg X.TT))

def zxS (l : Fin (segS X.TT j)) : ℕ :=
  coarseA X.p (X.seg C0 CE1 CE2 j) (β j) l -
    (if (l : ℕ) < (X.seg C0 CE1 CE2 j).sigma then (β j).w l else (β j).o l)

def a0Z : ℤ :=
  ⌊(((X.seg C0 CE1 CE2 j).A0 X.p : ℤ) : ℝ) - mu⌋ -
    ∑ l : Fin (segS X.TT j), (if (l : ℕ) < (X.seg C0 CE1 CE2 j).sigma then ((β j).sg l : ℤ) else 0)

def nuS (T : ℕ) : ℤ :=
  if T = 0 then 0 else a0Z C0 CE1 CE2 mu X β j +
    ∑ l : Fin (segS X.TT j), (if 2 * (l : ℕ) + 2 ≤ T then (zxS C0 CE1 CE2 X β j l : ℤ) else 0)

end

def PS (X : Loc) (j : Fin (numSeg X.TT)) (t : Fin (2 * segS X.TT j + 1 + 1)) : ℕ := X.p ^ (zS X j - posS X j t).toNat

section

variable (C0 CE1 CE2 mu : ℝ) (X : Loc) (β : GlobalTheory X) (j : Fin (numSeg X.TT))
  (ka : Fin (2 * segS X.TT j + 1 + 1) → Fin X.m → ℤ)

def colsS : Finset ℤ := colRange ka ∪ Finset.Icc 1 (nuS C0 CE1 CE2 mu X β j (2 * segS X.TT j + 1 + 1))

def plS (c : ℤ) : MonH X :=
  ∑ t : Fin (2 * segS X.TT j + 1 + 1),
    if nuS C0 CE1 CE2 mu X β j t.val < c ∧ c ≤ nuS C0 CE1 CE2 mu X β j (t.val + 1) then
      Finsupp.single (phiS X j (t, Fin.castAdd X.m 0)) (PS X j t) else 0

def dKS (c : ℤ) (i : Fin (2 * segS X.TT j + 1)) : ℕ := if colH (ka i.castSucc) c = colH (ka i.succ) c then 0 else 1

def oCS (c : ℤ) : ℕ := oc (PS X j) (muP (nuS C0 CE1 CE2 mu X β j) ka) c

def dgCS (c : ℤ) (l : X.TT × Bool) : ℕ :=
  ∑ t : Fin (2 * segS X.TT j + 1 + 1), if lamS X j t = l then
    dgS X.p (posS X j) (muP (nuS C0 CE1 CE2 mu X β j) ka) c (2 * segS X.TT j + 1 + 1) (zS X j) t else 0

def fCS [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra (WF X.p X.n') O] (I'' : ℤ → Finset (Fin X.m)) (c : ℤ) :
    RHH O X :=
  rename (phiS X j) (KKc X.p X.n' (O := O) (LLseg X j) 1 (zS X j) (muP (nuS C0 CE1 CE2 mu X β j) ka) c
    (Jc (nuS C0 CE1 CE2 mu X β j) (2 * segS X.TT j + 1) c (I'' c)))

end

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

def mdHom (X : Loc) (l : X.TT × Bool) : MonH X →+ ℕ where
  toFun := fun m => multideg m l
  map_zero' := by simp [multideg]
  map_add' := fun a b => multideg_add a b l

def ndHom (X : Loc) : MonH X →+ ℕ where
  toFun := ndM X
  map_zero' := Formalism.MainNotions.LemmaBAlt.degUS_zero _ _
  map_add' := ndM_add X

section Hom

variable {X : Loc} {O : Type} [CommRing O] [IsDomain O]

def HomW (φ : MonH X →+ ℕ) (d : ℕ) (P : RHH O X) : Prop := ∀ m ∈ P.support, φ m = d

theorem HomW.mul {φ : MonH X →+ ℕ} {d d' : ℕ} {P Q : RHH O X} (hP : HomW φ d P) (hQ : HomW φ d' Q) :
    HomW φ (d + d') (P * Q) := by
  classical
  intro m hm
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (support_mul P Q hm)
  rw [map_add (f := _), hP a ha, hQ b hb]

theorem HomW.one (φ : MonH X →+ ℕ) : HomW φ 0 (1 : RHH O X) := by
  classical
  intro m hm
  rw [mem_support_iff, coeff_one] at hm
  by_cases h : 0 = m
  · rw [← h, map_zero]
  · rw [if_neg h] at hm; exact absurd rfl hm

theorem HomW.pow {φ : MonH X →+ ℕ} {d : ℕ} {P : RHH O X} (hP : HomW φ d P) (u : ℕ) : HomW φ (u * d) (P ^ u) := by
  induction u with
  | zero => simpa using HomW.one (O := O) φ
  | succ u ih =>
    rw [pow_succ, Nat.succ_mul]
    exact ih.mul hP

theorem HomW.prod {φ : MonH X →+ ℕ} {κ : Type} (s : Finset κ) (d : κ → ℕ) (P : κ → RHH O X)
    (h : ∀ a ∈ s, HomW φ (d a) (P a)) : HomW φ (∑ a ∈ s, d a) (∏ a ∈ s, P a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HomW.one (O := O) φ
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

theorem HomW.monomial (φ : MonH X →+ ℕ) (M : MonH X) (c : KK O) : HomW φ (φ M) (monomial M c : RHH O X) := by
  classical
  intro m hm
  have := support_monomial_subset hm
  rw [Finset.mem_singleton] at this
  rw [this]

theorem mem_Pol_iffW {d : X.TT × Bool → ℕ} {P : RHH O X} :
    P ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) d ↔ ∀ l, HomW (mdHom X l) (d l) P := by
  unfold Pol
  rw [mem_restrictSupport_iff]
  constructor
  · intro h l m hm
    exact h (Finset.mem_coe.2 hm) l
  · intro h m hm l
    exact h l m (Finset.mem_coe.1 hm)

theorem mono_sum {ι : Type} (s : Finset ι) (n : ι → ℕ) (a : ι → MonH X) :
    (monomial (∑ i ∈ s, n i • a i) (1 : KK O) : RHH O X) = ∏ i ∈ s, (monomial (a i) (1 : KK O) : RHH O X) ^ n i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, ← ih, monomial_pow, one_pow, monomial_mul, one_mul]

theorem hom_total (φ : MonH X →+ ℕ) {κ : Type} [Fintype κ] (sg : κ → RHH O X) (d : κ → ℕ) (h : ∀ a, HomW φ (d a) (sg a))
    {sgR : RHH O X} {dR : ℕ} (hR : HomW φ dR sgR) (mult u : κ → ℕ) (M : MonH X) :
    HomW φ (dR + ∑ a, (mult a - u a) * d a + φ M) (sgR * (∏ a, sg a ^ (mult a - u a)) * monomial M 1) :=
  (hR.mul (HomW.prod _ _ _ fun a _ => (h a).pow _)).mul (HomW.monomial φ M 1)

end Hom


open Formalism.MainNotions.G.PolBridge Formalism.MainNotions.G.GLWeightTheory in
theorem ycond_factor (D : Formalism.BasicNotions.D7) {K : Type} [Field K] [CharZero K] {N r : ℕ} [NeZero r] (LL : ChainLetters N) (jj : ℕ)
    (M : WithTop ℤ) (Gu Gr : MvPolynomial (Fin N × Fin r) K) (dr : Fin N → ℕ) (hr : Gr ∈ Pol K r dr) (hne : Gr ≠ 0)
    (h : Gu * Gr ∈ YCond K (r := r) LL jj M) (cov : ℕ) (hcov : ∑ i, (if LL.vec i then 0 else dr i) ≤ cov) :
    Gu ∈ YCond K (r := r) LL jj (M + ((cov : ℤ) : WithTop ℤ)) := by
  classical
  cases M with
  | top => rw [WithTop.top_add, ycond_top]; exact Submodule.mem_top
  | coe Mz =>
    rw [← WithTop.coe_add, mem_ycond_iff D]
    rw [mem_ycond_iff D, (valuationsAdditive_D7 D K (Fin N) (⟨LL.vec⟩ : Letters (Fin N)) r {i : Fin N | (i : ℕ) < jj}).2.2.1] at h
    have hlow : ¬ lam1S (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < jj} Gr ≤ ((-(cov : ℤ) - 1 : ℤ) : WithBot ℤ) := by
      intro hle
      have h1 := ycond_le (K := K) (r := r) LL jj ((-(cov : ℤ) - 1 : ℤ) : WithTop ℤ) ((mem_ycond_iff D LL jj _ Gr).2 hle)
      rw [MvPolynomial.mem_restrictSupport_iff] at h1
      obtain ⟨m, hm⟩ : Gr.support.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]; intro h0; exact hne (MvPolynomial.support_eq_empty.1 h0)
      have h2 : ((chWt LL jj 0 m : ℤ) : WithTop ℤ) ≤ ((-(cov : ℤ) - 1 : ℤ) : WithTop ℤ) := h1 (Finset.mem_coe.2 hm)
      have h3 : chWt LL jj 0 m ≤ -(cov : ℤ) - 1 := by exact_mod_cast h2
      have hdeg : ∀ i, multideg m i = dr i := by
        unfold Pol at hr
        rw [MvPolynomial.mem_restrictSupport_iff] at hr
        exact hr (Finset.mem_coe.2 hm)
      have h4 : -((∑ i, (if LL.vec i then 0 else dr i) : ℕ) : ℤ) ≤ chWt LL jj 0 m := by
        unfold chWt
        rw [Nat.cast_sum, ← Finset.sum_neg_distrib]
        refine Finset.sum_le_sum fun i _ => ?_
        have hm0 : m (i, 0) ≤ dr i := by
          rw [← hdeg i]
          exact Finset.single_le_sum (f := fun c => m (i, c)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)
        have hm0' : (m (i, 0) : ℤ) ≤ (dr i : ℤ) := by exact_mod_cast hm0
        by_cases hv : LL.vec i = true
        · simp only [hv, if_true]
          split_ifs <;> simp
        · simp only [hv]
          split_ifs <;> simp <;> omega
      have h5 : ((∑ i, (if LL.vec i then 0 else dr i) : ℕ) : ℤ) ≤ (cov : ℤ) := by exact_mod_cast hcov
      omega
    induction hGr : lam1S (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < jj} Gr using WithBot.recBotCoe with
    | bot => rw [hGr] at hlow; exact absurd bot_le hlow
    | coe v =>
      rw [hGr] at hlow h
      have hv : -(cov : ℤ) - 1 < v := by
        by_contra hc
        exact hlow (by exact_mod_cast (not_lt.1 hc))
      induction hGu : lam1S (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < jj} Gu using WithBot.recBotCoe with
      | bot => exact bot_le
      | coe a =>
        rw [hGu] at h
        have h6 : a + v ≤ Mz := by exact_mod_cast h
        have : a ≤ Mz + (cov : ℤ) := by omega
        exact_mod_cast this

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

def ioA (K : Type) [CommRing K] (p : ℕ) (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) :
    MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) K →ₐ[K]
      MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) K :=
  aeval (fun v => (MvPolynomial.X (symVar C0 CE1 CE2 X j v) : MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) K) ^
      symLev p C0 CE1 CE2 X j v)

theorem ioBlock_eq (K : Type) [CommRing K] (p : ℕ) (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT))
    (b : SegBlock (segS X.TT j) X.m) (u : MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) K) :
    ioBlock K p C0 CE1 CE2 X j b u =
      digitMon K C0 CE1 CE2 X j b * sTopMon K p C0 CE1 CE2 X j b * ioA K p C0 CE1 CE2 X j u := rfl

abbrev BDk (C0 CE1 CE2 mu : ℝ) (X : Loc) (β : GlobalTheory X) (j : Fin (numSeg X.TT)) : BlockData (2 * segS X.TT j + 1) :=
  blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) mu (β j)

def ioD (O : Type) [CommRing O] [IsDomain O] (C0 CE1 CE2 mu : ℝ) (X : Loc) (β : GlobalTheory X) (j : Fin (numSeg X.TT)) :
    MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t) (KK O) →ₐ[KK O] RHH O X :=
  ioA (KK O) X.p C0 CE1 CE2 X j

structure LvDat (C0 CE1 CE2 mu : ℝ) (X : Loc) (β : GlobalTheory X) where
  lv : ∀ j, Fin (BDk C0 CE1 CE2 mu X β j).T.t → ℕ
  jp : Fin (numSeg X.TT) → ℕ
  ok : ∀ j, (BDk C0 CE1 CE2 mu X β j).LevelOK (lv j) (jp j)
  γ : Fin (numSeg X.TT) → Fin X.m → ℕ
  hγ : ∀ j, ∑ c, γ j c = (BDk C0 CE1 CE2 mu X β j).B - jp j

section

variable (O : Type) [CommRing O] [IsDomain O] {C0 CE1 CE2 mu : ℝ} {X : Loc} [NeZero X.m] {β : GlobalTheory X}

abbrev LvDat.LL (L : LvDat C0 CE1 CE2 mu X β) (j : Fin (numSeg X.TT)) : ChainLetters (2 * segS X.TT j + 1) :=
  (BDk C0 CE1 CE2 mu X β j).lettersAt (L.lv j) (L.jp j)

def LvDat.stdPoly (L : LvDat C0 CE1 CE2 mu X β) (j : Fin (numSeg X.TT)) : RHH O X :=
  digitMon (KK O) C0 CE1 CE2 X j (β j) * sTopMon (KK O) X.p C0 CE1 CE2 X j (β j) *
    ioD O C0 CE1 CE2 mu X β j
      ((∏ i, MvPolynomial.X (scalZ (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t (Fin.castSucc i)) ^
          (BDk C0 CE1 CE2 mu X β j).T.z i) *
        MvPolynomial.X (scalZ (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t
          (Fin.last (BDk C0 CE1 CE2 mu X β j).T.t)) ^ (BDk C0 CE1 CE2 mu X β j).zPlus *
        ∏ c, MvPolynomial.X (xiVar (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t c) ^ L.γ j c)

def LvDat.head (L : LvDat C0 CE1 CE2 mu X β) (j : Fin (numSeg X.TT))
    (ju : Fin (BDk C0 CE1 CE2 mu X β j).T.t → ℕ) (G : MvPolynomial (Fin (2 * segS X.TT j + 1) × Fin X.m) (KK O)) : RHH O X :=
  ioD O C0 CE1 CE2 mu X β j
    ((∏ i, (BDk C0 CE1 CE2 mu X β j).Ehat O (r := X.m) i ^ ju i) * (BDk C0 CE1 CE2 mu X β j).Eplus O (r := X.m) ^ L.jp j *
      rename (chainEmb (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t) G)

def LvDat.word (L : LvDat C0 CE1 CE2 mu X β) (j : Fin (numSeg X.TT))
    (G : MvPolynomial (Fin (2 * segS X.TT j + 1) × Fin X.m) (KK O)) :
    MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t) (KK O) :=
  (∏ i, (BDk C0 CE1 CE2 mu X β j).Ehat O (r := X.m) i ^ L.lv j i) * (BDk C0 CE1 CE2 mu X β j).Eplus O (r := X.m) ^ L.jp j *
      (∏ i, MvPolynomial.X (scalZ (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t (Fin.castSucc i)) ^
          (BDk C0 CE1 CE2 mu X β j).T.z i) *
      MvPolynomial.X (scalZ (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t
          (Fin.last (BDk C0 CE1 CE2 mu X β j).T.t)) ^ (BDk C0 CE1 CE2 mu X β j).zPlus *
      rename (chainEmb (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t) G *
      ∏ c, MvPolynomial.X (xiVar (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t c) ^ L.γ j c

theorem LvDat.ioBlock_word (L : LvDat C0 CE1 CE2 mu X β) (j : Fin (numSeg X.TT))
    (G : MvPolynomial (Fin (2 * segS X.TT j + 1) × Fin X.m) (KK O)) :
    ioBlock (KK O) X.p C0 CE1 CE2 X j (β j) (L.word O j G) = L.head O j (L.lv j) G * L.stdPoly O j := by
  change digitMon (KK O) C0 CE1 CE2 X j (β j) * sTopMon (KK O) X.p C0 CE1 CE2 X j (β j) *
    ioA (KK O) X.p C0 CE1 CE2 X j (L.word O j G) = _
  simp only [LvDat.word, LvDat.head, LvDat.stdPoly, ioD]
  conv_rhs => rw [mul_comm, mul_assoc]
  erw [← map_mul]
  refine congrArg (fun w => digitMon (KK O) C0 CE1 CE2 X j (β j) * sTopMon (KK O) X.p C0 CE1 CE2 X j (β j) *
    ioA (KK O) X.p C0 CE1 CE2 X j w) ?_
  have hcomm : ∀ (e ep z zp r xi : MvPolynomial (BVar (2 * segS X.TT j + 1) X.m
      (X.seg C0 CE1 CE2 j).t) (KK O)), e * ep * z * zp * r * xi = z * zp * xi * (e * ep * r) :=
    fun e ep z zp r xi => by ring
  exact hcomm _ _ _ _ _ _

end

def TCoreAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O), S.SqP → D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ mm : ℝ, (mm = 0 ∨ mm = 12 * (X.c : ℝ)) →
    ∀ n : ℕ, 1 ≤ n → n ≤ X.c →
    ∀ β : GlobalTheory X, (∀ j, BLk C0 Cde CE1 CE2 X (((X.c - n : ℕ) : ℝ) * ka1 X) j (β j)) →
    ∀ (L : LvDat C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β) (Std : MonH X),
      (monomial Std (1 : KK O) : RHH O X) = ∏ j, L.stdPoly O j →
    ∀ e : ℕ, 1 ≤ e → e < n →
    ∀ (ju : ∀ j, Fin (BDk C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j).T.t → ℕ), (∀ j i, ju j i ≤ L.lv j i) →
    ∀ (Gu : ∀ j, MvPolynomial (Fin (2 * segS X.TT j + 1) × Fin X.m) (KK O))
      (du : ∀ j, Fin (2 * segS X.TT j + 1) → ℕ),
      (∀ j, Gu j ∈ IntPol O (Fin (2 * segS X.TT j + 1) × Fin X.m)) →
      (∀ j, Gu j ∈ Pol (KK O) X.m (du j)) → (∀ j a, du j a ≤ (L.LL j).deg a) →
      (∀ j k, Gu j ∈ YCond (KK O) (r := X.m) (L.LL j) ((BDk C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j).T.J k)
        ((BDk C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j).T.thr k + (((X.N1 * e : ℕ) : ℤ) : WithTop ℤ))) →
    ∀ A : MonH X,
      (∀ l, ∑ c, (Std (l, c) - A (l, c)) ≤ X.p ^ X.G' * e) → (∀ l, ∑ c, (A (l, c) - Std (l, c)) ≤ X.p ^ X.G' * e) →
      (∀ j c, A ((topEnd X j, false), c) = Std ((topEnd X j, false), c)) →
      (∏ j, L.head O j (ju j) (Gu j)) * monomial A 1 ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (hhDegs X.TT X.aT X.bT) →
      (∀ m ∈ ((∏ j, L.head O j (ju j) (Gu j)) * monomial A 1).support, ndM X m ≤ ordFam C0 CE1 CE2 X β + e) →
      (∏ j, L.head O j (ju j) (Gu j)) * monomial A 1 ∈ SSe C0 Cde CE1 CE2 X O mm n (ordFam C0 CE1 CE2 X β) e

def RestTCore : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => TCoreAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

def colGens (O : Type) [CommRing O] [IsDomain O] {N r : ℕ} [NeZero r] (D : BlockData N) :
    Set (MvPolynomial (BVar N r D.T.t) (KK O)) :=
  {x | ∃ (j : Fin D.T.t → ℕ) (jp : ℕ), D.LevelOK j jp ∧
    ∃ y : Tx r (D.lettersAt j jp), y ∈ sAll (D.lettersAt j jp) D.T.J D.T.thr ∧
    ∃ γ : Fin r → ℕ, ∑ c, γ c = D.B - jp ∧
    x = (∏ i, D.Ehat O (r := r) i ^ j i) * D.Eplus O (r := r) ^ jp *
      (∏ i, X (scalZ N r D.T.t (Fin.castSucc i)) ^ D.T.z i) * X (scalZ N r D.T.t (Fin.last D.T.t)) ^ D.zPlus *
      rename (chainEmb N r D.T.t) (psiR (KK O) (D.lettersAt j jp) y) * ∏ c, X (xiVar N r D.T.t c) ^ γ c}

def FacSysAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O), S.SqP → D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ mm : ℝ, (mm = 0 ∨ mm = 12 * (X.c : ℝ)) →
    ∀ n : ℕ, 1 ≤ n → n ≤ X.c →
    ∀ β : GlobalTheory X, (∀ j, BLk C0 Cde CE1 CE2 X (((X.c - n : ℕ) : ℝ) * ka1 X) j (β j)) →
    ∀ s : Syms O C0 CE1 CE2 X,
      (∀ j, s j ∈ colGens O (r := X.m)
        (blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (mm + (n : ℝ) * ka1 X) (β j))) →
      Nonempty (FacSys C0 Cde CE1 CE2 X O S.w mm n (ordFam C0 CE1 CE2 X β) (symFam (KK O) X.p C0 CE1 CE2 X β s))

def FacSysCondition : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => FacSysAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc

end Formalism.MainNotions.ColumnSystems.Pf
end
end
