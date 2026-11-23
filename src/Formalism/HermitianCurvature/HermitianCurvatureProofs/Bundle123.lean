module

public import Formalism.HermitianCurvature.Bundle006
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BlockRelationTwistedHeight
public import Formalism.HermitianCurvature.FrameExists2
public import Formalism.PeriodIntegrals.UpqRep
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle111
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsFrameTwo
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle090
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LieBracketMultiplication
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SingleMulVecOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleRecOfAdmissibleWord
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle025
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.PTie

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBH

section reindex

variable {K A S S' : Type}


end reindex

def TowerAt : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq),
    ∃ T : D.LevTower k r Wp Wq, T.base.z = Bs.z ∧ T.base.z' = Bs.z' ∧ T.base.π = Bs.π ∧ T.base.π' = Bs.π' ∧
      D.TowerNormalised T

def PlAt : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Mx P.k P.r → (Wq →L[ℂ] Wq))
    (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (Bs : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → 2 ≤ P.k → Bs.z = z → Bs.z' = z' → Bs.π = π → Bs.π' = π' →
    ∃ p : KB.Pl P Wp Wq, p.l0 = l0 ∧ p.T.base.z = z ∧ p.T.base.z' = z' ∧ p.T.base.π = π ∧ p.T.base.π' = π'

def shiftCf {r : ℕ} (i : Fin (r + 1)) (c'' : Fin (r - i) → ℂ) : Cf r i :=
  fun l => c'' ⟨l.1.val - i.val, by have := l.1.isLt; have := l.2; omega⟩

def LevTrClauses {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    {z z' : Fin (2 * P.r + P.k + 1) → ℂ} {π : Mx P.k P.r → (Wp →L[ℂ] Wp)} {π' : Mx P.k P.r → (Wq →L[ℂ] Wq)}
    (μ : Measure (Mt P.k P.r)) (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r)
    (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ) (i : Fin (P.r + 1)) (c : Fin P.r → ℂ)
    (Di : B.RealPlaceData P.k (P.r - i) Wp Wq) (μi : Measure (Mt P.k (P.r - i)))
    (Li : R.LevelData (Pr (RadSp P.k (P.r - i) Di.z Di.z' Di.π Di.π')) (P.r - i))
    (sti : Fr.Start (Pr (RadSp P.k (P.r - i) Di.z Di.z' Di.π Di.π')))
    (T : RadSp P.k P.r z z' π π' →ₗ[ℂ] RadSp P.k (P.r - i) Di.z Di.z' Di.π Di.π') : Prop :=
  (∀ Φ c'' g, (T Φ : Fn P.k (P.r - i) (Wq →L[ℂ] Wp)) c'' g =
      (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) (glue i c (shiftCf i c'')) (D.castM (by omega) (ιLev P.k i (P.r - i) g))) ∧
    (∃ κ : ℝ, 0 < κ ∧ ∀ Φ Ψ c'', pairAt μi (T Φ) (T Ψ) c'' = (κ : ℂ) * pairAt μ Φ Ψ (glue i c (shiftCf i c''))) ∧
    (∀ (n : ℕ) (hn : n + i ≤ P.r) (Y : ℂ),
      MRel T (QQi L st ⟨n + i, by omega⟩ Y) (QQi Li sti ⟨n, by omega⟩ Y)) ∧
    ∀ (S : Type) [Fintype S] [DecidableEq S] (w : List (Wd.Letter ℂ S)),
      (∀ l : Fin (P.r - i), ARel T (bTl L ⟨l.val + i, by omega⟩ w) (bTl Li l w)) ∧
      (∀ (n : ℕ) (hn : n + i ≤ P.r), ARel T (RRi L st ⟨n + i, by omega⟩ w) (RRi Li sti ⟨n, by omega⟩ w)) ∧
      (WordOK P z z' π π' st l0 w → WordOK (JC.parLev P i) Di.z Di.z' Di.π Di.π' sti l0 w)

def LevTransportHer : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Mx P.k P.r → (Wq →L[ℂ] Wq))
    (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (Bs : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → Bs.z = z → Bs.z' = z' → Bs.π = π → Bs.π' = π' →
    ∀ (i : Fin (P.r + 1)) (c : Fin P.r → ℂ), (∀ l : Fin P.r, l.val < i.val → c l ≠ 0) →
    ∃ (Di : B.RealPlaceData P.k (P.r - i) Wp Wq)
      (Xi : ActualOps (JC.parLev P i).k (JC.parLev P i).r Di.z Di.z' Di.π Di.π') (μi : Measure (Mt P.k (P.r - i)))
      (Li : R.LevelData (Pr (RadSp P.k (P.r - i) Di.z Di.z' Di.π Di.π')) (P.r - i))
      (sti : Fr.Start (Pr (RadSp P.k (P.r - i) Di.z Di.z' Di.π Di.π')))
      (T : RadSp P.k P.r z z' π π' →ₗ[ℂ] RadSp P.k (P.r - i) Di.z Di.z' Di.π Di.π'),
      IsData (JC.parLev P i) Di.z Di.z' Di.π Di.π' Xi μi Li sti l0 ∧
        LevTrClauses P μ L st l0 i c Di μi Li sti T ∧
        ∀ (S : Type) [Fintype S] [DecidableEq S], ∀ Φ ∈ herKc S P z z' π π' L st l0 Bs i,
          T Φ ∈ herKc S (JC.parLev P i) Di.z Di.z' Di.π Di.π' Li sti l0 Di 0

def JFScale : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs Bs' : B.RealPlaceData k r Wp Wq), Bs.z = Bs'.z → Bs.z' = Bs'.z' → Bs.π = Bs'.π →
    Bs.π' = Bs'.π' → ∃ κ : ℂ, ∀ F, B.JF Bs F = κ • B.JF Bs' F

def SliceStepHer : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (T : D.LevTower P.k P.r Wp Wq), IsPlace P T.base.z T.base.z' T.base.π T.base.π' → D.TowerNormalised T →
    ∀ (j : ℕ) (hj : j + 1 ≤ P.r) (l0 : ℕ), 1 ≤ l0 → l0 ≤ P.k →
    ∀ (Xj : ActualOps (JC.parLev P j).k (JC.parLev P j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
      (μj : Measure (Mt P.k (P.r - j)))
      (Lj : R.LevelData (Pr (RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')) (P.r - j))
      (stj : Fr.Start (Pr (RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')))
      (Xs : ActualOps (JC.parLev P (j + 1)).k (JC.parLev P (j + 1)).r (T.bs (j + 1)).z (T.bs (j + 1)).z'
        (T.bs (j + 1)).π (T.bs (j + 1)).π')
      (μs : Measure (Mt P.k (P.r - (j + 1))))
      (Ls : R.LevelData (Pr (RadSp P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π
        (T.bs (j + 1)).π')) (P.r - (j + 1)))
      (sts : Fr.Start (Pr (RadSp P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π
        (T.bs (j + 1)).π'))),
    IsData (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' Xj μj Lj stj l0 →
    IsData (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π' Xs μs Ls
      sts l0 →
    ∀ (Tt : RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' →ₗ[ℂ]
        RadSp P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π') (t : ℂ),
      t ≠ 0 →
      (∀ Φ c g, (Tt Φ : Fn P.k (P.r - (j + 1)) (Wq →L[ℂ] Wp)) c g =
        (Φ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) (fun l => consC t c (Fin.cast (by omega) l))
          (D.castM (by omega) (ιLev P.k 1 (P.r - (j + 1)) g))) →
    ∀ (S : Type) [Fintype S] [DecidableEq S] (w : List (Wd.Letter ℂ S)) (a b : Wd.Ix S),
      WordOK (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' stj l0 w →
      ∀ Ψ ∈ herKc S (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' Lj stj l0 (T.bs j) 0,
        Tt ((bTl Lj (⟨0, by change 0 < P.r - j; omega⟩ : Fin (JC.parLev P j).r) w a b).1 Ψ) ∈
          herKc S (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π' Ls sts
            l0 (T.bs (j + 1)) 0

end Formalism.FourierDecayAlt.P.PTie
end
end

section

open Matrix Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P.QrD

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace QrCap

theorem exp_eig {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W] (A : W →L[ℂ] W) (μ : ℂ)
    (x : W) (hx : A x = μ • x) : NormedSpace.exp A x = Complex.exp μ • x := by
  have hpow : ∀ n : ℕ, (A ^ n) x = μ ^ n • x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ]
      show (A ^ n) (A x) = _
      rw [hx, map_smul, ih, smul_smul, pow_succ, mul_comm]
  rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum ℂ (𝔸 := W →L[ℂ] W), NormedSpace.exp_eq_tsum ℂ (𝔸 := ℂ)]
  simp only
  have h := (ContinuousLinearMap.apply ℂ W x).map_tsum (NormedSpace.expSeries_summable' (𝕂 := ℂ) A)
  simp only [ContinuousLinearMap.apply_apply] at h
  rw [h]
  simp only [_root_.smul_apply, hpow, smul_smul]
  rw [← (NormedSpace.expSeries_summable' (𝕂 := ℂ) μ).tsum_smul_const x]
  simp only [smul_eq_mul]

theorem exp_sum_eig {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W] {k : ℕ}
    (T : Fin k → (W →L[ℂ] W)) (θ μ : Fin k → ℝ) (x : W) (hx : ∀ c, T c x = (μ c : ℂ) • x) :
    NormedSpace.exp (∑ c, ((θ c : ℂ) * Complex.I) • T c) x = Complex.exp (((∑ c, μ c * θ c : ℝ) : ℂ) * Complex.I) • x := by
  rw [exp_eig _ (∑ c, ((θ c : ℂ) * Complex.I) * (μ c : ℂ)) x]
  · congr 2
    push_cast
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro c _
    ring
  · rw [_root_.sum_apply, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro c _
    rw [_root_.smul_apply, hx, smul_smul]

theorem lowK_allPos (k : ℕ) (u : Fin k → ℝ) (j : Fin k) :
    PI.UpqRep.lowK (PI.UpqRep.allPos k) u j = u j - ((k : ℝ) - 1) / 2 + (j : ℕ) := by
  have hj := j.isLt
  unfold PI.UpqRep.lowK PI.UpqRep.rhoN PI.UpqRep.rhoC PI.UpqRep.allPos
  simp only [Pi.add_apply, Pi.sub_apply, ne_eq, not_true_eq_false, and_false, and_true]
  rw [Finset.filter_lt_eq_Ioi, Finset.filter_gt_eq_Iio, Fin.card_Ioi, Fin.card_Iio]
  rw [Nat.sub_sub, Nat.cast_sub (by omega)]
  push_cast
  ring

theorem deriv_cexp {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] (L : ℝ) (v : W) :
    HasDerivAt (fun t : ℝ => Complex.exp (((-t * L : ℝ) : ℂ) * Complex.I) • v) ((-(L : ℂ) * Complex.I) • v) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => -t * L) (-L) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).neg).mul_const L
    simpa using this
  have h2 : HasDerivAt (fun t : ℝ => (((-t * L : ℝ) : ℂ) * Complex.I)) (((-L : ℝ) : ℂ) * Complex.I) 0 :=
    h1.ofReal_comp.mul_const Complex.I
  have h3 := (h2.cexp).smul_const v
  convert h3 using 1
  simp

section Rep

variable {k r : ℕ} {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (W →L[ℂ] W)}

theorem lie_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ) (X : ι → Mx k r) (hX : ∀ i, InLieW k r z (X i)) :
    InLieW k r z (∑ i ∈ s, ((c i : ℝ) : ℂ) • X i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (LieBracketMultiplication.lie_zero (k := k) (r := r) (z := z))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact LieBracketMultiplication.lie_add (LieBracketMultiplication.lie_smul (hX a) _) ih

theorem dOp_sum (hR : IsRepW k r z π) {ι : Type*} (s : Finset ι) (c : ι → ℝ) (X : ι → Mx k r)
    (hX : ∀ i, InLieW k r z (X i)) : dOp π (∑ i ∈ s, ((c i : ℝ) : ℂ) • X i) = ∑ i ∈ s, c i • dOp π (X i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using SkewHermitianParts.dOp_zero π
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      (differential_operator_linear W k r z π hR _ _ (LieBracketMultiplication.lie_smul (hX a) (c a)) (lie_sum s c X hX)).1,
      (differential_operator_linear W k r z π hR _ _ (hX a) (hX a)).2 (c a), ih]

theorem op_torus (hR : IsRepW k r z π) {Bs : Fin k → Fin (2 * r + k + 1) → ℂ} (hB : IsFrameOf k r [z] Bs)
    (θ : Fin k → ℝ) :
    π (NormedSpace.exp (∑ c, ((θ c : ℂ) * Complex.I) • unitB (Hpk k r) Bs c c)) =
      NormedSpace.exp (∑ c, ((θ c : ℂ) * Complex.I) • ecOp π (unitB (Hpk k r) Bs c c)) := by
  set A : Fin k → Mx k r := fun c => hpart2 (Hpk k r) (unitB (Hpk k r) Bs c c) with hAdef
  have hA : ∀ c, InLieW k r z (A c) := fun c => (QrD.frame_lie hB c c).2
  have hAe : ∀ c, A c = (-Complex.I) • unitB (Hpk k r) Bs c c := fun c => hpart2_self Bs c
  have hY : ∑ c, ((θ c : ℂ) * Complex.I) • unitB (Hpk k r) Bs c c =
      ((1 : ℝ) : ℂ) • ∑ c, ((-θ c : ℝ) : ℂ) • A c := by
    rw [Complex.ofReal_one, one_smul]
    apply Finset.sum_congr rfl
    intro c _
    rw [hAe c, smul_smul]
    congr 1
    push_cast
    ring
  have hec : ∀ c, ecOp π (unitB (Hpk k r) Bs c c) = Complex.I • dOp π (A c) := by
    intro c
    unfold ecOp
    rw [hpart1_self, SkewHermitianParts.dOp_zero, zero_add]
  rw [hY, representation_exp W k r z π hR _ (lie_sum _ _ _ hA) 1, one_smul, dOp_sum hR _ _ _ hA]
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  rw [hec c, ← Complex.coe_smul, smul_smul]
  congr 1
  push_cast
  linear_combination (-(θ c : ℂ)) * Complex.I_sq

end Rep

end QrCap

end Formalism.FourierDecayAlt.P
end
end

section

open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.WordCorrespondence

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.P.PBH

section core

variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] {T : V →ₗ[ℂ] V'}
  {S : Type} [Fintype S] [DecidableEq S]

theorem rel_inv {a b : Pr V} {a' b' : Pr V'} (h : Rel T a a') (hab : a * b = 1) (hba : b * a = 1)
    (hab' : a' * b' = 1) (hba' : b' * a' = 1) : Rel T b b' := by
  have e1 : a.1 * b.1 = 1 := congrArg Prod.fst hab
  have e2 : b'.1 * a'.1 = 1 := congrArg Prod.fst hba'
  have e3 : a.2.unop * b.2.unop = 1 := congrArg (fun x : Pr V => x.2.unop) hba
  have e4 : b'.2.unop * a'.2.unop = 1 := congrArg (fun x : Pr V' => x.2.unop) hab'
  refine ⟨LinearMap.ext fun v => ?_, LinearMap.ext fun v => ?_⟩
  · have i1 : a.1 (b.1 v) = v := by simpa using LinearMap.congr_fun e1 v
    have i2 : b'.1 (a'.1 (T (b.1 v))) = T (b.1 v) := by simpa using LinearMap.congr_fun e2 (T (b.1 v))
    have i3 : a'.1 (T (b.1 v)) = T (a.1 (b.1 v)) := LinearMap.congr_fun h.1 (b.1 v)
    show b'.1 (T v) = T (b.1 v)
    rw [← i2, i3, i1]
  · have i1 : a.2.unop (b.2.unop v) = v := by simpa using LinearMap.congr_fun e3 v
    have i2 : b'.2.unop (a'.2.unop (T (b.2.unop v))) = T (b.2.unop v) := by
      simpa using LinearMap.congr_fun e4 (T (b.2.unop v))
    have i3 : a'.2.unop (T (b.2.unop v)) = T (a.2.unop (b.2.unop v)) := LinearMap.congr_fun h.2 (b.2.unop v)
    show b'.2.unop (T v) = T (b.2.unop v)
    rw [← i2, i3, i1]

theorem arel_star' {M : SlopeTestRemainingChoices S (Pr V)} {M' : SlopeTestRemainingChoices S (Pr V')} (h : ARel T M M') : ARel T (star M) (star M') :=
  fun x y => by
    rw [Matrix.star_apply, Matrix.star_apply]
    exact rel_star (h y x)

theorem arel_pow' {M : SlopeTestRemainingChoices S (Pr V)} {M' : SlopeTestRemainingChoices S (Pr V')} (h : ARel T M M') : ∀ n : ℕ, ARel T (M ^ n) (M' ^ n)
  | 0 => by rw [pow_zero, pow_zero]; exact arel_one
  | n + 1 => by rw [pow_succ, pow_succ]; exact arel_mul (arel_pow' h n) h

theorem brel_of {a b c d : SlopeTestRemainingChoices S (Pr V)} {a' b' c' d' : SlopeTestRemainingChoices S (Pr V')} (h1 : ARel T a a') (h2 : ARel T b b')
    (h3 : ARel T c c') (h4 : ARel T d d') : BRel T !![a, b; c, d] !![a', b'; c', d'] := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact h1
  · exact h2
  · exact h3
  · exact h4

structure Gen {r₀ r₁ : ℕ} (T : V →ₗ[ℂ] V') (L₀ : LevelData (Pr V) r₀) (L : LevelData (Pr V') r₁) : Prop where
  ζ : Rel T L₀.ζ L.ζ
  ζi : Rel T L₀.ζi L.ζi
  ζb : Rel T L₀.ζb L.ζb
  ζbi : Rel T L₀.ζbi L.ζbi
  GG : Rel T L₀.GG L.GG
  GGi : Rel T L₀.GGi L.GGi
  TT : L₀.TT = L.TT

abbrev Corr (T : V →ₗ[ℂ] V') (inv0 : Set ℂ) (f₀ : FrameData S (Pr V)) (f : FrameData S (Pr V')) : Prop :=
  ARel T f₀.F f.F ∧ ARel T f₀.Fi f.Fi ∧ ARel T f₀.c f.c ∧ ARel T f₀.ci f.ci ∧ (∀ Y, ARel T (f₀.x Y) (f.x Y)) ∧
    (∀ Y ∈ inv0, ARel T (f₀.xi Y) (f.xi Y)) ∧ (∀ Y, BRel T (f₀.TT Y) (f.TT Y)) ∧ f₀.N = f.N ∧ f₀.q = f.q ∧
    f₀.inv = f.inv ∧ f₀.inv ⊆ inv0

variable {r₀ r₁ : ℕ} {L₀ : LevelData (Pr V) r₀} {L : LevelData (Pr V') r₁}

theorem l_eq {r : ℕ} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] (L : LevelData A r) (f : FrameData S A)
    (hf : IsFrame L f) (Y : ℂ) (hY : Y ∈ f.inv) (hY1 : Y + 1 ∈ f.inv) :
    f.l L Y = f.xi Y * io L.GGi * f.F * f.TT Y 1 0 * f.Fi := by
  have h := hf.frame_l Y hY hY1
  have hio : (io L.GGi : SlopeTestRemainingChoices S A) * io L.GG = 1 := by simp only [io, ← map_mul, L.GGi_GG, map_one]
  have hx := (hf.x_xi Y hY).2
  calc f.l L Y = (f.xi Y * f.x Y) * f.l L Y * (f.F * f.Fi) := by rw [hx, hf.F_Fi, one_mul, mul_one]
    _ = f.xi Y * ((io L.GGi * io L.GG) * f.x Y * f.l L Y * f.F) * f.Fi := by
      rw [hio]; simp only [one_mul, mul_assoc]
    _ = f.xi Y * io L.GGi * (io L.GG * f.x Y * f.l L Y * f.F) * f.Fi := by simp only [mul_assoc]
    _ = f.xi Y * io L.GGi * f.F * f.TT Y 1 0 * f.Fi := by rw [← h]; simp only [mul_assoc]

theorem l_rel (G : Gen T L₀ L) {inv0 : Set ℂ} {f₀ : FrameData S (Pr V)} {f : FrameData S (Pr V')}
    (hc : Corr T inv0 f₀ f) (hf₀ : IsFrame L₀ f₀) (hf : IsFrame L f) (Y : ℂ) (hY : Y ∈ f₀.inv)
    (hY1 : Y + 1 ∈ f₀.inv) : ARel T (f₀.l L₀ Y) (f.l L Y) := by
  obtain ⟨hF, hFi, -, -, -, hxi, hTT, -, -, hinv, hsub⟩ := hc
  rw [l_eq L₀ f₀ hf₀ Y hY hY1, l_eq L f hf Y (hinv ▸ hY) (hinv ▸ hY1)]
  exact arel_mul (arel_mul (arel_mul (arel_mul (hxi Y (hsub hY)) (arel_io G.GGi)) hF) (hTT Y 1 0)) hFi

theorem m_rel (G : Gen T L₀ L) {inv0 : Set ℂ} {f₀ : FrameData S (Pr V)} {f : FrameData S (Pr V')}
    (hc : Corr T inv0 f₀ f) (hf₀ : IsFrame L₀ f₀) (hf : IsFrame L f) (Y : ℂ) (hY : Y - 1 ∈ f₀.inv)
    (hY1 : Y ∈ f₀.inv) : ARel T (f₀.m L₀ Y) (f.m L Y) := by
  have hl := l_rel G hc hf₀ hf (Y - 1) hY (by rw [sub_add_cancel]; exact hY1)
  obtain ⟨-, -, hc', hci, -, -, -, hN, -, -, -⟩ := hc
  have hwt : ARel T (wt (S := S) L₀) (wt L) := arel_io (rel_mul (rel_mul G.ζ G.ζb) G.GGi)
  have hwti : ARel T (wti (S := S) L₀) (wti L) := arel_io (rel_mul (rel_mul G.GG G.ζi) G.ζbi)
  unfold FrameData.m FrameData.d FrameData.di
  rw [hN]
  exact arel_mul (arel_mul (arel_mul hci (arel_pow' hwti _)) (arel_star' hl)) (arel_mul (arel_pow' hwt _) hc')

theorem corr_plus (G : Gen T L₀ L) {inv0 : Set ℂ} {f₀ : FrameData S (Pr V)} {f : FrameData S (Pr V')}
    (hc : Corr T inv0 f₀ f) (hf₀ : IsFrame L₀ f₀) (hf : IsFrame L f) (a : S) (Ya : ℂ) (h1 : Ya ∈ f₀.inv)
    (h2 : Ya + 1 ∈ f₀.inv) : Corr T inv0 (f₀.plus L₀ a Ya) (f.plus L a Ya) := by
  have hl := l_rel G hc hf₀ hf Ya h1 h2
  obtain ⟨hF, hFi, hc', hci, hx, hxi, hTT, hN, hq, hinv, hsub⟩ := hc
  dsimp only [FrameData.plus]
  refine ⟨?_, ?_, ?_, ?_, fun Y => ?_, fun Y hY => ?_, fun Y => ?_, by rw [hN], by rw [hq], by rw [hinv],
    Set.inter_subset_left.trans hsub⟩
  · exact arel_mul (arel_ins a (brel_mul (brel_of (arel_io G.ζi) arel_zero arel_zero (arel_io G.ζbi))
      (brel_of arel_one arel_zero (arel_mul (arel_io G.GG) hl) (arel_io G.GG)))) hF
  · exact arel_mul hFi (arel_ins a (brel_mul (brel_of arel_one arel_zero (arel_neg hl) (arel_io G.GGi))
      (brel_of (arel_io G.ζ) arel_zero arel_zero (arel_io G.ζb))))
  · rw [hq]
    exact arel_mul hc' (arel_ins a (brel_of (arel_smul _ (hxi _ (hsub h2))) arel_zero arel_zero (hx Ya)))
  · rw [hq]
    exact arel_mul hci (arel_ins a (brel_of (arel_smul _ (hx _)) arel_zero arel_zero (hxi _ (hsub h1))))
  · exact arel_mul (hx Y) (arel_ins a (brel_of (arel_smul _ arel_one) arel_zero arel_zero arel_one))
  · exact arel_mul (hxi Y hY) (arel_ins a (brel_of (arel_smul _ arel_one) arel_zero arel_zero arel_one))
  · exact brel_mul (hTT Y) (block_relation_height a _)

theorem corr_minus (G : Gen T L₀ L) {inv0 : Set ℂ} {f₀ : FrameData S (Pr V)} {f : FrameData S (Pr V')}
    (hc : Corr T inv0 f₀ f) (hf₀ : IsFrame L₀ f₀) (hf : IsFrame L f) (b : S) (Yb : ℂ) (h1 : Yb ∈ f₀.inv)
    (h0 : Yb - 1 ∈ f₀.inv) : Corr T inv0 (f₀.minus L₀ b Yb) (f.minus L b Yb) := by
  have hm := m_rel G hc hf₀ hf Yb h0 h1
  obtain ⟨hF, hFi, hc', hci, hx, hxi, hTT, hN, hq, hinv, hsub⟩ := hc
  dsimp only [FrameData.minus]
  refine ⟨?_, ?_, ?_, ?_, fun Y => ?_, fun Y hY => ?_, fun Y => ?_, by rw [hN], by rw [hq], by rw [hinv],
    Set.inter_subset_left.trans hsub⟩
  · exact arel_mul (arel_ins b (brel_mul (brel_of (arel_io G.ζbi) arel_zero arel_zero (arel_io G.ζi))
      (brel_of arel_one arel_zero (arel_mul (arel_io G.GG) hm) (arel_io G.GG)))) hF
  · exact arel_mul hFi (arel_ins b (brel_mul (brel_of arel_one arel_zero (arel_neg hm) (arel_io G.GGi))
      (brel_of (arel_io G.ζb) arel_zero arel_zero (arel_io G.ζ))))
  · rw [hq]
    exact arel_mul hc' (arel_ins b (brel_of (arel_smul _ (hxi _ (hsub h0))) arel_zero arel_zero (hx Yb)))
  · rw [hq]
    exact arel_mul hci (arel_ins b (brel_of (arel_smul _ (hx _)) arel_zero arel_zero (hxi _ (hsub h1))))
  · exact arel_mul (hx Y) (arel_ins b (brel_of (arel_smul _ arel_one) arel_zero arel_zero arel_one))
  · exact arel_mul (hxi Y hY) (arel_ins b (brel_of (arel_smul _ arel_one) arel_zero arel_zero arel_one))
  · exact brel_mul (block_relation_twisted_height b _) (hTT Y)

variable {st₀ : Start (Pr V)} {st : Start (Pr V')}

theorem x_rel (G : Gen T L₀ L) (hQ : ∀ Y, MRel T (st₀.QQ Y) (st.QQ Y)) (hs₀ : IsLevelStart L₀ st₀)
    (hs : IsLevelStart L st) (Y : ℂ) : Rel T (st₀.x Y) (st.x Y) := by
  have e₀ : st₀.x Y = L₀.GGi * st₀.QQ Y 1 1 := by rw [hs₀.tau, ← mul_assoc, L₀.GGi_GG, one_mul]
  have e : st.x Y = L.GGi * st.QQ Y 1 1 := by rw [hs.tau, ← mul_assoc, L.GGi_GG, one_mul]
  rw [e₀, e]
  exact rel_mul G.GGi (hQ Y 1 1)

theorem corr_word (G : Gen T L₀ L) (hQ : ∀ Y, MRel T (st₀.QQ Y) (st.QQ Y)) (hq : st₀.q = st.q)
    (hinv : st₀.inv = st.inv) (hL₀ : IsStarLevel L₀) (hL : IsStarLevel L) (hs₀ : IsLevelStart L₀ st₀)
    (hs : IsLevelStart L st) :
    ∀ w : List (Letter ℂ S), AdmRec L₀ st₀ w → AdmRec L st w →
      Corr T st₀.inv (ofWord L₀ st₀ w) (ofWord L st w) := by
  intro w
  induction w with
  | nil =>
    intro _ _
    refine ⟨arel_one, arel_one, arel_one, arel_one, fun Y => arel_io (x_rel G hQ hs₀ hs Y), fun Y hY => ?_,
      fun Y => brel_lift0 (hQ Y), rfl, hq, hinv, subset_rfl⟩
    exact arel_io (rel_inv (x_rel G hQ hs₀ hs Y) (hs₀.x_xi Y hY).1 (hs₀.x_xi Y hY).2
      (hs.x_xi Y (hinv ▸ hY)).1 (hs.x_xi Y (hinv ▸ hY)).2)
  | cons l w ih =>
    intro h₀ h
    unfold AdmRec at h₀ h
    obtain ⟨hw₀, -, -, hp0, hp1, hrest⟩ := h₀
    obtain ⟨hw, -⟩ := h
    have hf₀ := Formalism.FourierDecayAlt.P.frame_of_recursive_word (Pr V) S r₀ L₀ st₀ w hL₀ hs₀ hw₀
    have hf := Formalism.FourierDecayAlt.P.frame_of_recursive_word (Pr V') S r₁ L st w hL hs hw
    by_cases hp : l.plus
    · simpa only [ofWord, ite_eq_left hp] using
        corr_plus G (ih hw₀ hw) hf₀ hf l.intersection_update_fsHerm_neg_one l.pt hp0 hp1
    · rw [ite_eq_right hp] at hrest
      simpa only [ofWord, ite_eq_right hp] using
        corr_minus G (ih hw₀ hw) hf₀ hf l.intersection_update_fsHerm_neg_one l.pt hp0 hrest.1

theorem act_frame (G : Gen T L₀ L) (hQ : ∀ Y, MRel T (st₀.QQ Y) (st.QQ Y)) (hq : st₀.q = st.q)
    (hinv : st₀.inv = st.inv) (hL₀ : IsStarLevel L₀) (hL : IsStarLevel L) (hs₀ : IsLevelStart L₀ st₀)
    (hs : IsLevelStart L st) (w : List (Letter ℂ S)) (h₀ : admitted st₀ w) (h : admitted st w) (Ψ : Ix S → V) (e : Ix S) :
    T (∑ b, ((ofWord L₀ st₀ w).F e b).1 (Ψ b)) = ∑ b, ((ofWord L st w).F e b).1 (T (Ψ b)) :=
  act_tr (corr_word G hQ hq hinv hL₀ hL hs₀ hs w
    (Formalism.FourierDecayAlt.P.admissible_rec_of_admissible (Pr V) S r₀ L₀ st₀ w h₀)
    (Formalism.FourierDecayAlt.P.admissible_rec_of_admissible (Pr V') S r₁ L st w h)).1 Ψ e

end core

end Formalism.FourierDecayAlt.P.WordCorrespondence
end
end
