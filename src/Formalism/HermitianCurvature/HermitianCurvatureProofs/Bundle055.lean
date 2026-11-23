module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle046
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle047
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.FDeriv.Star
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JfS.Sym

noncomputable section

variable {k r : ℕ}

def Flt (a : ℕ) (x : Fin (2 * r + k + 1) → ℂ) : Prop := ∀ i : Fin (2 * r + k + 1), a ≤ i.val → x i = 0

def hermL (y : Fin (2 * r + k + 1) → ℂ) : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] ℂ where
  toFun x := herm (Hpk k r) x y
  map_add' x x' := herm_add_left x x' y
  map_smul' c x := by simp [herm_smul_left]

theorem herm_sum_left {ι : Type*} (s : Finset ι) (f : ι → Fin (2 * r + k + 1) → ℂ) (y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (∑ j ∈ s, f j) y = ∑ j ∈ s, herm (Hpk k r) (f j) y :=
  map_sum (hermL y) f s

theorem herm_sum_right {ι : Type*} (s : Finset ι) (f : ι → Fin (2 * r + k + 1) → ℂ) (x : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) x (∑ j ∈ s, f j) = ∑ j ∈ s, herm (Hpk k r) x (f j) := by
  rw [herm_swap, herm_sum_left, star_sum]
  exact Finset.sum_congr rfl (fun j _ => by rw [← herm_swap])

theorem mulVec_sum' {ι : Type*} (s : Finset ι) (g : B.Mat k r) (f : ι → Fin (2 * r + k + 1) → ℂ) :
    g *ᵥ (∑ j ∈ s, f j) = ∑ j ∈ s, g *ᵥ f j :=
  map_sum (Matrix.mulVecLin g) f s

theorem flt_decomp (a : ℕ) (ha : a ≤ r) (y : Fin (2 * r + k + 1) → ℂ) (hy : Flt a y) :
    y = ∑ j : Fin a, y (eI k r ⟨j.val, by omega⟩) • bvec (eI k r ⟨j.val, by omega⟩) := by
  funext i
  rw [Finset.sum_apply]
  by_cases hi : i.val < a
  · rw [Finset.sum_eq_single ⟨i.val, hi⟩]
    · have : eI k r ⟨i.val, by omega⟩ = i := Fin.ext rfl
      simp [this, bvec]
    · intro j _ hj
      have : eI k r ⟨j.val, by omega⟩ ≠ i := by
        intro e; apply hj; apply Fin.ext; have := congrArg Fin.val e; simpa [eI] using this
      simp [bvec, Ne.symm this]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [hy i (by omega)]
    symm
    refine Finset.sum_eq_zero (fun j _ => ?_)
    have : eI k r ⟨j.val, by omega⟩ ≠ i := by
      intro e; have := congrArg Fin.val e; simp [eI] at this; omega
    simp [bvec, Ne.symm this]

def Mblk (g : B.Mat k r) (a : ℕ) (ha : a ≤ r) : Matrix (Fin a) (Fin a) ℂ := fun i j =>
  herm (Hpk k r) (g *ᵥ bvec (eI k r ⟨j.val, by omega⟩)) (bvec (eI k r ⟨i.val, by omega⟩))

theorem dmin_eq (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) (a : ℕ) (ha : a ≤ r) :
    Dmin k r z z' g ⟨a, by omega⟩ = (Mblk g a ha).det := by
  unfold Dmin
  congr 1
  ext i j
  simp only [Matrix.submatrix_apply, Zhat, fvec, Fin.val_castLE, Mblk]
  have hi : (i : ℕ) < a := i.isLt
  have hj : (j : ℕ) < a := j.isLt
  rw [dite_eq_left (show i.val < r by omega), dite_eq_left (show j.val < r by omega)]

theorem dlem_i (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) (a : ℕ) (ha : a ≤ r)
    (hD : Dmin k r z z' g ⟨a, by omega⟩ ≠ 0) (y : Fin (2 * r + k + 1) → ℂ) (hy : Flt a y)
    (h : ∀ c : Fin r, c.val < a → herm (Hpk k r) (g *ᵥ y) (bvec (eI k r c)) = 0) : y = 0 := by
  rw [dmin_eq z z' g a ha] at hD
  set y' : Fin a → ℂ := fun j => y (eI k r ⟨j.val, by omega⟩)
  have hMy : Mblk g a ha *ᵥ y' = 0 := by
    funext c
    have hc := h ⟨c.val, by omega⟩ c.isLt
    rw [flt_decomp a ha y hy, mulVec_sum', herm_sum_left] at hc
    simp only [mulVec_smul, herm_smul_left] at hc
    rw [Pi.zero_apply, ← hc]
    simp only [mulVec, dotProduct, Mblk, y']
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hy' : y' = 0 := Matrix.eq_zero_of_mulVec_eq_zero hD hMy
  rw [flt_decomp a ha y hy]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  have : y (eI k r ⟨j.val, by omega⟩) = 0 := congrFun hy' j
  rw [this, zero_smul]

theorem dlem_ii (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) (a : ℕ) (ha : a ≤ r)
    (hD : Dmin k r z z' g ⟨a, by omega⟩ ≠ 0) (y : Fin (2 * r + k + 1) → ℂ) (hy : Flt a y)
    (h : ∀ c : Fin r, c.val < a → herm (Hpk k r) y (g *ᵥ bvec (eI k r c)) = 0) : y = 0 := by
  rw [dmin_eq z z' g a ha] at hD
  set y' : Fin a → ℂ := fun j => y (eI k r ⟨j.val, by omega⟩)
  have hMy : star y' ᵥ* Mblk g a ha = 0 := by
    funext c
    have hc := h ⟨c.val, by omega⟩ c.isLt
    rw [herm_swap, star_eq_zero, flt_decomp a ha y hy, herm_sum_right] at hc
    simp only [herm_smul_right] at hc
    rw [Pi.zero_apply, ← hc]
    simp only [vecMul, dotProduct, Mblk, y', Pi.star_apply]
  have hy' : star y' = 0 := Matrix.eq_zero_of_vecMul_eq_zero hD hMy
  rw [flt_decomp a ha y hy]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  have : y (eI k r ⟨j.val, by omega⟩) = 0 := by
    have := congrFun hy' j
    simpa [y'] using this
  rw [this, zero_smul]

end

end Formalism.FourierDecayAlt.P.CutMP.JfS.Sym
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

section preds

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def SSLoc (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')))
    (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (s t : ℕ → M.Ty P → M.Ty P → ℂ → ℂ) : Prop :=
  ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (ρ' : M.Ty P),
    trR P Bs e ((d.SS l).1 Φ) ρ' = ∑ ρ, fnZ P (s l ρ' ρ) * trR P Bs e Φ ρ ∧
    trR P Bs e ((star (d.SS l)).1 Φ) ρ' = ∑ ρ, fnZ P (t l ρ' ρ) * trR P Bs e Φ ρ

def SmST (P : M.Par) (s t : ℕ → M.Ty P → M.Ty P → ℂ → ℂ) : Prop :=
  ∀ l ρ' ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (s l ρ' ρ) (Ann P) ∧
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (t l ρ' ρ) (Ann P)

end preds

def GTSSLocal : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e →
      ∃ s t : ℕ → M.Ty P → M.Ty P → ℂ → ℂ, SmST P s t ∧ SSLoc P Bs d e s t

def GTRadAdj : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ (Y : ℂ) (a b : Fin 2) (c : Fin P.r → ℂ), c ∈ OmX P.r →
    ∀ Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
      (∃ K : Set ℂ, IsCompact K ∧ K ⊆ Ann P ∧ ∀ ζ ∈ Ann P, ζ ∉ K →
        (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ) = 0 ∧
          (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ) = 0) →
      ∫ ζ in Ann P, (((wR P.k P.TT ζ) ^ 2 : ℝ) : ℂ) *
          inner ℂ (B.hsVec ((X.t Y a b Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ)))
            (B.hsVec ((Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ))) =
        ∫ ζ in Ann P, (((wR P.k P.TT ζ) ^ 2 : ℝ) : ℂ) *
          inner ℂ (B.hsVec ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ)))
            (B.hsVec ((X.t (star Y) b a Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ)))

def GTSSAdjPt : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e →
      ∀ s t : ℕ → M.Ty P → M.Ty P → ℂ → ℂ, SmST P s t → SSLoc P Bs d e s t →
        ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ ρ ρ' : M.Ty P, ∀ ζ ∈ Ann P, t l ρ ρ' ζ = star (s l ρ' ρ ζ)

def GTSSConst : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e → NabF P Bs d e →
      ∀ s t : ℕ → M.Ty P → M.Ty P → ℂ → ℂ, SmST P s t → SSLoc P Bs d e s t →
        ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ ρ' ρ : M.Ty P, ∃ C D : ℂ, ∀ ζ ∈ Ann P, s l ρ' ρ ζ = C ∧ t l ρ' ρ ζ = D

def GTSSPhase : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e → NabF P Bs d e →
      ∀ s t : ℕ → M.Ty P → M.Ty P → ℂ, SSLoc P Bs d e (fun l ρ' ρ _ => s l ρ' ρ) (fun l ρ' ρ _ => t l ρ' ρ) →
        (∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ ρ ρ' : M.Ty P, t l ρ ρ' = star (s l ρ' ρ)) →
        ∃ e' : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e' ∧ KapF P Bs d e' ∧ NabF P Bs d e' ∧ SSF P Bs d e'

theorem fnZ_congr (P : M.Par) {f g : ℂ → ℂ} (h : ∀ ζ ∈ Ann P, f ζ = g ζ) : fnZ P f = fnZ P g := by
  unfold fnZ
  congr 1
  funext q
  exact h _ q.2.2

theorem ann_pt (P : M.Par) (hTT : 0 < P.TT) : ((Real.sqrt P.TT + 1 : ℝ) : ℂ) ∈ Ann P := by
  show P.TT < Complex.normSq (((Real.sqrt P.TT + 1 : ℝ)) : ℂ)
  rw [Complex.normSq_ofReal]
  have h1 := Real.sq_sqrt hTT.le
  have h2 := Real.sqrt_nonneg P.TT
  nlinarith

def GTSSOfCut : Prop := GTSSLocal → GTSSAdjPt → GTSSConst → GTSSPhase → GTSS

theorem gTSS_of_cut : GTSSOfCut := by
  intro hL hA hC hP
  intro Wp Wq _ _ _ _ _ _ P Bs X d hH e he hk hn
  obtain ⟨s, t, hst, hSL⟩ := hL Wp Wq P Bs X d hH e he hk
  have hc := hC Wp Wq P Bs X d hH e he hk hn s t hst hSL
  choose! C D hCD using hc
  have hζ0 : (((|P.TT| + 1 : ℝ)) : ℂ) ∈ Ann P := by
    show P.TT < Complex.normSq (((|P.TT| + 1 : ℝ)) : ℂ)
    rw [Complex.normSq_ofReal]
    nlinarith [abs_nonneg P.TT, le_abs_self P.TT]
  apply hP Wp Wq P Bs X d hH e he hk hn C D
  · intro l hl Φ ρ'
    obtain ⟨h1, h2⟩ := hSL l hl Φ ρ'
    refine ⟨h1.trans ?_, h2.trans ?_⟩
    · refine Finset.sum_congr rfl fun ρ _ => ?_
      rw [fnZ_congr P (f := s l ρ' ρ) (g := fun _ => C l ρ' ρ) (fun ζ hζ => (hCD l hl ρ' ρ ζ hζ).1)]
    · refine Finset.sum_congr rfl fun ρ _ => ?_
      rw [fnZ_congr P (f := t l ρ' ρ) (g := fun _ => D l ρ' ρ) (fun ζ hζ => (hCD l hl ρ' ρ ζ hζ).2)]
  · intro l hl ρ ρ'
    have h := hA Wp Wq P Bs X d hH e he hk s t hst hSL l hl ρ ρ' _ hζ0
    rw [(hCD l hl ρ ρ' _ hζ0).2, (hCD l hl ρ' ρ _ hζ0).1] at h
    exact h

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

def GTCRef : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∃ e0 : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e0 ∧ KapF P Bs d e0 ∧
      ∃ A0 B0 : M.Ty P → ℂ → ℂ, SmAB P A0 B0 ∧ ConnF P Bs d e0 A0 B0 ∧
        (∀ ρ, ∀ ζ ∈ Ann P, (NF.dZb (fun w => modA P ρ w - A0 ρ w) ζ).re = 0) ∧
        ∀ ρ (R : ℝ), 0 < R → P.TT < R ^ 2 →
          ∃ n : ℤ, (circleIntegral (fun w => modA P ρ w - A0 ρ w) 0 R).im = Real.pi * n

def GTCPhaseRel : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e e0 : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e →
      IsFrameB P Bs e0 → KapF P Bs d e0 →
      ∃ u : M.Ty P → ℂ → ℂ, (∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (u ρ) (Ann P) ∧ ∀ ζ ∈ Ann P, ‖u ρ ζ‖ = 1) ∧
        ∀ ρ, ∀ ζ ∈ Ann P, e ρ ζ = u ρ ζ • e0 ρ ζ

def GTCConnUniq : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e →
      ∀ A B A' B' : M.Ty P → ℂ → ℂ, SmAB P A B → SmAB P A' B' → ConnF P Bs d e A B → ConnF P Bs d e A' B' →
        ∀ ρ, ∀ ζ ∈ Ann P, A ρ ζ = A' ρ ζ

def GTCConnPhase : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (A B u : M.Ty P → ℂ → ℂ), SmAB P A B →
      (∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (u ρ) (Ann P) ∧ ∀ ζ ∈ Ann P, ‖u ρ ζ‖ = 1) →
      ConnF P Bs d e A B →
      SmAB P (fun ρ ζ => A ρ ζ + star (u ρ ζ) * NF.dZ (u ρ) ζ) (fun ρ ζ => B ρ ζ - star (u ρ ζ) * NF.dZb (u ρ) ζ) ∧
      ConnF P Bs d (fun ρ ζ => u ρ ζ • e ρ ζ) (fun ρ ζ => A ρ ζ + star (u ρ ζ) * NF.dZ (u ρ) ζ)
        (fun ρ ζ => B ρ ζ - star (u ρ ζ) * NF.dZb (u ρ) ζ)

def GTCPhHol : Prop :=
  ∀ (TT : ℝ) (u : ℂ → ℂ), ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u {ζ : ℂ | TT < Complex.normSq ζ} →
    (∀ ζ : ℂ, TT < Complex.normSq ζ → ‖u ζ‖ = 1) →
    ∀ R : ℝ, 0 < R → TT < R ^ 2 → ∃ n : ℤ, (circleIntegral (fun w => star (u w) * NF.dZ u w) 0 R).im = Real.pi * n

def GTCPhCurv : Prop :=
  ∀ (TT : ℝ) (u : ℂ → ℂ), ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u {ζ : ℂ | TT < Complex.normSq ζ} →
    (∀ ζ : ℂ, TT < Complex.normSq ζ → ‖u ζ‖ = 1) →
    ∀ ζ : ℂ, TT < Complex.normSq ζ → (NF.dZb (fun w => star (u w) * NF.dZ u w) ζ).re = 0

theorem ann_isOpen (P : M.Par) : IsOpen (Ann P) := isOpen_lt continuous_const Complex.continuous_normSq

theorem sphere_sub_ann (P : M.Par) {R : ℝ} (hR0 : 0 < R) (hR : P.TT < R ^ 2) :
    Metric.sphere (0 : ℂ) R ⊆ Ann P := by
  intro w hw
  have h : ‖w‖ = R := by simpa using hw
  show P.TT < Complex.normSq w
  rw [Complex.normSq_eq_norm_sq, h]
  exact hR

theorem trR_congr {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (e e' : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (h : ∀ ρ, ∀ ζ ∈ Ann P, e ρ ζ = e' ρ ζ) :
    trR P Bs e = trR P Bs e' := by
  funext Φ ρ
  unfold trR rawR
  congr 1
  funext q
  rw [h ρ q.1.2 q.2.2]

theorem tt_nonneg_of_hyp {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}
    {X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π'} {d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))}
    (h : GTHyp P Bs X d) : 0 ≤ P.TT := by
  have hOK := h.1.1
  show (0 : ℝ) ≤ P.T * P.T'
  exact (mul_pos hOK.T_pos hOK.T'_pos).le

theorem gauge_rel (hRef : GTCRef) (hPR : GTCPhaseRel) (hU : GTCConnUniq) (hCP : GTCConnPhase)
    (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')))
    (hyp : GTHyp P Bs X d) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (he : IsFrameB P Bs e) (hk : KapF P Bs d e)
    (A B : M.Ty P → ℂ → ℂ) (hAB : SmAB P A B) (hConn : ConnF P Bs d e A B) :
    ∃ (A0 : M.Ty P → ℂ → ℂ) (u : M.Ty P → ℂ → ℂ),
      (∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (A0 ρ) (Ann P)) ∧
      (∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (u ρ) (Ann P) ∧ ∀ ζ ∈ Ann P, ‖u ρ ζ‖ = 1) ∧
      (∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ζ => star (u ρ ζ) * NF.dZ (u ρ) ζ) (Ann P)) ∧
      (∀ ρ, ∀ ζ ∈ Ann P, (NF.dZb (fun w => modA P ρ w - A0 ρ w) ζ).re = 0) ∧
      (∀ ρ (R : ℝ), 0 < R → P.TT < R ^ 2 →
          ∃ n : ℤ, (circleIntegral (fun w => modA P ρ w - A0 ρ w) 0 R).im = Real.pi * n) ∧
      ∀ ρ, ∀ ζ ∈ Ann P, A ρ ζ = A0 ρ ζ + star (u ρ ζ) * NF.dZ (u ρ) ζ := by
  obtain ⟨e0, he0, hk0, A0, B0, hAB0, hConn0, hcurv, hhol⟩ := hRef Wp Wq P Bs X d hyp
  obtain ⟨u, hu, heu⟩ := hPR Wp Wq P Bs X d hyp e e0 he hk he0 hk0
  obtain ⟨hAB1, hConn1⟩ := hCP Wp Wq P Bs X d hyp e0 A0 B0 u hAB0 hu hConn0
  have htr : trR P Bs (fun ρ ζ => u ρ ζ • e0 ρ ζ) = trR P Bs e :=
    trR_congr P Bs _ _ (fun ρ ζ hζ => (heu ρ ζ hζ).symm)
  have hConn1' : ConnF P Bs d e (fun ρ ζ => A0 ρ ζ + star (u ρ ζ) * NF.dZ (u ρ) ζ)
      (fun ρ ζ => B0 ρ ζ - star (u ρ ζ) * NF.dZb (u ρ) ζ) := by
    unfold ConnF at hConn1 ⊢
    rw [← htr]
    exact hConn1
  have hA := hU Wp Wq P Bs X d hyp e he A B _ _ hAB hAB1 hConn hConn1'
  refine ⟨A0, u, fun ρ => (hAB0 ρ).1, hu, fun ρ => ?_, hcurv, hhol, hA⟩
  exact ((hAB1 ρ).1.sub (hAB0 ρ).1).congr (fun ζ _ => by ring)

def GTCHolOfCut : Prop := GTCRef → GTCPhaseRel → GTCConnUniq → GTCConnPhase → GTCPhHol → GTCHol

theorem gTCHol_of_cut : GTCHolOfCut := by
  intro hRef hPR hU hCP hPh Wp Wq _ _ _ _ _ _ P Bs X d hyp e he hk A B hAB hConn ρ R hR0 hR
  obtain ⟨A0, u, hA0s, hu, hws, -, hhol, hA⟩ :=
    gauge_rel hRef hPR hU hCP Wp Wq P Bs X d hyp e he hk A B hAB hConn
  have hTT := tt_nonneg_of_hyp hyp
  obtain ⟨n1, hn1⟩ := hhol ρ R hR0 hR
  obtain ⟨n2, hn2⟩ := hPh P.TT (u ρ) (hu ρ).1 (hu ρ).2 R hR0 hR
  have hsph := sphere_sub_ann P hR0 hR
  have hf : CircleIntegrable (fun w => modA P ρ w - A0 ρ w) 0 R :=
    ContinuousOn.circleIntegrable hR0.le (((modA_smooth P ρ hTT).sub (hA0s ρ)).continuousOn.mono hsph)
  have hg : CircleIntegrable (fun w => star (u ρ w) * NF.dZ (u ρ) w) 0 R :=
    ContinuousOn.circleIntegrable hR0.le ((hws ρ).continuousOn.mono hsph)
  have heq : (∮ w in C(0, R), modA P ρ w - A ρ w) =
      ∮ w in C(0, R), (modA P ρ w - A0 ρ w) - star (u ρ w) * NF.dZ (u ρ) w := by
    apply circleIntegral.integral_congr hR0.le
    intro w hw
    try dsimp only
    rw [hA ρ w (hsph hw)]
    ring
  refine ⟨n1 - n2, ?_⟩
  rw [heq, circleIntegral.integral_sub hf hg, Complex.sub_im, hn1, hn2]
  push_cast
  ring

def GTCCurvOfCut : Prop := GTCRef → GTCPhaseRel → GTCConnUniq → GTCConnPhase → GTCPhCurv → GTCCurv

theorem gTCCurv_of_cut : GTCCurvOfCut := by
  intro hRef hPR hU hCP hPc Wp Wq _ _ _ _ _ _ P Bs X d hyp e he hk A B hAB hConn ρ ζ hζ
  obtain ⟨A0, u, hA0s, hu, hws, hcurv, -, hA⟩ :=
    gauge_rel hRef hPR hU hCP Wp Wq P Bs X d hyp e he hk A B hAB hConn
  have hTT := tt_nonneg_of_hyp hyp
  have hnhds : Ann P ∈ nhds ζ := (ann_isOpen P).mem_nhds hζ
  have hev : (fun w => modA P ρ w - A ρ w) =ᶠ[nhds ζ]
      fun w => (modA P ρ w - A0 ρ w) - star (u ρ w) * NF.dZ (u ρ) w := by
    filter_upwards [hnhds] with w hw
    rw [hA ρ w hw]
    ring
  have hfd : DifferentiableAt ℝ (fun w => modA P ρ w - A0 ρ w) ζ :=
    (((modA_smooth P ρ hTT).sub (hA0s ρ)).differentiableOn (by simp)).differentiableAt hnhds
  have hgd : DifferentiableAt ℝ (fun w => star (u ρ w) * NF.dZ (u ρ) w) ζ :=
    ((hws ρ).differentiableOn (by simp)).differentiableAt hnhds
  have hder : fderiv ℝ (fun w => modA P ρ w - A ρ w) ζ =
      fderiv ℝ (fun w => modA P ρ w - A0 ρ w) ζ - fderiv ℝ (fun w => star (u ρ w) * NF.dZ (u ρ) w) ζ := by
    exact hev.fderiv_eq.trans (hfd.hasFDerivAt.sub hgd.hasFDerivAt).fderiv
  have h1 := hcurv ρ ζ hζ
  have h2 := hPc P.TT (u ρ) (hu ρ).1 (hu ρ).2 ζ hζ
  unfold NF.dZb at h1 h2 ⊢
  rw [hder, ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply]
  have key : ∀ a b c d : ℂ, (1 / 2 : ℂ) * ((a - b) + Complex.I * (c - d)) =
      (1 / 2 : ℂ) * (a + Complex.I * c) - (1 / 2 : ℂ) * (b + Complex.I * d) := by
    intros; ring
  rw [key, Complex.sub_re, h1, h2, sub_zero]

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

theorem modA_eq_fun (P : M.Par) (ρ : M.Ty P) :
    modA P ρ = fun w => (M.aC P ρ : ℂ) * star w * (w * star w - (P.TT : ℂ))⁻¹ := by
  funext w
  have h : (w * star w : ℂ) = (Complex.normSq w : ℂ) := Complex.mul_conj w
  rw [h]
  simp only [modA, div_eq_mul_inv]

theorem dZb_modA (P : M.Par) (ρ : M.Ty P) {ζ : ℂ} (hζ : ζ ∈ Ann P) :
    NF.dZb (modA P ρ) ζ = -(((M.aC P ρ * P.TT : ℝ) : ℂ)) / ((Complex.normSq ζ : ℂ) - (P.TT : ℂ)) ^ 2 := by
  have hns : (ζ * star ζ : ℂ) = (Complex.normSq ζ : ℂ) := Complex.mul_conj ζ
  have hlt : P.TT < Complex.normSq ζ := hζ
  have hN0 : ζ * star ζ - (P.TT : ℂ) ≠ 0 := by
    rw [hns, ← Complex.ofReal_sub]
    exact Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr hlt.ne')
  have hS := (hasFDerivAt_id (𝕜 := ℝ) ζ).star
  have hN := ((hasFDerivAt_id (𝕜 := ℝ) ζ).mul hS).sub_const (P.TT : ℂ)
  have hI := ((hasDerivAt_inv hN0).hasFDerivAt.restrictScalars ℝ).comp ζ hN
  have hF := ((hasFDerivAt_const (𝕜 := ℝ) (M.aC P ρ : ℂ) ζ).mul hS).mul hI
  have hF' : HasFDerivAt (fun w : ℂ => (M.aC P ρ : ℂ) * star w * (w * star w - (P.TT : ℂ))⁻¹) _ ζ := hF
  rw [modA_eq_fun]
  simp only [NF.dZb]
  rw [hF'.fderiv]
  rw [← hns]
  simp [Complex.star_def]
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem re_dZb_modA (P : M.Par) (ρ : M.Ty P) {ζ : ℂ} (hζ : ζ ∈ Ann P) :
    (NF.dZb (modA P ρ) ζ).re = -(M.aC P ρ * P.TT) / (Complex.normSq ζ - P.TT) ^ 2 := by
  rw [dZb_modA P ρ hζ]
  have h : (-(((M.aC P ρ * P.TT : ℝ) : ℂ)) / ((Complex.normSq ζ : ℂ) - (P.TT : ℂ)) ^ 2) =
      ((-(M.aC P ρ * P.TT) / (Complex.normSq ζ - P.TT) ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [h, Complex.ofReal_re]

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end
