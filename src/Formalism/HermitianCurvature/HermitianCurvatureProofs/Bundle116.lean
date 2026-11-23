module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle054
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NfRadOrder0OfRadRed
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle058
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsAdmissibleSplittingCharPairMulTwist
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle092
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle103
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle111
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsFrameTwo
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameCompletion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameEntries
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle090
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle112
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Lemma
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
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CoordinateCommuteRaisingConstant
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.LNab

noncomputable section

open Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

section closure

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

abbrev Coef (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] : Type :=
  (j : ℕ) → ℂ → (ContinuousMultilinearMap ℝ (fun _ : Fin j => ℂ) (Wq →L[ℂ] Wp) →L[ℝ] (Wq →L[ℂ] Wp))

abbrev AnnZ (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) : Set ℂ :=
  {ζ : ℂ | Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ}

abbrev Dj (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (j : ℕ)
    (q : (Fin P.r → ℂ) × ℂ) : ContinuousMultilinearMap ℝ (fun _ : Fin j => ℂ) (Wq →L[ℂ] Wp) :=
  iteratedFDeriv ℝ j (fun ζ => NF.radR P.k P.r Bs.z Bs.z' Bs.μsec Φ (q.1, ζ)) q.2

def Rep (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (T : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))
    (n : ℕ) (A : Coef Wp Wq) : Prop :=
  (∀ j, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (A j) (AnnZ P Bs)) ∧
    ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (q : (Fin P.r → ℂ) × ℂ), q ∈ NF.QR P.k P.r Bs.z Bs.z' →
      NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (T Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q =
        ∑ j ∈ Finset.range (n + 1), A j q.2 (Dj P Bs (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) j q)

theorem rep_ext {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}
    {T : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} {n m : ℕ} (hnm : n ≤ m) {A : Coef Wp Wq}
    (h : Rep P Bs T n A) : Rep P Bs T m (fun j ζ => if j ≤ n then A j ζ else 0) := by
  refine ⟨fun j => ?_, fun Φ q hq => ?_⟩
  · by_cases hj : j ≤ n
    · simp only [hj, if_true]; exact h.1 j
    · simp only [hj, if_false]; exact contDiffOn_const
  · rw [h.2 Φ q hq]
    symm
    rw [← Finset.sum_subset (Finset.range_mono (by omega : n + 1 ≤ m + 1))]
    · refine Finset.sum_congr rfl fun j hj => ?_
      have : j ≤ n := by simp at hj; omega
      simp only [this, if_true]
    · intro j _ hj
      have : ¬ j ≤ n := by simp at hj; omega
      simp only [this, if_false, ContinuousLinearMap.zero_apply]

theorem radR_smul' (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (c : ℂ) (F : Q.Fn P.k P.r (Wq →L[ℂ] Wp))
    (x : (Fin P.r → ℂ) × ℂ) :
    NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (c • F) x = c • NF.radR P.k P.r Bs.z Bs.z' Bs.μsec F x := by
  unfold NF.radR
  by_cases hx : x ∈ NF.QR P.k P.r Bs.z Bs.z' <;> simp [hx]

theorem radR_zero'' (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (x : (Fin P.r → ℂ) × ℂ) :
    NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (0 : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x = 0 := by
  unfold NF.radR
  by_cases hx : x ∈ NF.QR P.k P.r Bs.z Bs.z' <;> simp [hx]

theorem radDZ_zero (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) :
    RadDZ P Bs (0 : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) := by
  refine ⟨0, fun _ _ => 0, fun _ => contDiffOn_const, fun Φ q _ => ?_⟩
  have : (((0 : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
      Q.Fn P.k P.r (Wq →L[ℂ] Wp)) = 0 := rfl
  rw [this, radR_zero'']
  simp

theorem radDZ_one (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) :
    RadDZ P Bs (1 : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) := by
  refine ⟨0, fun j _ => ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => ℂ) (Wq →L[ℂ] Wp) (fun _ => 0),
    fun _ => contDiffOn_const, fun Φ q _ => ?_⟩
  rw [Finset.sum_range_one]
  show _ = (iteratedFDeriv ℝ 0 (fun ζ => NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (q.1, ζ)) q.2)
    (fun _ => 0)
  rw [iteratedFDeriv_zero_apply]
  rfl

theorem radDZ_add {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}
    {T1 T2 : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} (h1 : RadDZ P Bs T1) (h2 : RadDZ P Bs T2) :
    RadDZ P Bs (T1 + T2) := by
  obtain ⟨n1, A1, hr1⟩ := h1
  obtain ⟨n2, A2, hr2⟩ := h2
  have e1 := rep_ext (by omega : n1 ≤ n1 + n2) hr1
  have e2 := rep_ext (by omega : n2 ≤ n1 + n2) hr2
  refine ⟨n1 + n2, fun j ζ => (if j ≤ n1 then A1 j ζ else 0) + (if j ≤ n2 then A2 j ζ else 0),
    fun j => (e1.1 j).add (e2.1 j), fun Φ q hq => ?_⟩
  have hc : ((T1 + T2) Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) = (T1 Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) + (T2 Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) := rfl
  rw [hc, Formalism.FourierDecayAlt.P.NFRO.radR_add, e1.2 Φ q hq, e2.2 Φ q hq, ← Finset.sum_add_distrib]
  rfl

theorem radDZ_sum {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq} {ι : Type*} (s : Finset ι)
    (T : ι → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) (h : ∀ i ∈ s, RadDZ P Bs (T i)) :
    RadDZ P Bs (∑ i ∈ s, T i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using radDZ_zero P Bs
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact radDZ_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem radDZ_comp_left {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}
    {T T' : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} (hT : RadDZ P Bs T)
    (Mf : ℂ → ((Wq →L[ℂ] Wp) →L[ℝ] (Wq →L[ℂ] Wp)))
    (hM : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Mf (AnnZ P Bs))
    (h : ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (q : (Fin P.r → ℂ) × ℂ), q ∈ NF.QR P.k P.r Bs.z Bs.z' →
      NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (T' Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q =
        Mf q.2 (NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (T Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q)) :
    RadDZ P Bs T' := by
  obtain ⟨n, A, hA, hTA⟩ := hT
  refine ⟨n, fun j ζ => (Mf ζ).comp (A j ζ), fun j => hM.clm_comp (hA j), fun Φ q hq => ?_⟩

  rw [h Φ q hq, hTA Φ q hq, map_sum]
  rfl

theorem radDZ_fun_left {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}
    {T T' : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} (hT : RadDZ P Bs T) (s : ℂ → ℂ)
    (hs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) s (AnnZ P Bs))
    (h : ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (q : (Fin P.r → ℂ) × ℂ), q ∈ NF.QR P.k P.r Bs.z Bs.z' →
      NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (T' Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q =
        s q.2 • NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (T Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q) :
    RadDZ P Bs T' :=
  radDZ_comp_left hT (fun ζ => s ζ • ContinuousLinearMap.id ℝ (Wq →L[ℂ] Wp)) (hs.smul contDiffOn_const)
    fun Φ q hq => by rw [h Φ q hq]; rfl

theorem radDZ_smul {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}
    {T : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} (hT : RadDZ P Bs T) (c : ℂ) :
    RadDZ P Bs (c • T) :=
  radDZ_fun_left hT (fun _ => c) contDiffOn_const fun Φ q _ => by
    have : ((c • T) Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) = c • (T Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) := rfl
    rw [this, radR_smul']

theorem radDZ_neg {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}
    {T : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} (hT : RadDZ P Bs T) : RadDZ P Bs (-T) := by
  have := radDZ_smul hT (-1)
  rwa [neg_one_smul] at this

end closure

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.LNab
end

section

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants

noncomputable section

theorem pointwise_bound_normal_form_holds : NFBddPtw := by
  intro P L hTT hL b hb
  obtain ⟨C, Mx, hSA, hC, hM⟩ := Formalism.FourierDecayAlt.P.MAx3.AD.SAB_closure (hTTp := hTT) (hL := hL)
    (hLaw := Formalism.FourierDecayAlt.P.analytic_laws P.r P.TT hTT.le) hb
  refine ⟨(Fintype.card (M.Ty P) : ℝ) * ((Fintype.card (M.Ty P) : ℝ) * C ^ 2), fun u q => ?_⟩
  have key : ∀ ρ, ‖MA.evQ P (MA.actA P b u ρ) q‖ ^ 2 ≤
      (Fintype.card (M.Ty P) : ℝ) * (C ^ 2 * ∑ ρ', ‖MA.evQ P (u ρ') q‖ ^ 2) := by
    intro ρ
    rw [hSA.1 u q ρ]
    have h1 : ‖∑ π', Mx q ρ π' * MA.evQ P (u π') q‖ ≤ ∑ π', C * ‖MA.evQ P (u π') q‖ := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun π' _ => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hM q ρ π') (norm_nonneg _)
    have h2 := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (M.Ty P)))
      (f := fun π' => C * ‖MA.evQ P (u π') q‖)
    calc _ ≤ (∑ π', C * ‖MA.evQ P (u π') q‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ _ := h2
      _ = _ := by
        rw [Finset.card_univ]
        simp only [mul_pow, ← Finset.mul_sum]
  calc _ ≤ ∑ ρ : M.Ty P, (Fintype.card (M.Ty P) : ℝ) * (C ^ 2 * ∑ ρ', ‖MA.evQ P (u ρ') q‖ ^ 2) :=
        Finset.sum_le_sum fun ρ _ => key ρ
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

end

end Formalism.FourierDecayAlt.P.CutBP
end

section

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.QrD

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

namespace KLR

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem exp_intertwine {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] [FiniteDimensional ℂ Wq] (A : Wq →L[ℂ] Wp) (D' : Wq →L[ℂ] Wq)
    (D : Wp →L[ℂ] Wp) (h : A.comp D' = D.comp A) :
    A.comp (NormedSpace.exp D') = (NormedSpace.exp D).comp A := by
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  have : CompleteSpace Wq := FiniteDimensional.complete ℂ Wq
  have hp : ∀ n : ℕ, A.comp (D' ^ n) = (D ^ n).comp A := by
    intro n
    induction n with
    | zero => ext v; simp
    | succ n ih =>
      ext v
      have e1 := congrArg (fun T : Wq →L[ℂ] Wp => T (D' v)) ih
      have e2 := congrArg (fun T : Wq →L[ℂ] Wp => T v) h
      simp only [ContinuousLinearMap.comp_apply] at e1 e2 ⊢
      rw [pow_succ, pow_succ, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, e1, e2]
  have h1 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) D'
  have h2 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) D
  have g1 := h1.map (ContinuousLinearMap.compL ℂ Wq Wq Wp A) (ContinuousLinearMap.continuous _)
  have g2 := h2.map ((ContinuousLinearMap.compL ℂ Wq Wp Wp).flip A) (ContinuousLinearMap.continuous _)
  have e : ((ContinuousLinearMap.compL ℂ Wq Wq Wp A) ∘ fun n : ℕ => ((n.factorial : ℂ)⁻¹) • D' ^ n) =
      (((ContinuousLinearMap.compL ℂ Wq Wp Wp).flip A) ∘ fun n : ℕ => ((n.factorial : ℂ)⁻¹) • D ^ n) := by
    funext n
    simp only [Function.comp_apply, ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp, hp]
  rw [e] at g1
  exact g1.unique g2

theorem exp_conj {g : Mx k r} (hg : IsUnit g.det) (X : Mx k r) :
    NormedSpace.exp (g * X * g⁻¹) = g * NormedSpace.exp X * g⁻¹ := by
  have h := HermitianFormRankFour.exp_semiconj (g * X * g⁻¹) X g (by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hg, Matrix.mul_one])
  calc NormedSpace.exp (g * X * g⁻¹) = NormedSpace.exp (g * X * g⁻¹) * g * g⁻¹ := by
        rw [Matrix.mul_assoc (NormedSpace.exp (g * X * g⁻¹)) g g⁻¹, Matrix.mul_nonsing_inv _ hg, Matrix.mul_one]
    _ = g * NormedSpace.exp X * g⁻¹ := by rw [h]

theorem pi_exp_frame {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (W →L[ℂ] W)} (hπ : Qr.IsRepW k r z π) {m : ℕ}
    {Bs : Fin m → Fin (2 * r + k + 1) → ℂ} (hB : IsFrameOf k r [z] Bs) (B : Matrix (Fin m) (Fin m) ℂ)
    (hBs : Bᴴ = -B) :
    InLieW k r z (∑ p : Fin m × Fin m, B p.1 p.2 • unitB (Hpk k r) Bs p.1 p.2) ∧
    π (NormedSpace.exp (∑ p : Fin m × Fin m, B p.1 p.2 • unitB (Hpk k r) Bs p.1 p.2)) =
      NormedSpace.exp (∑ p : Fin m × Fin m, B p.1 p.2 • ecOp π (unitB (Hpk k r) Bs p.1 p.2)) := by
  obtain ⟨X, hX⟩ : ∃ X, X = ∑ p : Fin m × Fin m, B p.1 p.2 • unitB (Hpk k r) Bs p.1 p.2 := ⟨_, rfl⟩
  rw [← hX]
  have hsk : Xᴴ * Hpk k r + Hpk k r * X = 0 := by
    rw [hX, ← KLG.sum_unitB]
    exact HermitianFormRankFour.skew_of Qx8.hpk_herm hBs
  have hs := HermitianFormSums.ec_sum elementary_lie_elements hπ Finset.univ (fun p : Fin m × Fin m => B p.1 p.2)
    (fun p => unitB (Hpk k r) Bs p.1 p.2) (fun p => frame_lie hB p.1 p.2) 0 (SkewHermitianParts.inGl_zero z)
  beta_reduce at hs
  rw [← hX] at hs
  have hL : InLieW k r z X := by
    have := hs.1.1
    rwa [SkewHermitianParts.hpart1_skew hsk] at this
  have he : ecOp π X = dOp π X := by
    unfold ecOp
    rw [SkewHermitianParts.hpart1_skew hsk, SkewHermitianParts.hpart2_skew hsk, SkewHermitianParts.dOp_zero, smul_zero, add_zero]
  refine ⟨hL, ?_⟩
  have h2 := representation_exp W k r z π hπ X hL 1
  simp only [Complex.ofReal_one, one_smul] at h2
  rw [h2, ← he, hs.2]

end KLR

open KLR in
theorem lie_group_realization : KLLieGrp := by
  intro Wp Wq _ _ _ _ _ _ k r z z' π π' hz hz' hT hT' hπ hπ' g hg hGG Fr hFr A hA h hh h' hh' hgh
  have hgu := hg.1
  have hgU : IsUnit g.det := WeylGroupFacts.isUnit_of_uh hgu
  have hhU : IsUnit h.det := WeylGroupFacts.isUnit_of_uh hh.1
  have cancel : ∀ M : Mx k r, IsUnit M.det → ∀ v, M⁻¹ *ᵥ (M *ᵥ v) = v := fun M hM v => by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hM, Matrix.one_mulVec]
  obtain ⟨y, hy⟩ : ∃ y, y = g⁻¹ *ᵥ z := ⟨_, rfl⟩
  rw [← hy] at hFr
  have hgy : g *ᵥ y = z := by rw [hy]; exact Qx8.inv_mulVec_uh hgu z
  have hginv : g⁻¹ ∈ Glev k r (Fin.last r) := FrameEntries.glev_inv hg
  have hyW : inWb k r y := by rw [hy]; exact Qx8.inWb_mulVec hginv hz
  have hyy : herm (Hpk k r) y y = -((Tz k r z : ℝ) : ℂ) := by
    rw [← Qx8.herm_self', ← hgy, Qx8.herm_UH hgu]
  have hζ : herm (Hpk k r) z' y = zetaL k r z z' (Fin.last r) g := by
    unfold zetaL
    rw [Qx8.fvec_last, Qx8.fvec_last, ← hgy, Qx8.herm_UH hgu]
  have hpos := Qx8.GGl_pos hz hz' hT hT' hg hGG
  have hG2 : 0 < Complex.normSq (herm (Hpk k r) y z') - Tz k r z * Tz k r z' := by
    rw [← Qx8.herm_conj, hζ]
    have hc : Complex.normSq (star (zetaL k r z z' (Fin.last r) g)) = Complex.normSq (zetaL k r z z' (Fin.last r) g) :=
      Complex.normSq_conj _
    rw [hc]
    exact hpos
  obtain ⟨e', s, c, hs, he', he'W, he'z, he'e⟩ := Qx8.orth_unit hyW hz' hT' hyy (Qx8.herm_self' z') hG2
  have hFz' : ∀ a, herm (Hpk k r) (Fr a) z' = 0 := fun a => hFr.2.2 a z' (by simp)
  have hFy : ∀ a, herm (Hpk k r) (Fr a) y = 0 := fun a => hFr.2.2 a y (by simp)
  have hFe : ∀ a, herm (Hpk k r) (Fr a) e' = 0 := by
    intro a
    rw [he', Qx8.herm_smul_right', Qx8.herm_add_right', Qx8.herm_smul_right', hFy, hFz']
    simp
  have hFr2 : IsFrameOf k r [z', e'] Fr := ⟨hFr.1, hFr.2.1, fun a v hv => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact hFz' a
    · exact hFe a⟩
  have hFz'1 : IsFrameOf k r [z'] Fr := ⟨hFr.1, hFr.2.1, fun a v hv => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    subst hv
    exact hFz' a⟩

  have e1 : h *ᵥ (g *ᵥ (h' *ᵥ y)) = h *ᵥ z := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hgh, hgy, hh.2.2]
  have e2 : g *ᵥ (h' *ᵥ y) = z := by
    rw [← cancel h hhU (g *ᵥ (h' *ᵥ y)), e1, cancel h hhU z]
  have hh'y : h' *ᵥ y = y := by
    calc h' *ᵥ y = g⁻¹ *ᵥ (g *ᵥ (h' *ᵥ y)) := (cancel g hgU _).symm
      _ = y := by rw [e2, hy]
  have hh'e : h' *ᵥ e' = e' := by
    rw [he', Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul, hh'y, hh'.2.2]

  obtain ⟨B, hBs, hBe⟩ := KLG.stab_exp hz' hT' he'W he'z he'e hFr2 hh' hh'e
  rw [KLG.sum_unitB] at hBe
  obtain ⟨-, hE'⟩ := pi_exp_frame hπ' hFz'1 B hBs
  have hgF : IsFrameOf k r [z] (fun a => g *ᵥ Fr a) := ⟨fun a => Qx8.inWb_mulVec hg (hFr.1 a), fun a b => by
    rw [Qx8.herm_UH hgu]; exact hFr.2.1 a b, fun a v hv => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    subst hv
    rw [← hgy, Qx8.herm_UH hgu]
    exact hFy a⟩
  obtain ⟨hL, hE⟩ := pi_exp_frame hπ hgF B hBs
  have hconj : g * h' * g⁻¹ = NormedSpace.exp
      (∑ p : Fin (k - 1) × Fin (k - 1), B p.1 p.2 • unitB (Hpk k r) (fun a => g *ᵥ Fr a) p.1 p.2) := by
    have hsum : (∑ p : Fin (k - 1) × Fin (k - 1), B p.1 p.2 • unitB (Hpk k r) (fun a => g *ᵥ Fr a) p.1 p.2) =
        g * (∑ p : Fin (k - 1) × Fin (k - 1), B p.1 p.2 • unitB (Hpk k r) Fr p.1 p.2) * g⁻¹ := by
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Matrix.mul_smul, Matrix.smul_mul, Qx8.unitB_conj Fr p.1 p.2 hgu]
    rw [hsum, ← hBe]
    exact (exp_conj hgU _).symm
  have hD : A.comp (∑ p : Fin (k - 1) × Fin (k - 1), B p.1 p.2 • ecOp π' (unitB (Hpk k r) Fr p.1 p.2)) =
      (∑ p : Fin (k - 1) × Fin (k - 1), B p.1 p.2 • ecOp π (unitB (Hpk k r) (fun a => g *ᵥ Fr a) p.1 p.2)).comp A := by
    ext v

    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    map_sum, map_smul]
    refine Finset.sum_congr rfl fun p _ => ?_
    congr 1
    exact hA p.1 p.2 v
  have hX := exp_intertwine A _ _ hD
  rw [← hE', ← hE, hBe, ← hconj] at hX
  have hmem : g * h' * g⁻¹ ∈ UWset k r z := by
    rw [hconj]
    have := exp_uw hL 1
    simpa using this
  have hone : h * (g * h' * g⁻¹) = 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hgh, Matrix.mul_nonsing_inv _ hgU]
  rw [hX, ← ContinuousLinearMap.comp_assoc, ← hπ.1.2 h hh _ hmem, hone, hπ.1.1]
  ext v
  simp

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP.Dc

open Formalism.FourierDecayAlt.P.B2x3 Formalism.FourierDecayAlt.P.SettingConstruction Formalism.FourierDecayAlt.P.TheSec Formalism.FourierDecayAlt.B2

noncomputable section

section ps

variable {TT : ℝ}

lemma gg_eval (ζ : ℂ) : gg TT ζ = MvPolynomial.eval ![ζ, conj ζ, sig TT ζ]
    (MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C (TT : ℂ)) := by
  unfold Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.gg
  simp only [MvPolynomial.eval_sub, MvPolynomial.eval_mul, MvPolynomial.eval_X, MvPolynomial.eval_C,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Complex.mul_conj]
  push_cast
  ring

lemma ps_const (c : ℂ) : PS TT (fun _ => c) := ⟨0, MvPolynomial.C c, fun ζ _ => by simp⟩

lemma ps_id : PS TT (fun ζ => ζ) := ⟨0, MvPolynomial.X 0, fun ζ _ => by simp⟩

lemma ps_conj : PS TT (fun ζ => conj ζ) := ⟨0, MvPolynomial.X 1, fun ζ _ => by simp⟩

lemma ps_sig : PS TT (fun ζ => sig TT ζ) := ⟨0, MvPolynomial.X 2, fun ζ _ => by simp⟩

lemma ps_add {f g : ℂ → ℂ} (hf : PS TT f) (hg : PS TT g) : PS TT (fun ζ => f ζ + g ζ) := by
  obtain ⟨m, p, hp⟩ := hf
  obtain ⟨n, q, hq⟩ := hg
  refine ⟨m + n, (MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C (TT : ℂ)) ^ n * p + (MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C (TT : ℂ)) ^ m * q, fun ζ hζ => ?_⟩
  rw [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_mul, MvPolynomial.eval_pow,
    MvPolynomial.eval_pow, ← gg_eval, ← hp ζ hζ, ← hq ζ hζ]
  ring

lemma ps_mul {f g : ℂ → ℂ} (hf : PS TT f) (hg : PS TT g) : PS TT (fun ζ => f ζ * g ζ) := by
  obtain ⟨m, p, hp⟩ := hf
  obtain ⟨n, q, hq⟩ := hg
  refine ⟨m + n, p * q, fun ζ hζ => ?_⟩
  rw [MvPolynomial.eval_mul, ← hp ζ hζ, ← hq ζ hζ]
  ring

lemma sig_sq {ζ : ℂ} (hζ : TT < Complex.normSq ζ) : sig TT ζ * sig TT ζ = gg TT ζ := by
  unfold Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.gg Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.sig
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]

lemma sig_ne {ζ : ℂ} (hζ : TT < Complex.normSq ζ) : sig TT ζ ≠ 0 := by
  unfold Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.sig
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by linarith))

lemma ps_sigInv : PS TT (fun ζ => (sig TT ζ)⁻¹) := by
  refine ⟨1, MvPolynomial.X 2, fun ζ hζ => ?_⟩
  rw [pow_one, ← sig_sq hζ, mul_assoc, mul_inv_cancel₀ (sig_ne hζ), mul_one]
  simp

end ps

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP.Dc
end
