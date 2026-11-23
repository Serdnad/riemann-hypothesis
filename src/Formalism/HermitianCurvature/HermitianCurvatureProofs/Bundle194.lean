module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle183
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutDec
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle184
public import Formalism.HermitianCurvature.Bundle004
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle130
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TriangleInequalityAtPlace
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CornerBZero
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableCsmul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutER
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

def xD (φ : ℝ → ℝ) : ℝ → ℝ := fun x => x * deriv φ x

def IsSCoef {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq)
    (w : List C.Letter) (e : Wd.Ix (Fin w.length)) (Q : ℕ) (L : Fin (Q + 1) → B.DiffOp P.k P.r Wp Wq) : Prop :=
  ∀ (s : ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), B.CkOn ⊤ (B.GV P.k P.r) F → ∀ g ∈ C6.domL p.T.base ∅,
    ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ (-s) : ℝ) : ℂ) •
        p.Θ.Θ w e (fun g' => ((Gf P.k P.r p.T.base.z p.T.base.z' g' ^ s : ℝ) : ℂ) • F g') g =
      ∑ q : Fin (Q + 1), ((s ^ (q : ℕ) : ℝ) : ℂ) • B.opApply (L q) F g

def NFUnfoldTop : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (c : Fin (P.r + 1) → ℂ), w ≠ [] →
    D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) → 0 < TBB.Gp p (TBB.bigPt P.r c) →
      topD p H w c = (Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c)) *
          Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c))) *
        ∑ e : Wd.Ix (Fin w.length), ∑ ρ : M.Ty P, Top.dH P p.l0 (TBB.TTp p) w (TBB.bigPt P.r c) e ρ ^ 2 *
          ‖B.hsVec ((p.TP.E ρ).comp (p.V (p.Θ.Θ w e H) (TBB.bigPt P.r c)))‖ ^ 2

def NFVMul : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (φ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (γ : C.LPt), D.IsLocPt γ (P.r + 1) → 0 < TBB.Gp p γ →
      p.V (fun g => ((φ (Gf P.k P.r p.T.base.z p.T.base.z' g) : ℝ) : ℂ) • F g) γ = ((φ (TBB.Gp p γ) : ℝ) : ℂ) • p.V F γ

def NFCutSup : Prop :=
  ∀ χ : ℝ → ℝ, C6.IsCut0 χ → ∀ q : ℕ, ∃ K : ℝ, ∀ ε : ℝ, 0 < ε → ∀ x : ℝ, 0 < x →
    |(xD^[q] (fun y => χ (y / ε))) x| ≤ K

def NFLeibV : Prop :=
  ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → ∀ w, KB.CutWord P p.l0 w → ∀ e : Wd.Ix (Fin w.length),
      ∃ (Q : ℕ) (L : Fin (Q + 1) → B.DiffOp P.k P.r Wp Wq),
        (∀ q, B.SmoothCoef (C6.domL p.T.base ∅) (L q)) ∧ IsSCoef p w e Q L ∧
        ∀ φ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → ∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A : ℝ),
          B.CkOn ⊤ (B.GV P.k P.r) F → (∀ m : ℕ, B.InCC A m F) →
          Cc * ((P.r : ℝ) + 1) ^ 4 * ((w.length : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
          ∀ γ : C.LPt, D.IsLocPt γ (P.r + 1) → 0 < TBB.Gp p γ →
            p.V (p.Θ.Θ w e (fun g => ((φ (Gf P.k P.r p.T.base.z p.T.base.z' g) : ℝ) : ℂ) • F g)) γ =
              ∑ q : Fin (Q + 1), (((xD^[(q : ℕ)] φ) (TBB.Gp p γ) : ℝ) : ℂ) • p.V (B.opApply (L q) F) γ

def NFEmptyOps : Prop :=
  ∃ C₁ : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (N : ℕ), ∃ Th₀ Th₁ : B.DiffOp P.k P.r Wp Wq, NFOpOK C₁ p N Th₀ ∧ NFOpOK C₁ p N Th₁ ∧
      ∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (g : B.Mat P.k P.r),
        B.opApply Th₀ F g = F g ∧ B.opApply Th₁ F g = ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ N : ℝ) : ℂ) • F g

theorem unfolding_top_term_holds : NFUnfoldTop := by
  intro Wp Wq _ _ _ _ _ _ P p H w c hw hloc _
  have hn : TBB.normC (fun _ => 1) w = 1 := by
    simp [TBB.normC]
  have hRR : p.RR H (P.r + 1) w (TBB.bigPt P.r c) (TBB.bigPt P.r c) =
      Top.topOf P p.l0 p.T p.ν' p.m₀ p.Θ p.TP H w (TBB.bigPt P.r c) (TBB.bigPt P.r c) := by
    rw [KB.Pl.RR, D.RRplace, dite_eq_left ⟨hloc, hloc⟩, dite_eq_right (Nat.not_succ_le_self _), if_pos rfl, if_neg hw]
  show (TBB.NP p (fun _ => 1) H (P.r + 1) w (TBB.bigPt P.r c) (TBB.bigPt P.r c)).re = _
  rw [TBB.NP, hn, div_one, hRR, Top.topOf, Complex.re_ofReal_mul]
  congr 1
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  have hsq : ∀ v : PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp), (inner ℂ v v : ℂ).re = ‖v‖ ^ 2 :=
    fun v => by simpa using inner_self_eq_norm_sq (𝕜 := ℂ) v
  rw [Complex.re_ofReal_mul, B.hsInner, hsq]
  simp only [TBB.TTp, KB.Pl.V]
  ring

end

end Formalism.FourierDecayAlt.P.CutBP
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def cay {k r : ℕ} (X : B.Mat k r) : B.Mat k r := (1 + X) * (1 - X)⁻¹

def cayInv {k r : ℕ} (g : B.Mat k r) : B.Mat k r := (g - 1) * (g + 1)⁻¹

def LieBasis : Prop :=
  ∀ k r : ℕ, ∃ (d : ℕ) (L : (Fin d → ℝ) →L[ℝ] B.Mat k r) (M : B.Mat k r →L[ℝ] (Fin d → ℝ)),
    (∀ x, B.inLie k r (L x)) ∧ (∀ x, M (L x) = x) ∧ ∀ X, B.inLie k r X → L (M X) = X

def CayAlg : Prop :=
  ∀ k r : ℕ,
    (∀ X : B.Mat k r, B.inLie k r X → IsUnit (1 - X) → cay X ∈ B.GV k r ∧ IsUnit (cay X + 1) ∧ cayInv (cay X) = X) ∧
    ∀ g ∈ B.GV k r, IsUnit (g + 1) → B.inLie k r (cayInv g) ∧ IsUnit (1 - cayInv g) ∧ cay (cayInv g) = g

def GVGrp : Prop :=
  ∀ k r : ℕ, IsUnit ((1 : B.Mat k r) + 1) ∧ ∀ g₀ ∈ B.GV k r, g₀⁻¹ * g₀ = 1 ∧
    ∀ h ∈ B.GV k r, g₀ * h ∈ B.GV k r ∧ g₀⁻¹ * h ∈ B.GV k r ∧ g₀ * (g₀⁻¹ * h) = h

def CaySmooth : Prop :=
  ∀ (k r : ℕ) (g₀ : B.Mat k r),
    IsOpen {X : B.Mat k r | IsUnit (1 - X)} ∧ IsOpen {m : B.Mat k r | IsUnit (g₀⁻¹ * m + 1)} ∧
    ContDiffOn ℝ ∞ (fun X : B.Mat k r => g₀ * cay X) {X | IsUnit (1 - X)} ∧
    ContDiffOn ℝ ∞ (fun m : B.Mat k r => cayInv (g₀⁻¹ * m)) {m | IsUnit (g₀⁻¹ * m + 1)}

theorem gChart_of (hB : LieBasis) (hA : CayAlg) (hG : GVGrp) (hS : CaySmooth) : GChart := by
  intro k r
  obtain ⟨d, L, M, hL, hML, hLM⟩ := hB k r
  refine ⟨d, fun g₀ hg₀ => ?_⟩
  obtain ⟨hA1, hA2⟩ := hA k r
  obtain ⟨hOne, hGg⟩ := hG k r
  obtain ⟨hinv, hmul⟩ := hGg g₀ hg₀
  obtain ⟨hO1, hU1, hκs, hΦs⟩ := hS k r g₀
  refine ⟨{x | IsUnit (1 - L x)}, {m | IsUnit (g₀⁻¹ * m + 1)}, fun x => g₀ * cay (L x),
    fun m => M (cayInv (g₀⁻¹ * m)), hO1.preimage L.continuous, hU1, ?_, ?_, ?_, ?_, ?_⟩
  · show IsUnit (g₀⁻¹ * g₀ + 1)
    rw [hinv]; exact hOne
  · exact hκs.comp L.contDiff.contDiffOn (fun x hx => hx)
  · exact M.contDiff.comp_contDiffOn hΦs
  · intro x hx
    obtain ⟨hc, hc1, hci⟩ := hA1 (L x) (hL x) hx
    have e : g₀⁻¹ * (g₀ * cay (L x)) = cay (L x) := by
      rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]
    refine ⟨(hmul _ hc).1, ?_, ?_⟩
    · show IsUnit (g₀⁻¹ * (g₀ * cay (L x)) + 1)
      rw [e]; exact hc1
    · show M (cayInv (g₀⁻¹ * (g₀ * cay (L x)))) = x
      rw [e, hci, hML]
  · intro g hg hgG
    obtain ⟨-, hh, hgh⟩ := hmul g hgG
    obtain ⟨hl, hu, hc⟩ := hA2 _ hh hg
    refine ⟨?_, ?_⟩
    · show IsUnit (1 - L (M (cayInv (g₀⁻¹ * g))))
      rw [hLM _ hl]; exact hu
    · show g₀ * cay (L (M (cayInv (g₀⁻¹ * g)))) = g
      rw [hLM _ hl, hc, hgh]

def IsDomOmPlus : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), inWb k r z → inWb k r z' →
    Q.IsDom k r z z' 0 (Q.OmPlus k r z z')

def RightTypeAction0 : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    [FiniteDimensional ℂ Wq]
    (k r m : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq))
    (D : Set (Q.Mx k r)) (mm : ℕ∞), inWb k r z → inWb k r z' → Q.IsDom k r z z' 0 D →
    IsCRepOn (UWset k r z') π' → ContinuousOn π' (UWset k r z') →
    ∀ J ∈ Gr.FFlM mm k r z z' π π' 0 D, ∀ g ∈ Q.Glev k r 0 ∩ D,
    ∀ Bs : Fin m → Fin (2 * r + k + 1) → ℂ, Q.IsFrameOf k r [z'] Bs → ∀ (w : ℂ) (v : Wq),
      Q.capR k r Bs w J g v = J g (Q.capRep k r π' Bs w v)

def LeftTypeAction0 : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    [FiniteDimensional ℂ Wp]
    (k r m : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq))
    (D : Set (Q.Mx k r)) (mm : ℕ∞), inWb k r z → inWb k r z' → Q.IsDom k r z z' 0 D →
    IsCRepOn (UWset k r z) π → ContinuousOn π (UWset k r z) →
    ∀ J ∈ Gr.FFlM mm k r z z' π π' 0 D, ∀ g ∈ Q.Glev k r 0 ∩ D,
    ∀ Bs : Fin m → Fin (2 * r + k + 1) → ℂ, Q.IsFrameOf k r [z] Bs → ∀ (w : ℂ) (v : Wq),
      Q.capLft k r Bs w J g v = Q.capRep k r π Bs w (J g v)

theorem uCap_of (h0 : IsDomOmPlus) (hR : RightTypeAction0) (hL : LeftTypeAction0) : UCap := by
  intro k r Wp Wq _ _ _ _ _ _ D u u' J hT hT' hF
  have hD := h0 k r D.z D.z' D.z_mem D.z'_mem
  have hg0 : ∀ g ∈ JF.Om k r D.z D.z', g ∈ Q.Glev k r 0 ∩ Q.OmPlus k r D.z D.z' :=
    fun g hg => ⟨⟨hg.1, fun a ha => absurd ha (Nat.not_lt_zero _)⟩, hg.2⟩
  refine ⟨fun Bs hBs w => ⟨∏ i ∈ Finset.Icc 1 k, (w - (k : ℂ) / 2 + 1 / 2 + (u i : ℂ)), fun g hg => ?_⟩,
    fun Bs hBs w => ⟨∏ i ∈ Finset.Icc 1 k, (w - (k : ℂ) / 2 + 1 / 2 + (u' i : ℂ)), fun g hg => ?_⟩⟩
  · refine ContinuousLinearMap.ext fun v => ?_
    rw [hL Wp Wq k r k D.z D.z' D.π D.π' _ _ D.z_mem D.z'_mem hD hT.2.1 hT.2.2.1 J hF g (hg0 g hg) Bs hBs w v,
      hT.2.2.2.2.2 Bs hBs w (J g v)]
    rfl
  · refine ContinuousLinearMap.ext fun v => ?_
    rw [hR Wp Wq k r k D.z D.z' D.π D.π' _ _ D.z_mem D.z'_mem hD hT'.2.1 hT'.2.2.1 J hF g (hg0 g hg) Bs hBs w v,
      hT'.2.2.2.2.2 Bs hBs w v, map_smul]
    rfl

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

def DominatedL2TruncationBound : Prop :=
  ∀ Cb C₁ : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (N : ℕ),
    NFHyp Cb Cc p f A₀ p₀ χ N → ∀ Th : B.DiffOp P.k P.r Wp Wq, NFOpOK C₁ p N Th →
      ∃ h : (Fin (P.r + 1) → ℂ) → ℝ, Integrable h ∧ ∀ n : ℕ, ∀ᵐ c : Fin (P.r + 1) → ℂ,
        ‖TBB.Gp p (TBB.bigPt P.r c)‖ ^ (2 * p₀ - N) *
          TBB.Ew p (fun _ => 1) (B.opApply Th (fun g => cutN P.k P.r n g • f g)) (P.r + 1) [] (TBB.bigPt P.r c) ≤ h c

section cutn

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem cutN_ckOn {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : B.Mat k r → E}
    (hf : B.CkOn (⊤ : ℕ∞) (B.GV k r) f) (n : ℕ) :
    B.CkOn (⊤ : ℕ∞) (B.GV k r) (fun g => cutN k r n g • f g) := by
  have hN : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => Complex.normSq z) := by
    simp_rw [Complex.normSq_apply]
    exact (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cutN k r n) := by
    unfold cutN
    refine Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp ?_)
    refine ContDiff.div_const (contDiff_const.sub ?_) _
    refine ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_
    exact hN.comp ((contDiff_apply_apply (𝕜 := ℝ) i j).comp (contDiff_const_smul _))
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hf', hff⟩ := hf g₀ hg₀
  refine ⟨U, fun g => cutN k r n g • f' g, hU, hgU, hc.contDiffOn.smul hf', fun g hg hgv => ?_⟩
  show cutN k r n g • f g = cutN k r n g • f' g
  rw [hff g hg hgv]

end cutn

end

end Formalism.FourierDecayAlt.P.CutBP
end

section

namespace Formalism.FourierDecayAlt.P.CutBP.TDM

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

def TypeNormMeas : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (Y : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A : ℝ), JF.TransportedAlt P.k P.r A 0 → B.InCC A 0 Y → ∀ ρ : M.Ty P,
      AEStronglyMeasurable (fun c : Fin (P.r + 1) → ℂ =>
        ‖B.hsVec ((p.TP.E ρ).comp (p.V Y (TBB.bigPt P.r c)))‖) volume

def VecVGPos : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (Y Y' : B.Mat P.k P.r → (Wq →L[ℂ] Wp)),
    (∀ g ∈ B.GV P.k P.r, 0 < Gf P.k P.r p.T.base.z p.T.base.z' g → Y g = Y' g) → ∀ a : C.LPt, p.V Y a = p.V Y' a

def DopCC : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (X : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (Cb : ℝ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base X → KB.CutWord P p.l0 w →
    ∀ e : Wd.Ix (Fin w.length), ∃ Y : B.Mat P.k P.r → (Wq →L[ℂ] Wp),
      (∀ g ∈ B.GV P.k P.r, 0 < Gf P.k P.r p.T.base.z p.T.base.z' g → Y g = p.Θ.Θ w e X g) ∧
        ∀ A : ℝ, B.InCC A 0 Y

def ScalarMeas : Prop :=
  ∀ (k r : ℕ) (TT : ℝ), Measurable (fun c : Fin (r + 1) → ℂ => TBB.nPt k r TT (TBB.bigPt r c)) ∧
    Measurable (fun c : Fin (r + 1) → ℂ => Top.wPt TT r (TBB.bigPt r c))

def EmptyMeas : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (X : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), KB.CptCoef p.T.base X → AEStronglyMeasurable (topD p X []) volume

theorem ae_all_ne (r : ℕ) : ∀ᵐ c : Fin (r + 1) → ℂ, ∀ i, c i ≠ 0 := by
  rw [ae_all_iff]
  intro i
  have h : volume ((fun c : Fin (r + 1) → ℂ => c i) ⁻¹' {0}) = 0 := by
    rw [volume_pi]
    exact Measure.pi_eval_preimage_null _ (measure_singleton 0)
  have e : {a : Fin (r + 1) → ℂ | ¬a i ≠ 0} = (fun c : Fin (r + 1) → ℂ => c i) ⁻¹' {0} := by
    ext a; simp
  exact ae_iff.2 (by rw [e]; exact h)

theorem topDMeasCpt_of_parts (h1 : TypeNormMeas) (h2 : VecVGPos) (h3 : DopCC) (h4 : ScalarMeas) (h5 : EmptyMeas) :
    TopDMeasCpt := by
  intro Wp Wq _ _ _ _ _ _ P p X w Cb hD hX hw
  by_cases hw0 : w = []
  · subst hw0; exact h5 Wp Wq P p X hX
  choose Y hYe hYc using h3 Wp Wq P p X w Cb hD hX hw
  set TT : ℝ := Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' with hTT
  set A : ℝ := 9 * ((P.r : ℝ) + 1) * (((2 * P.r + P.k + 1 : ℕ) : ℝ) ^ 2 + 1) with hA
  have hThr : JF.TransportedAlt P.k P.r A 0 := by
    unfold JF.TransportedAlt
    have hr : (0 : ℝ) < 9 * ((P.r : ℝ) + 1) := by positivity
    rw [Nat.cast_zero, mul_zero, sub_zero, lt_div_iff₀ hr, hA]
    nlinarith
  have hV : ∀ e a, p.V (p.Θ.Θ w e X) a = p.V (Y e) a := fun e a =>
    h2 Wp Wq P p _ _ (fun g hg hG => (hYe e g hg hG).symm) a
  obtain ⟨hn, hW⟩ := h4 P.k P.r TT
  set g : (Fin (P.r + 1) → ℂ) → ℝ := fun c =>
    ((((Real.sqrt (TBB.nPt P.k P.r TT (TBB.bigPt P.r c)) * Real.sqrt (TBB.nPt P.k P.r TT (TBB.bigPt P.r c)) /
        TBB.normC (fun _ => 1) w : ℝ) : ℂ) *
      ∑ e : Wd.Ix (Fin w.length), ∑ ρ : M.Ty P,
        ((Top.dH P p.l0 TT w (TBB.bigPt P.r c) e ρ * Top.dH P p.l0 TT w (TBB.bigPt P.r c) e ρ : ℝ) : ℂ) *
          (((‖B.hsVec ((p.TP.E ρ).comp (p.V (Y e) (TBB.bigPt P.r c)))‖ ^ 2 : ℝ)) : ℂ))).re with hg
  have hgm : AEStronglyMeasurable g volume := by
    have hdH : ∀ e ρ, Measurable (fun c : Fin (P.r + 1) → ℂ => Top.dH P p.l0 TT w (TBB.bigPt P.r c) e ρ) := by
      intro e ρ
      unfold Top.dH
      exact ((hW.pow_const _).mul_const _).sqrt
    have hterm : ∀ e ρ, AEStronglyMeasurable (fun c : Fin (P.r + 1) → ℂ =>
        ((Top.dH P p.l0 TT w (TBB.bigPt P.r c) e ρ * Top.dH P p.l0 TT w (TBB.bigPt P.r c) e ρ : ℝ) : ℂ) *
          (((‖B.hsVec ((p.TP.E ρ).comp (p.V (Y e) (TBB.bigPt P.r c)))‖ ^ 2 : ℝ)) : ℂ)) volume := by
      intro e ρ
      have h1' : AEStronglyMeasurable (fun c : Fin (P.r + 1) → ℂ =>
          ‖B.hsVec ((p.TP.E ρ).comp (p.V (Y e) (TBB.bigPt P.r c)))‖ ^ 2) volume :=
        (h1 Wp Wq P p (Y e) A hThr (hYc e A) ρ).pow 2
      have h2' : AEStronglyMeasurable (fun c : Fin (P.r + 1) → ℂ =>
          (((‖B.hsVec ((p.TP.E ρ).comp (p.V (Y e) (TBB.bigPt P.r c)))‖ ^ 2 : ℝ)) : ℂ)) volume :=
        Complex.continuous_ofReal.comp_aestronglyMeasurable h1'
      have h3' : AEStronglyMeasurable (fun c : Fin (P.r + 1) → ℂ =>
          ((Top.dH P p.l0 TT w (TBB.bigPt P.r c) e ρ * Top.dH P p.l0 TT w (TBB.bigPt P.r c) e ρ : ℝ) : ℂ)) volume :=
        (Complex.measurable_ofReal.comp ((hdH e ρ).mul (hdH e ρ))).aestronglyMeasurable
      exact h3'.mul h2'
    have hsum : AEStronglyMeasurable (fun c : Fin (P.r + 1) → ℂ => ∑ e : Wd.Ix (Fin w.length), ∑ ρ : M.Ty P,
        ((Top.dH P p.l0 TT w (TBB.bigPt P.r c) e ρ * Top.dH P p.l0 TT w (TBB.bigPt P.r c) e ρ : ℝ) : ℂ) *
          (((‖B.hsVec ((p.TP.E ρ).comp (p.V (Y e) (TBB.bigPt P.r c)))‖ ^ 2 : ℝ)) : ℂ)) volume :=
      Finset.aestronglyMeasurable_fun_sum _ fun e _ => Finset.aestronglyMeasurable_fun_sum _ fun ρ _ => hterm e ρ
    have hpre : AEStronglyMeasurable (fun c : Fin (P.r + 1) → ℂ =>
        (((Real.sqrt (TBB.nPt P.k P.r TT (TBB.bigPt P.r c)) * Real.sqrt (TBB.nPt P.k P.r TT (TBB.bigPt P.r c)) /
          TBB.normC (fun _ => 1) w : ℝ) : ℂ))) volume :=
      (Complex.measurable_ofReal.comp (((hn.sqrt.mul hn.sqrt).div_const _))).aestronglyMeasurable
    exact Complex.continuous_re.comp_aestronglyMeasurable (hpre.mul hsum)
  refine hgm.congr ?_
  filter_upwards [ae_all_ne P.r] with c hc
  have hl : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) := Formalism.FourierDecayAlt.P.PBJ.Dens.isLocPt_bigPt c hc
  show g c = topD p X w c
  unfold topD TBB.Ew TBB.NP KB.Pl.RR D.RRplace
  rw [dite_eq_left ⟨hl, hl⟩, dite_eq_right (by omega), if_pos rfl, if_neg hw0]
  unfold Top.topOf
  simp only [hg]
  congr 3
  funext e
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [Formalism.FourierDecayAlt.P.TBBx2.Tri.hsInner_self]
  show _ = _ * (((‖B.hsVec ((p.TP.E ρ).comp (p.V (p.Θ.Θ w e X) (TBB.bigPt P.r c)))‖ ^ 2 : ℝ)) : ℂ)
  rw [hV e]

end

end Formalism.FourierDecayAlt.P.CutBP.TDM
end

section

open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem psi_cont_of {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) :
    Continuous (fun g : B.Mat k r => psi k r z c g) := by
  have hl : Continuous fun g : B.Mat k r => ell k r z g := Formalism.FourierDecayAlt.P.B7.continuous_ell (k := k) (r := r) z
  unfold psi
  exact Complex.continuous_exp.comp (continuous_const.mul
    (Complex.continuous_ofReal.comp (Complex.continuous_re.comp (continuous_const.mul hl))))

theorem krI_aesm {k p ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (B0 : B.RealPlaceData k (p + ρ) Wp Wq) (H : B.Mat k (p + ρ) → (Wq →L[ℂ] Wp))
    (hHc : ContinuousOn H {x | x ∈ B.GV k (p + ρ) ∧ U.DjU k p ρ x ≠ 0}) (y₀ : B.Mat k (p + ρ))
    (hy₀ : y₀ ∈ B.GV k (p + ρ)) (hD : U.DjU k p ρ y₀ ≠ 0) :
    AEStronglyMeasurable (LeftFubiniLemmas.KrI B0 H y₀) (B0.μW'.prod B0.μN) := by
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite B0.haarW'
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite B0.haarN
  set S := {ξ : Mt k (p + ρ) × Mt k (p + ρ) | Formalism.FourierDecayAlt.P.PBG.InR B0 ξ} with hS
  have hcG := Formalism.FourierDecayAlt.P.unitary_group_closed k (p + ρ)
  have hcW := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k (p + ρ) B0.z'
  have hmem : ∀ ξ ∈ S, y₀ * Matrix.of ξ.2 * Matrix.of ξ.1 ∈ {x | x ∈ B.GV k (p + ρ) ∧ U.DjU k p ρ x ≠ 0} := by
    intro ξ hξ
    refine ⟨hcG.mul_mem _ (hcG.mul_mem _ hy₀ _ hξ.2.1) _ hξ.1.1, ?_⟩
    show U.DjU k p ρ (y₀ * Matrix.of ξ.2 * Matrix.of ξ.1) ≠ 0
    rw [LeftFubiniLemmas.djU_mul_UW B0.z' _ _ hξ.1, LeftFubiniLemmas.djU_mul_N _ _ hξ.2]
    exact hD
  have hof1 : Continuous (fun ξ : Mt k (p + ρ) × Mt k (p + ρ) => (Matrix.of ξ.1 : B.Mat k (p + ρ))) :=
    continuous_fst
  have hof2 : Continuous (fun ξ : Mt k (p + ρ) × Mt k (p + ρ) => (Matrix.of ξ.2 : B.Mat k (p + ρ))) :=
    continuous_snd
  have hc1 : Continuous (fun ξ : Mt k (p + ρ) × Mt k (p + ρ) => y₀ * Matrix.of ξ.2 * Matrix.of ξ.1) :=
    (continuous_const.matrix_mul hof2).matrix_mul hof1
  have hH : ContinuousOn (fun ξ : Mt k (p + ρ) × Mt k (p + ρ) => H (y₀ * Matrix.of ξ.2 * Matrix.of ξ.1)) S :=
    hHc.comp hc1.continuousOn hmem
  have hinv : ContinuousOn (fun ξ : Mt k (p + ρ) × Mt k (p + ρ) => (Matrix.of ξ.1 : B.Mat k (p + ρ))⁻¹) S :=
    Formalism.FourierDecayAlt.P.PBG.inv_cont_GV.comp hof1.continuousOn (fun ξ hξ => hξ.1.1)
  have hπ : ContinuousOn (fun ξ : Mt k (p + ρ) × Mt k (p + ρ) => B0.π' (Matrix.of ξ.1 : B.Mat k (p + ρ))⁻¹) S :=
    B0.π'_cont.comp hinv (fun ξ hξ => hcW.inv_mem _ hξ.1)
  have hψ : Continuous (fun ξ : Mt k (p + ρ) × Mt k (p + ρ) => star (psi k (p + ρ) B0.z' cStd (Matrix.of ξ.2))) :=
    continuous_star.comp ((psi_cont_of B0.z' cStd).comp hof2)
  have hK : ContinuousOn (LeftFubiniLemmas.KrI B0 H y₀) S := hψ.continuousOn.smul (hH.clm_comp hπ)
  have hm := hK.aestronglyMeasurable (μ := B0.μW'.prod B0.μN) (Formalism.FourierDecayAlt.P.PBG.isClosed_InR B0).measurableSet
  rwa [Measure.restrict_eq_self_of_ae_mem (s := S) (Formalism.FourierDecayAlt.P.PBG.ae_inR B0)] at hm

end Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra
end
end

section

namespace Formalism.FourierDecayAlt.P.CutMP.ER

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants MeasureTheory
open scoped ComplexConjugate

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def CapAdjInt : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (s Y : ℂ) (μ : Measure (Mt k r)),
    B.IsHaarOn (B.GV k r) μ → ∀ φ ψ : B.Mat k r → (Wq →L[ℂ] Wp),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ → HasCompactSupport ψ →
    (∫ x : Mt k r, B.hsInner (φ (Matrix.of x)) (B.opAdj (capTh k r Wp Wq s Y) ψ (Matrix.of x)) ∂μ) =
      ∫ x : Mt k r, B.hsInner (φ (Matrix.of x)) (conj s • Q.CV k r (conj Y) ψ (Matrix.of x)) ∂μ

def CapAdjFromInt : Prop := CapAdjInt → CapAdj

end Formalism.FourierDecayAlt.P.CutMP.ER
end
