module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle193
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle194
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyZeroNear
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle083
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle086
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.MulVecBvecApply
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SigmaFiniteOfHaar
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwoByOneBlock
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ComplexifiedDerivativeCommutator
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Matrix Filter
open scoped ContDiff Topology

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

local instance rwcN {d n : ℕ} : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ →L[ℝ] (Fin d → ℝ)) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance rwcS {d n : ℕ} : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℂ →L[ℝ] (Fin d → ℝ)) :=
  ContinuousLinearMap.toNormedSpace

namespace RightChartMultiplication

variable {d : ℕ}

theorem vfD_contDiffOn {V : (Fin d → ℝ) → (Fin d → ℝ)} {u : (Fin d → ℝ) → ℂ} {O : Set (Fin d → ℝ)}
    (hO : IsOpen O) {m : ℕ} (hu : ContDiffOn ℝ ((m + 1 : ℕ) : WithTop ℕ∞) u O) (hV : ContDiffOn ℝ ∞ V O) :
    ContDiffOn ℝ (m : WithTop ℕ∞) (vfD V u) O := by
  have h1 : ContDiffOn ℝ (m : WithTop ℕ∞) (fun x => fderiv ℝ u x) O :=
    hu.fderiv_of_isOpen hO (by push_cast; exact le_rfl)
  exact h1.clm_apply (hV.of_le (by exact_mod_cast le_top))

theorem vfW_contDiffOn {O : Set (Fin d → ℝ)} (hO : IsOpen O) :
    ∀ (Vs : List ((Fin d → ℝ) → (Fin d → ℝ))) (n : ℕ) (u : (Fin d → ℝ) → ℂ),
      ContDiffOn ℝ (n : WithTop ℕ∞) u O → (∀ V ∈ Vs, ContDiffOn ℝ ∞ V O) → Vs.length ≤ n →
      ContDiffOn ℝ ((n - Vs.length : ℕ) : WithTop ℕ∞) (vfW Vs u) O
  | [], n, u, hu, _, _ => by simpa [vfW] using hu
  | V :: Vs, n, u, hu, hV, hl => by
      simp only [List.length_cons] at hl
      have ih := vfW_contDiffOn hO Vs n u hu (fun W hW => hV W (List.mem_cons_of_mem _ hW)) (by omega)
      have e : n - Vs.length = (n - (Vs.length + 1)) + 1 := by omega
      rw [e] at ih
      simp only [vfW, List.length_cons]
      exact vfD_contDiffOn hO ih (hV V (List.mem_cons_self ..))

theorem glev0 {k r : ℕ} {g : B.Mat k r} (hg : g ∈ B.GV k r) : g ∈ Q.Glev k r 0 :=
  ⟨hg, fun _ ha => absurd ha (Nat.not_lt_zero _)⟩

def mulLC {k r : ℕ} (X : B.Mat k r) : B.Mat k r →L[ℝ] B.Mat k r :=
  LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ X)

theorem lcurve_hasDerivAt {k r : ℕ} (X g : B.Mat k r) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) * g) (X * g) 0 := by
  have h1 := P.B5.curve_hasDerivAt (1 : B.Mat k r) X 0
  have h2 := (mulRightRealCLM g).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  simp only [Function.comp_def, mulRightCLM_apply, Matrix.one_mul, Complex.ofReal_zero, zero_smul,
    NormedSpace.exp_zero] at h2
  exact h2

theorem rcurve_hasDerivAt {k r : ℕ} (X g : B.Mat k r) :
    HasDerivAt (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) (g * X) 0 := by
  have h1 := P.B5.curve_hasDerivAt g X 0
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, Matrix.mul_one] at h1
  exact h1

theorem step {k r : ℕ} {O : Set (Fin d → ℝ)} {U : Set (B.Mat k r)} {κ : (Fin d → ℝ) → B.Mat k r}
    {Φ : B.Mat k r → (Fin d → ℝ)} (hC : IsChart k r d O U κ Φ) (f : B.Mat k r → ℂ) (h : (Fin d → ℝ) → ℂ)
    (hfh : ∀ y ∈ O, f (κ y) = h y) {x : Fin d → ℝ} (hx : x ∈ O) (hh : DifferentiableAt ℝ h x)
    (c : ℝ → B.Mat k r) (v : B.Mat k r) (hc : HasDerivAt c v 0) (hc0 : c 0 = κ x)
    (hcG : ∀ t, c t ∈ B.GV k r) :
    deriv (fun t => f (c t)) 0 = fderiv ℝ h x (fderiv ℝ Φ (κ x) v) := by
  obtain ⟨hO, hU, hκ, hΦ, hκO, hΦU⟩ := hC
  have hxU : κ x ∈ U := (hκO x hx).2.1
  have hΦd : DifferentiableAt ℝ Φ (κ x) :=
    (hΦ.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hxU)
  have hmem : ∀ᶠ t : ℝ in 𝓝 0, c t ∈ U :=
    hc.continuousAt.preimage_mem_nhds (by rw [hc0]; exact hU.mem_nhds hxU)
  have heq : (fun t => f (c t)) =ᶠ[𝓝 0] fun t => h (Φ (c t)) := by
    filter_upwards [hmem] with t ht
    obtain ⟨h1, h2⟩ := hΦU (c t) ht (hcG t)
    rw [← hfh _ h1, h2]
  rw [heq.deriv_eq]
  have hγ : HasDerivAt (fun t => Φ (c t)) (fderiv ℝ Φ (κ x) v) 0 := by
    have := hΦd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hc hc0.symm
    exact this
  have hγ0 : Φ (c 0) = x := by rw [hc0]; exact (hκO x hx).2.2
  exact (hh.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0.symm).deriv

end RightChartMultiplication

open RightChartMultiplication in
theorem right_chart_holds : RwChart := by
  intro k r z z' d O U κ Φ u hC hOm hu
  have hC' := hC
  obtain ⟨hO, hU, hκ, hΦ, hκO, hΦU⟩ := hC

  have h1 : ∀ n : ℕ, n ≤ 2 * r + k + 1 → ContDiffOn ℝ (n : WithTop ℕ∞) (fun x => u (κ x)) O := by
    intro n hn x hx
    obtain ⟨V, F, hVo, hxV, hF, hFu⟩ := hu (κ x) ⟨glev0 (hκO x hx).1, hOm x hx⟩
    have hxV' : κ x ∈ V := hxV
    have hev : ∀ᶠ y in 𝓝[O] x, κ y ∈ V := (hκ.continuousOn x hx) (hVo.mem_nhds hxV')
    have hFκ : ContDiffWithinAt ℝ (n : WithTop ℕ∞) (fun y => F (κ y)) O x :=
      ((hF.contDiffAt (hVo.mem_nhds hxV')).of_le (by exact_mod_cast hn)).comp_contDiffWithinAt x
        ((hκ x hx).of_le (by exact_mod_cast le_top))
    refine hFκ.congr_of_eventuallyEq ?_ (hFu _ hxV' (glev0 (hκO x hx).1))
    filter_upwards [hev, self_mem_nhdsWithin] with y hyV hyO
    exact hFu _ hyV (glev0 (hκO y hyO).1)

  have hDΦ : ContDiffOn ℝ ∞ (fun g => fderiv ℝ Φ g) U :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen hU).1 hΦ).2
  have hDΦκ : ContDiffOn ℝ ∞ (fun x => fderiv ℝ Φ (κ x)) O :=
    hDΦ.comp hκ (fun x hx => (hκO x hx).2.1)
  have hVR : ∀ X : B.Mat k r, ContDiffOn ℝ ∞ (VR κ Φ X) O := fun X =>
    hDΦκ.clm_apply ((mulRightRealCLM X).contDiff.comp_contDiffOn hκ)
  have hVL : ∀ X : B.Mat k r, ContDiffOn ℝ ∞ (VL κ Φ X) O := fun X =>
    hDΦκ.clm_apply ((mulLC X).contDiff.comp_contDiffOn hκ)
  refine ⟨h1 _ le_rfl, fun X => ⟨hVR X, hVL X⟩, ?_⟩

  have hdiff : ∀ (Vs : List ((Fin d → ℝ) → (Fin d → ℝ))), (∀ V ∈ Vs, ContDiffOn ℝ ∞ V O) →
      Vs.length + 1 ≤ 2 * r + k + 1 → ∀ x ∈ O, DifferentiableAt ℝ (vfW Vs fun y => u (κ y)) x := by
    intro Vs hVs hl x hx
    have hc := vfW_contDiffOn hO Vs (2 * r + k + 1) _ (h1 _ le_rfl) hVs (by omega)
    have hle : (1 : WithTop ℕ∞) ≤ ((2 * r + k + 1 - Vs.length : ℕ) : WithTop ℕ∞) := by
      exact_mod_cast (by omega : 1 ≤ 2 * r + k + 1 - Vs.length)
    exact ((hc.differentiableOn (by
      exact ne_of_gt (lt_of_lt_of_le (by norm_num) hle))).differentiableAt (hO.mem_nhds hx))
  intro Xs hXs hl
  induction Xs with
  | nil => intro x _; exact ⟨rfl, rfl⟩
  | cons X Xs ih =>
    have hX : B.inLie k r X := hXs X (List.mem_cons_self ..)
    have ih' := ih (fun Y hY => hXs Y (List.mem_cons_of_mem _ hY))
      (by simp only [List.length_cons] at hl; omega)
    simp only [List.length_cons] at hl
    intro x hx
    have hxG : κ x ∈ B.GV k r := (hκO x hx).1
    constructor
    · show RdV X (B.Rw Xs u) (κ x) = vfD (VR κ Φ X) (vfW (Xs.map (VR κ Φ)) fun y => u (κ y)) x
      unfold RdV vfD VR
      exact step hC' (B.Rw Xs u) _ (fun y hy => (ih' y hy).1) hx
        (hdiff _ (by simpa using fun Y _ => hVR Y) (by simpa using hl) x hx)
        (fun t : ℝ => κ x * NormedSpace.exp ((t : ℂ) • X)) (κ x * X) (rcurve_hasDerivAt X (κ x))
        (by simp [NormedSpace.exp_zero]) (fun t => P.B5.curve_mem hxG hX t)
    · show Q.LdV X (Xs.foldr Q.LdV u) (κ x) =
        vfD (VL κ Φ X) (vfW (Xs.map (VL κ Φ)) fun y => u (κ y)) x
      unfold Q.LdV vfD VL
      exact step hC' (Xs.foldr Q.LdV u) _ (fun y hy => (ih' y hy).2) hx
        (hdiff _ (by simpa using fun Y _ => hVL Y) (by simpa using hl) x hx)
        (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) * κ x) (X * κ x) (lcurve_hasDerivAt X (κ x))
        (by simp [NormedSpace.exp_zero]) (fun t => Formalism.FourierDecayAlt.P.TwoByOneBlock.UH_mul (P.B5.exp_mem hX t) hxG)

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section

namespace Formalism.FourierDecayAlt.P.CutBP.TDM

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section loc

variable {k r : ℕ} {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]

theorem dop_rdV_local {X : B.Mat k r} (hX : B.inLie k r X) {U : Set (B.Mat k r)} (hU : IsOpen U)
    {f f' : B.Mat k r → E₁} (he : ∀ x ∈ U, x ∈ B.GV k r → f x = f' x) {g : B.Mat k r} (hg : g ∈ U)
    (hgG : g ∈ B.GV k r) : Formalism.REAL.RdV X f g = Formalism.REAL.RdV X f' g := by
  show deriv (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) 0 =
    deriv (fun t : ℝ => f' (g * NormedSpace.exp ((t : ℂ) • X))) 0
  apply Filter.EventuallyEq.deriv_eq
  have hc : Continuous (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) :=
    (Formalism.FourierDecayAlt.P.B5.curve_contDiff g X).continuous
  have hev : ∀ᶠ t : ℝ in nhds (0 : ℝ), g * NormedSpace.exp (((t : ℝ) : ℂ) • X) ∈ U := by
    apply hc.continuousAt.preimage_mem_nhds
    show U ∈ nhds (g * NormedSpace.exp (((0 : ℝ) : ℂ) • X))
    rw [Formalism.FourierDecayAlt.P.B5.curve_zero]
    exact hU.mem_nhds hg
  filter_upwards [hev] with t ht
  exact he _ ht (Formalism.FourierDecayAlt.P.B5.curve_mem hgG hX t)

theorem dop_rw_local (w : List (B.Mat k r)) (hw : ∀ X ∈ w, B.inLie k r X) {U : Set (B.Mat k r)} (hU : IsOpen U)
    {f f' : B.Mat k r → E₁} (he : ∀ x ∈ U, x ∈ B.GV k r → f x = f' x) :
    ∀ x ∈ U, x ∈ B.GV k r → B.Rw w f x = B.Rw w f' x := by
  induction w with
  | nil => exact he
  | cons X w ih =>
    intro x hx hxG
    exact dop_rdV_local (hw X (by simp)) hU (ih (fun Y hY => hw Y (by simp [hY]))) hx hxG

theorem dop_rw_zero : ∀ v : List (B.Mat k r), B.Rw v (0 : B.Mat k r → E₁) = 0
  | [] => rfl
  | X :: v => by
    show Formalism.REAL.RdV X (B.Rw v 0) = 0
    rw [dop_rw_zero v]
    funext g
    simp [Formalism.REAL.RdV]

theorem dop_ckOn_ap {UU : Set (B.Mat k r)} {a : B.Mat k r → (E₁ →L[ℂ] E₂)} {Φ : B.Mat k r → E₁}
    (ha : B.CkOn ⊤ UU a) (hΦ : B.CkOn ⊤ UU Φ) : B.CkOn ⊤ UU (fun g => a g (Φ g)) := by
  intro g₀ hg₀
  obtain ⟨U, a', hU, hgU, hc, hff⟩ := ha g₀ hg₀
  obtain ⟨U₂, Φ', hU₂, hgU₂, hc₂, hff₂⟩ := hΦ g₀ hg₀
  refine ⟨U ∩ U₂, fun g => a' g (Φ' g), hU.inter hU₂, ⟨hgU, hgU₂⟩, ?_,
    fun g hg hgG => by simp only [hff g hg.1 hgG, hff₂ g hg.2 hgG]⟩
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun g => ContinuousLinearMap.restrictScalarsL ℂ E₁ E₂ ℝ ℝ (a' g)) (U ∩ U₂) :=
    (ContinuousLinearMap.restrictScalarsL ℂ E₁ E₂ ℝ ℝ).contDiff.comp_contDiffOn
      (hc.mono Set.inter_subset_left)
  exact h1.clm_apply (hc₂.mono Set.inter_subset_right)

theorem dop_ckOn_Rw {UU : Set (B.Mat k r)} {w : List (B.Mat k r)} (hw : ∀ X ∈ w, B.inLie k r X)
    {f : B.Mat k r → E₁} (hf : B.CkOn ⊤ UU f) : B.CkOn ⊤ UU (B.Rw w f) := by
  rw [← Formalism.FourierDecayAlt.P.BetaSesquilinearity.Dw_wR]
  apply Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_Dw (fun x hx => Formalism.FourierDecayAlt.P.BetaSesquilinearity.lie_LR (u := []) (by simp) hw x
    (by simpa [Formalism.FourierDecayAlt.P.BetaSesquilinearity.wL] using hx))
  have e : ((⊤ : ℕ∞) + ((Formalism.FourierDecayAlt.P.BetaSesquilinearity.wR w).length : ℕ∞)) = ⊤ := top_add _
  rw [e]; exact hf

end loc

section op

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem dop_ckOn_opApply {UU : Set (B.Mat k r)} {J : B.Mat k r → (Wq →L[ℂ] Wp)} (hJ : B.CkOn ⊤ UU J) :
    ∀ Θ : B.DiffOp k r Wp Wq, (∀ T ∈ Θ, B.CkOn ⊤ UU T.coef) → B.CkOn ⊤ UU (B.opApply Θ J)
  | [], _ => by
    have e : B.opApply ([] : B.DiffOp k r Wp Wq) J = fun _ => 0 := by funext g; simp [B.opApply]
    rw [e]; exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_zero
  | T :: Θ, h => by
    have e : B.opApply (T :: Θ) J = fun g => T.coef g (B.Rw T.word J g) + B.opApply Θ J g := by
      funext g; simp [B.opApply]
    rw [e]
    exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_add (dop_ckOn_ap (h T (by simp)) (dop_ckOn_Rw T.word_lie hJ))
      (dop_ckOn_opApply hJ Θ (fun T' hT' => h T' (by simp [hT'])))

theorem dop_opApply_zero (Θ : B.DiffOp k r Wp Wq) {O : Set (B.Mat k r)} (hO : IsOpen O)
    {J : B.Mat k r → (Wq →L[ℂ] Wp)} (hJ : ∀ g ∈ O, g ∈ B.GV k r → J g = 0) :
    ∀ g ∈ O, g ∈ B.GV k r → B.opApply Θ J g = 0 := by
  intro g hg hgG
  unfold B.opApply
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨T, _, rfl⟩ := List.mem_map.1 hx
  rw [dop_rw_local T.word T.word_lie hO (f' := 0) hJ g hg hgG, dop_rw_zero]
  simp

end op

theorem diff_operator_in_class_CC : DopCC := by
  intro Wp Wq _ _ _ _ _ _ P p X w Cb hD hX hw e
  obtain ⟨nf, fib, o, κ, Dop, hfib, hDD, -, -, hΘ⟩ := hD w hw e
  set Bs := p.T.base with hBs
  obtain ⟨hXs, ⟨R, hR⟩, ⟨ε, hε, hXε⟩⟩ := hX
  set O : Set (B.Mat P.k P.r) := {g | R < B.gN g} ∪ {g | Gf P.k P.r Bs.z Bs.z' g < ε} with hOdef
  have hO : IsOpen O := (isOpen_lt continuous_const Formalism.FourierDecayAlt.P.B6.gN_continuous).union
    (isOpen_lt (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.gf_cont _ _) continuous_const)
  have hX0 : ∀ g ∈ O, g ∈ B.GV P.k P.r → X g = 0 := by
    intro g hg hgG
    by_contra hne
    rcases hg with h | h
    · exact absurd (hR g hgG hne) (not_le.2 h)
    · exact absurd (hXε g hgG hne) (not_le.2 h)
  set Y : B.Mat P.k P.r → (Wq →L[ℂ] Wp) := B.opApply Dop X with hYdef
  have hY0 : ∀ g ∈ O, g ∈ B.GV P.k P.r → Y g = 0 := dop_opApply_zero Dop hO hX0
  have hYs : B.CkOn ⊤ (B.GV P.k P.r) Y := by
    intro g₀ hg₀
    by_cases hgO : g₀ ∈ O
    · exact ⟨O, 0, hO, hgO, contDiffOn_const, fun g hg hgG => hY0 g hg hgG⟩
    · have hG : ε ≤ Gf P.k P.r Bs.z Bs.z' g₀ := by
        by_contra h; exact hgO (Or.inr (not_le.1 h))
      have hdom : g₀ ∈ C6.domL Bs ∅ := ⟨hg₀, lt_of_lt_of_le hε hG, fun l hl => absurd hl (Finset.notMem_empty l)⟩
      have hXd : B.CkOn ⊤ (C6.domL Bs ∅) X := fun g hg => hXs g hg.1
      exact dop_ckOn_opApply hXd Dop (fun T hT => (hDD.1 T hT).1) g₀ hdom
  refine ⟨Y, fun g hg hG => ?_, fun A => ?_⟩
  · exact (hΘ X g ⟨hg, hG, fun l hl => absurd hl (Finset.notMem_empty l)⟩).symm
  ·
    set K : Set (B.Mat P.k P.r) := B.GV P.k P.r ∩ ({g | B.gN g ≤ R} ∩ {g | ε ≤ Gf P.k P.r Bs.z Bs.z' g}) with hKdef
    have hK : IsCompact K := (Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le P.k P.r R).of_isClosed_subset
      (Formalism.FourierDecayAlt.P.B5.GV_closed.inter ((isClosed_le Formalism.FourierDecayAlt.P.B6.gN_continuous continuous_const).inter
        (isClosed_le continuous_const (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.gf_cont _ _))))
      (fun g hg => hg.2.1)
    have hYc : ContinuousOn Y (B.GV P.k P.r) := Formalism.FourierDecayAlt.P.B5.ckOn_continuousOn hYs
    have hfc : ContinuousOn (fun g => B.gN g ^ A * ‖Y g‖) K := by
      refine ContinuousOn.mul ?_ ((hYc.mono Set.inter_subset_left).norm)
      exact (Formalism.FourierDecayAlt.P.B6.gN_continuous.continuousOn).rpow_const
        (fun g hg => Or.inl (ne_of_gt (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_pos hg.1)))
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hfc
    refine ⟨max C 0, ⟨?_, ?_⟩⟩
    · intro g₀ hg₀
      obtain ⟨U, f', hU, hgU, hc, he⟩ := hYs g₀ hg₀
      exact ⟨U, f', hU, hgU, hc.of_le (by exact_mod_cast le_top), he⟩
    · intro u v _ _ huv g hg
      have hu : u = [] := List.eq_nil_of_length_eq_zero (by omega)
      have hv : v = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hu; subst hv
      show B.gN g ^ A * ‖Y g‖ ≤ max C 0
      by_cases hgK : g ∈ K
      · have := hC g hgK
        rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (le_of_lt (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_pos hg)) _)
          (norm_nonneg _))] at this
        exact le_trans this (le_max_left _ _)
      · have hgO : g ∈ O := by
          by_contra hgO
          apply hgK
          refine ⟨hg, ?_, ?_⟩
          · show B.gN g ≤ R
            by_contra h; exact hgO (Or.inl (not_le.1 h))
          · show ε ≤ Gf P.k P.r Bs.z Bs.z' g
            by_contra h; exact hgO (Or.inr (not_le.1 h))
        rw [hY0 g hgO hg, norm_zero, mul_zero]
        exact le_max_right _ _

end

end Formalism.FourierDecayAlt.P.CutBP.TDM
end

section

namespace Formalism.FourierDecayAlt.P.CutBP.TDM

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

section orb

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem vv_choose_congr {α : Sort*} {P Q : α → Prop} (e : P = Q) (hP : ∃ x, P x) (hQ : ∃ x, Q x) :
    hP.choose = hQ.choose := by
  subst e; rfl

theorem orbJ_congr_gpos (Bs : B.RealPlaceData k r Wp Wq) {γ : B.Mat k r} (hγ : γ ∈ B.GV k r)
    (hpos : 0 < Gf k r Bs.z Bs.z' γ) (μR : Measure (Mt k r)) (Y Y' : B.Mat k r → (Wq →L[ℂ] Wp))
    (hYY : ∀ g ∈ B.GV k r, 0 < Gf k r Bs.z Bs.z' g → Y g = Y' g) :
    D.orbJ Bs γ μR Y = D.orbJ Bs γ μR Y' := by
  have hae : D.orbIntegrand Bs γ Y =ᵐ[Bs.μSS] D.orbIntegrand Bs γ Y' := by
    filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS Bs] with q hq
    have hG : 0 < Gf k r Bs.z Bs.z' (B.sgs q γ) := by
      have e : Gf k r Bs.z Bs.z' (B.sgs q γ) = Gf k r Bs.z Bs.z' γ := by
        unfold Gf
        rw [Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs Bs hq, Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs Bs hq]
      rw [e]; exact hpos
    unfold D.orbIntegrand B.rho
    rw [hYY _ (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.sgs_GV Bs hq hγ) hG]
  have hP : (fun θ => D.IsNormCut Bs γ μR θ ∧ Integrable (fun q => θ q • D.orbIntegrand Bs γ Y q) Bs.μSS) =
      (fun θ => D.IsNormCut Bs γ μR θ ∧ Integrable (fun q => θ q • D.orbIntegrand Bs γ Y' q) Bs.μSS) := by
    funext θ
    apply propext
    apply and_congr_right
    intro _
    exact integrable_congr (hae.mono fun q hq => by simp only [hq])
  unfold D.orbJ
  by_cases h : ∃ θ, D.IsNormCut Bs γ μR θ ∧ Integrable (fun q => θ q • D.orbIntegrand Bs γ Y q) Bs.μSS
  · have h2 : ∃ θ, D.IsNormCut Bs γ μR θ ∧ Integrable (fun q => θ q • D.orbIntegrand Bs γ Y' q) Bs.μSS := hP ▸ h
    rw [dite_eq_left h, dite_eq_left h2, vv_choose_congr hP h h2]
    apply integral_congr_ae
    filter_upwards [hae] with q hq
    rw [hq]
  · have h2 : ¬∃ θ, D.IsNormCut Bs γ μR θ ∧ Integrable (fun q => θ q • D.orbIntegrand Bs γ Y' q) Bs.μSS := hP ▸ h
    rw [dite_eq_right h, dite_eq_right h2]

end orb

theorem vector_positive_cone : VecVGPos := by
  intro Wp Wq _ _ _ _ _ _ P p Y Y' hYY a
  unfold KB.Pl.V D.vecV
  by_cases h : D.IsLocPt a (P.r + 1) ∧
      0 < D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r a
  · rw [dite_eq_left h, dite_eq_left h]
    by_cases h' : ∃ γ ∈ B.GV P.k P.r, Zhat P.k P.r p.T.base.z p.T.base.z' γ = D.ptMatN a (P.r + 1) ∧
        D.IsDFrame p.T.base p.ν' p.m₀ γ
    · rw [dite_eq_left h', dite_eq_left h']
      obtain ⟨hγ, hZ, -⟩ := h'.choose_spec
      have hpos : 0 < Gf P.k P.r p.T.base.z p.T.base.z' h'.choose := by
        rw [← Formalism.FourierDecayAlt.P.ptG_spec P.k P.r _ _ a _ h.1 hZ]; exact h.2
      exact orbJ_congr_gpos p.T.base hγ hpos _ Y Y' hYY
    · rw [dite_eq_right h', dite_eq_right h']
  · rw [dite_eq_right h, dite_eq_right h]

end

end Formalism.FourierDecayAlt.P.CutBP.TDM
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

theorem positive_domain_is_domain : IsDomOmPlus := fun _ _ _ _ hz hz' =>
  Formalism.FourierDecayAlt.P.JCx2.rma_isDom_omPlus hz hz'

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

theorem group_vector_space : GVGrp := by
  intro k r
  refine ⟨⟨⟨1 + 1, (1 / 2 : ℂ) • 1, ?_, ?_⟩, rfl⟩, fun g₀ hg₀ => ?_⟩
  · rw [Matrix.mul_smul, Matrix.mul_one, smul_add, ← add_smul]
    norm_num
  · rw [Matrix.smul_mul, Matrix.one_mul, smul_add, ← add_smul]
    norm_num
  · have hdet : IsUnit g₀.det := Formalism.FourierDecayAlt.P.PBG.isUnit_det_of_UH hg₀
    refine ⟨Matrix.nonsing_inv_mul g₀ hdet, fun h hh => ⟨Formalism.FourierDecayAlt.P.TwoByOneBlock.UH_mul hg₀ hh,
      Formalism.FourierDecayAlt.P.TwoByOneBlock.UH_mul (Formalism.FourierDecayAlt.P.PBM.GV_inv_mem g₀ hg₀) hh, ?_⟩⟩
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv g₀ hdet, Matrix.one_mul]

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end
