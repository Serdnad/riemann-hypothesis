module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle061
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellConjTransposeMulApply
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle057
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle004
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ComplexifiedDerivativeCommutator
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddSSn
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle084
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle029
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SplLen
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.PhiMulVec
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.Tactic.Lemma
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

open MeasureTheory Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section RdV

variable {k ρ : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def cur (X : Q.Mx k ρ) (y : Mt k ρ) (t : ℝ) : Mt k ρ :=
  Matrix.of.symm (Matrix.of y * NormedSpace.exp ((t : ℂ) • X))

theorem cur_zero (X : Q.Mx k ρ) (y : Mt k ρ) : cur X y 0 = y := by
  simp [cur, NormedSpace.exp_zero]

theorem cur_add (X : Q.Mx k ρ) (y : Mt k ρ) (s t : ℝ) : cur X (cur X y s) t = cur X y (s + t) := by
  have hc : Commute ((s : ℂ) • X) ((t : ℂ) • X) := ((Commute.refl X).smul_left _).smul_right _
  have e : NormedSpace.exp (((s + t : ℝ) : ℂ) • X) =
      NormedSpace.exp ((s : ℂ) • X) * NormedSpace.exp ((t : ℂ) • X) := by
    rw [← Matrix.exp_add_of_commute _ _ hc, Complex.ofReal_add, add_smul]
  unfold cur
  rw [Equiv.apply_symm_apply, e, Matrix.mul_assoc]

theorem cur_hasDerivAt0 (X : Q.Mx k ρ) (y : Mt k ρ) :
    HasDerivAt (cur X y) (Matrix.of.symm (Matrix.of y * X)) 0 :=
  Formalism.REAL.hasDerivAt_mul_exp_smul_zero (Matrix.of y) X

theorem cur_hasDerivAt (X : Q.Mx k ρ) (y : Mt k ρ) (s : ℝ) :
    HasDerivAt (cur X y) (Matrix.of.symm (Matrix.of (cur X y s) * X)) s := by
  have h0 := cur_hasDerivAt0 X (cur X y s)
  rw [← sub_self s] at h0
  have h1 := h0.comp_sub_const s s
  refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  show cur X y t = cur X (cur X y s) (t - s)
  rw [cur_add, add_sub_cancel]

def mulX (X : Q.Mx k ρ) : Mt k ρ →ₗ[ℝ] Mt k ρ where
  toFun y := Matrix.of.symm (Matrix.of y * X)
  map_add' a b := by
    show Matrix.of.symm ((Matrix.of a + Matrix.of b) * X) = _
    rw [Matrix.add_mul]; rfl
  map_smul' c a := by
    show Matrix.of.symm ((c • Matrix.of a) * X) = _
    rw [Matrix.smul_mul]; rfl

variable {Par : Type} [NormedAddCommGroup Par] [NormedSpace ℝ Par] [FiniteDimensional ℝ Par]

def dirL (X : Q.Mx k ρ) : Par × Mt k ρ →L[ℝ] Par × Mt k ρ :=
  (ContinuousLinearMap.inr ℝ Par (Mt k ρ)).comp
    ((LinearMap.toContinuousLinearMap (mulX X)).comp (ContinuousLinearMap.snd ℝ Par (Mt k ρ)))

theorem rdv_local {X : Q.Mx k ρ} (hX : Formalism.FourierDecayAlt.P.Qx3.LieLev (Fin.last ρ) X) {f : Par → Q.Mx k ρ → E}
    {U : Set (Par × Mt k ρ)} {F : Par × Mt k ρ → E} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (hfF : ∀ q ∈ U, Matrix.of q.2 ∈ Q.Glev k ρ (Fin.last ρ) → f q.1 (Matrix.of q.2) = F q)
    {q : Par × Mt k ρ} (hq : q ∈ U) (hqG : Matrix.of q.2 ∈ Q.Glev k ρ (Fin.last ρ)) :
    HasDerivAt (fun t : ℝ => f q.1 (Matrix.of (cur X q.2 t))) (fderiv ℝ F q (dirL X q)) 0 := by
  have hc := cur_hasDerivAt0 X q.2
  have hγ : HasDerivAt (fun t : ℝ => ((q.1, cur X q.2 t) : Par × Mt k ρ)) (dirL X q) 0 :=
    (hasDerivAt_const (0 : ℝ) q.1).prodMk hc
  have hγ0 : ((q.1, cur X q.2 0) : Par × Mt k ρ) = q := by rw [cur_zero]
  have hFd : DifferentiableAt ℝ F q := (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hq)
  have hcomp := hFd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0.symm
  refine hcomp.congr_of_eventuallyEq ?_
  have hmem : ∀ᶠ t : ℝ in 𝓝 0, ((q.1, cur X q.2 t) : Par × Mt k ρ) ∈ U :=
    hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hU.mem_nhds hq)
  filter_upwards [hmem] with t ht
  exact hfF _ ht (Formalism.FourierDecayAlt.P.Qx3.glev_mul hqG (hX t))

theorem parFam_contAt_comp {Y : Type} [TopologicalSpace Y] {U₀ : Set (Par × Mt k ρ)} {g : Par × Mt k ρ → E}
    (hg : PBI.ParFam k ρ U₀ g) {m : Y → Par × Mt k ρ} {y₀ : Y} (hm : ContinuousAt m y₀) (hU : m y₀ ∈ U₀)
    (hG : ∀ y, Matrix.of (m y).2 ∈ Q.Glev k ρ (Fin.last ρ)) : ContinuousAt (fun y => g (m y)) y₀ := by
  obtain ⟨U, F, hUo, hqU, hF, hgF⟩ := hg (m y₀) hU (hG y₀)
  have hcF : ContinuousAt F (m y₀) := hF.continuousOn.continuousAt (hUo.mem_nhds hqU)
  have h := ContinuousAt.comp (g := F) (f := m) (x := y₀) hcF hm
  refine h.congr ?_
  have hmem : ∀ᶠ y in 𝓝 y₀, m y ∈ U := hm.preimage_mem_nhds (hUo.mem_nhds hqU)
  filter_upwards [hmem] with y hy
  exact (hgF (m y) hy (hG y)).symm

theorem rdv_parFam {X : Q.Mx k ρ} (hX : Formalism.FourierDecayAlt.P.Qx3.LieLev (Fin.last ρ) X) {U₀ : Set (Par × Mt k ρ)}
    {f : Par → Q.Mx k ρ → E} (hf : PBI.ParFam k ρ U₀ (fun q => f q.1 (Matrix.of q.2))) :
    PBI.ParFam k ρ U₀ (fun q => RdV X (f q.1) (Matrix.of q.2)) := by
  intro q₀ hq₀ hG₀
  obtain ⟨U, F, hU, hqU, hF, hfF⟩ := hf q₀ hq₀ hG₀
  refine ⟨U, fun q => fderiv ℝ F q (dirL X q), hU, hqU, ?_, fun q hq hqG => ?_⟩
  · exact (hF.fderiv_of_isOpen (m := ∞) hU Formalism.REAL.withTop_enat_infty_add_one_le_infty).clm_apply
      (ContinuousLinearMap.contDiff (n := ∞) (dirL (Par := Par) (k := k) (ρ := ρ) X)).contDiffOn
  · exact (rdv_local hX hU hF hfF hq hqG).deriv

theorem hasDerivAt_right_derivative_curve {X : Q.Mx k ρ} (hX : Formalism.FourierDecayAlt.P.Qx3.LieLev (Fin.last ρ) X) {U₀ : Set (Par × Mt k ρ)}
    {f : Par → Q.Mx k ρ → E} (hf : PBI.ParFam k ρ U₀ (fun q => f q.1 (Matrix.of q.2))) (Z : Par) (y : Mt k ρ)
    (s : ℝ) (hq : (Z, cur X y s) ∈ U₀) (hG : Matrix.of (cur X y s) ∈ Q.Glev k ρ (Fin.last ρ)) :
    HasDerivAt (fun t : ℝ => f Z (Matrix.of (cur X y t))) (RdV X (f Z) (Matrix.of (cur X y s))) s := by
  obtain ⟨U, F, hU, hqU, hF, hfF⟩ := hf _ hq hG
  have h0 := rdv_local hX hU hF hfF hqU hG
  have h1 : HasDerivAt (fun t : ℝ => f Z (Matrix.of (cur X (cur X y s) t)))
      (RdV X (f Z) (Matrix.of (cur X y s))) 0 := h0.differentiableAt.hasDerivAt
  rw [← sub_self s] at h1
  have h2 := h1.comp_sub_const s s
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  show f Z (Matrix.of (cur X y t)) = f Z (Matrix.of (cur X (cur X y s) (t - s)))
  rw [cur_add, add_sub_cancel]

end RdV

theorem parOK_rdV {k ρ : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {X : Q.Mx k ρ}
    (hX : Formalism.FourierDecayAlt.P.Qx3.LieLev (Fin.last ρ) X) : ParOK k ρ (E := E) (RdV X) := by
  intro Par _ _ _ _ _ U₀ hU₀ f hf
  have hD := rdv_parFam hX hf
  refine ⟨hD, fun q hq hG W hW hqW hz => ?_, fun ν _ Kp hKp hν fi y V hV hyV hyG hKV hi => ?_⟩
  · show deriv (fun t : ℝ => f q.1 (Matrix.of (cur X q.2 t))) 0 = 0
    have hγ : ContinuousAt (fun t : ℝ => ((q.1, cur X q.2 t) : Par × Mt k ρ)) 0 :=
      continuousAt_const.prodMk (cur_hasDerivAt0 X q.2).continuousAt
    have hγ0 : ((q.1, cur X q.2 0) : Par × Mt k ρ) = q := by rw [cur_zero]
    have hmem : ∀ᶠ t : ℝ in 𝓝 0, ((q.1, cur X q.2 t) : Par × Mt k ρ) ∈ W :=
      hγ.preimage_mem_nhds (by rw [hγ0]; exact hW.mem_nhds hqW)
    have hev : (fun t : ℝ => f q.1 (Matrix.of (cur X q.2 t))) =ᶠ[𝓝 0] (fun _ => (0 : E)) := by
      filter_upwards [hmem] with t ht
      exact hz _ ht (Formalism.FourierDecayAlt.P.Qx3.glev_mul hG (hX t))
    rw [hev.deriv_eq, deriv_const]
  · have hGt : ∀ t : ℝ, Matrix.of (cur X y t) ∈ Q.Glev k ρ (Fin.last ρ) := fun t =>
      Formalism.FourierDecayAlt.P.Qx3.glev_mul hyG (hX t)
    have hpre : cur X y ⁻¹' V ∈ 𝓝 (0 : ℝ) :=
      (cur_hasDerivAt0 X y).continuousAt.preimage_mem_nhds (by rw [cur_zero]; exact hV.mem_nhds hyV)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpre
    have hδ : 0 < ε / 2 := half_pos hε
    have hcb : Metric.closedBall (0 : ℝ) (ε / 2) ⊆ cur X y ⁻¹' V := fun t ht =>
      hball (Metric.closedBall_subset_ball (half_lt_self hε) ht)
    have hUt : ∀ t ∈ Metric.closedBall (0 : ℝ) (ε / 2), ∀ Z ∈ Kp, (Z, cur X y t) ∈ U₀ :=
      fun t ht Z hZ => hKV ⟨hZ, hcb ht⟩
    have hcont : ContinuousOn (fun p : Par × ℝ => RdV X (f p.1) (Matrix.of (cur X y p.2)))
        (Kp ×ˢ Metric.closedBall (0 : ℝ) (ε / 2)) := by
      intro p hp
      have hm : ContinuousAt (fun p : Par × ℝ => ((p.1, cur X y p.2) : Par × Mt k ρ)) p :=
        continuous_fst.continuousAt.prodMk
          (ContinuousAt.comp (g := cur X y) (f := Prod.snd) (x := p) (cur_hasDerivAt X y p.2).continuousAt
            continuous_snd.continuousAt)
      exact (parFam_contAt_comp (g := fun q => RdV X (f q.1) (Matrix.of q.2)) hD hm (hUt p.2 hp.2 p.1 hp.1)
        (fun p => hGt p.2)).continuousWithinAt
    obtain ⟨C, hC⟩ := (hKp.prod (isCompact_closedBall (0 : ℝ) (ε / 2))).exists_bound_of_continuousOn hcont
    have hae : ∀ᵐ Z ∂ν, Z ∈ Kp := by
      rw [ae_iff]
      simpa [Set.compl_def] using hν
    have hb : Metric.ball (0 : ℝ) (ε / 2) ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds 0 hδ
    have hin : ∀ t ∈ Metric.ball (0 : ℝ) (ε / 2), t ∈ Metric.closedBall (0 : ℝ) (ε / 2) :=
      fun t ht => Metric.ball_subset_closedBall ht
    have hF_int : ∀ t ∈ Metric.closedBall (0 : ℝ) (ε / 2),
        Integrable (fun Z => f Z (Matrix.of (cur X y t))) ν := fun t ht =>
      parFam_integrable (f := fun q => f q.1 (Matrix.of q.2)) hf hKp hν (hGt t) (fun Z hZ => hUt t ht Z hZ)
    have h0c : (0 : ℝ) ∈ Metric.closedBall (0 : ℝ) (ε / 2) := Metric.mem_closedBall_self hδ.le
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν)
      (F := fun t Z => f Z (Matrix.of (cur X y t)))
      (F' := fun t Z => RdV X (f Z) (Matrix.of (cur X y t))) (x₀ := 0) (bound := fun _ => C) hb
      (by
        filter_upwards [hb] with t ht
        exact (hF_int t (hin t ht)).aestronglyMeasurable)
      (hF_int 0 h0c)
      ((parFam_integrable (f := fun q => RdV X (f q.1) (Matrix.of q.2)) hD hKp hν (hGt 0)
        (fun Z hZ => hUt 0 h0c Z hZ)).aestronglyMeasurable)
      (by
        filter_upwards [hae] with Z hZ
        intro t ht
        exact hC (Z, t) ⟨hZ, hin t ht⟩)
      (integrable_const C)
      (by
        filter_upwards [hae] with Z hZ
        intro t ht
        exact hasDerivAt_right_derivative_curve hX hf Z y t (hUt t (hin t ht) Z hZ) (hGt t))
    show deriv (fun t : ℝ => fi (Matrix.of (cur X y t))) 0 = ∫ Z, RdV X (f Z) (Matrix.of y) ∂ν
    have hev : (fun t : ℝ => fi (Matrix.of (cur X y t))) =ᶠ[𝓝 0]
        (fun t => ∫ Z, f Z (Matrix.of (cur X y t)) ∂ν) := by
      filter_upwards [hb] with t ht
      exact hi (cur X y t) (hcb (hin t ht)) (hGt t)
    rw [hev.deriv_eq, key.2.deriv, cur_zero]

end Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra
end
end

section

open Matrix Set
open scoped ComplexConjugate ContDiff Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

lemma gf_pd (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) :
    U.IsPolyDeg (2 * r + 2) (fun g : Mat k r => ((Gf k r z z' g : ℝ) : ℂ)) := by
  exact gram_function_polynomial k r z z'

section fac

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

lemma ubl_monoM (D : RealPlaceData k r Wp Wq) (L : Finset (Fin (r + 2))) (a b : Fin (r + 2) → ℕ) (c : ℕ)
    (hab : ∀ l, l ∉ L → l ≠ Fin.last (r + 1) → a l = 0 ∧ b l = 0) {S : Set (Mat k r)} (hSG : S ⊆ GV k r)
    {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hSD : ∀ g ∈ S, ∀ l, (l ∈ L ∨ l = Fin.last (r + 1)) → c₀ ≤ Complex.normSq (Dmin k r D.z D.z' g l))
    (hSGf : ∀ g ∈ S, c₀ ≤ Complex.normSq ((Gf k r D.z D.z' g : ℝ) : ℂ)) (n : ℕ) :
    UBL (C6.monoM D a b c) S n 0 (2 * r + 2) := by
  have hfac : ∀ l ∈ (Finset.univ : Finset (Fin (r + 2))),
      UBL (fun g => (Dmin k r D.z D.z' g l)⁻¹ ^ a l * (star (Dmin k r D.z D.z' g l))⁻¹ ^ b l)
        S n 0 (2 * r + 2) := by
    intro l _
    by_cases hl : l ∈ L ∨ l = Fin.last (r + 1)
    · have hl' : l.val ≤ 2 * r + 2 := by have := l.isLt; omega
      have h1 : UBL (fun g => (Dmin k r D.z D.z' g l)⁻¹ ^ a l) S n 0 (2 * r + 2) :=
        ubl_mono hSG (ubl_invpow (minor_polynomial_property k r D.z D.z' l) hSG hc₀
          (fun g hg => hSD g hg l hl) (a l) n) le_rfl hl'
      have h2 : UBL (fun g => (star (Dmin k r D.z D.z' g l))⁻¹ ^ b l) S n 0 (2 * r + 2) :=
        ubl_mono hSG (ubl_invpow (dmin_star_pd k r D.z D.z' l) hSG hc₀
          (fun g hg => by rw [Complex.star_def, Complex.normSq_conj]; exact hSD g hg l hl) (b l) n)
          le_rfl hl'
      exact ubl_mul hSG h1 h2
    · push_neg at hl
      obtain ⟨ha, hb⟩ := hab l hl.1 hl.2
      have e : (fun g => (Dmin k r D.z D.z' g l)⁻¹ ^ a l * (star (Dmin k r D.z D.z' g l))⁻¹ ^ b l) =
          fun _ => (1 : ℂ) := by
        funext g
        simp [ha, hb]
      rw [e]
      exact ubl_const 1 hSG n _
  have hP := ubl_prod hSG Finset.univ
    (fun l g => (Dmin k r D.z D.z' g l)⁻¹ ^ a l * (star (Dmin k r D.z D.z' g l))⁻¹ ^ b l) hfac
  have hG := ubl_invpow (gram_function_polynomial k r D.z D.z') hSG hc₀ hSGf c n
  exact ubl_mul hSG hP hG

private lemma rw_congr_on_open_of_eq_on_GV {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {V : Set (Mat k r)}
    (hV : IsOpen V) {f f' : Mat k r → F} (he : ∀ g ∈ GV k r, g ∈ V → f g = f' g) :
    ∀ (w : List (Mat k r)), (∀ X ∈ w, inLie k r X) → ∀ g ∈ GV k r, g ∈ V → Rw w f g = Rw w f' g := by
  intro w
  induction w with
  | nil => intro _ g hg hgV; exact he g hg hgV
  | cons X w ih =>
    intro hw g hg hgV
    have ih' := ih (fun Y hY => hw Y (List.mem_cons_of_mem _ hY))
    show Dx (false, X) (Rw w f) g = Dx (false, X) (Rw w f') g
    rw [Dx_eq, Dx_eq]
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [crv_ev (x := (false, X)) hV hgV] with t ht
    exact ih' _ (crv_mem (x := (false, X)) (hw X (by simp)) hg t) ht

private lemma dw_const_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] (c : ℂ) (f : Mat k r → F) :
    ∀ w : List (Bool × Mat k r), Dw w (fun g => c • f g) = fun g => c • Dw w f g := by
  intro w
  induction w with
  | nil => rfl
  | cons x w ih =>
    funext g
    show Dx x (Dw w (fun g => c • f g)) g = c • Dx x (Dw w f) g
    rw [ih, Dx_eq, Dx_eq]
    first
    | exact deriv_const_smul_field c (f := fun t => Dw w f (crv x g t))
    | exact deriv_const_smul' (f := fun t => Dw w f (crv x g t)) c
    | simp [deriv_const_smul']

lemma ubl_fib (D : RealPlaceData k r Wp Wq) (E : Mat k r → C6.EndH Wp Wq) (hE : C6.FibBound D E) {ε : ℝ} (hε : 0 < ε)
    {S : Set (Mat k r)} (hS : ∀ g ∈ S, g ∈ GV k r ∧ ε ≤ Gf k r D.z D.z' g) (v : List (Mat k r))
    (hv : ∀ X ∈ v, inLie k r X) (n : ℕ) :
    UBL (Rw v E) S n (3 * (r + 1) * v.length) (3 * (r + 1)) := by
  obtain ⟨hE1, hE2⟩ := hE
  have hSsub : S ⊆ GPos D := fun g hg => ⟨(hS g hg).1, lt_of_lt_of_le hε (hS g hg).2⟩
  choose Cf hCf using fun i => hE2 ε hε i
  refine ⟨⟨|(v.map nz).prod| * ∑ j ∈ Finset.range (n + v.length + 1), |Cf j|, by positivity, ?_⟩, ?_⟩
  · intro w hw g hg
    obtain ⟨u, v', hu, hv', hlen, rfl⟩ := hw
    have hgGV := (hS g hg).1
    have hgε := (hS g hg).2
    have hX : 0 ≤ gN g := by
      first
      | positivity
      | (unfold gN; positivity)
      | (simp only [gN]; positivity)
    rw [Rw_scale v E, dw_const_smul, norm_smul]
    have hsplit : Dw (wL u ++ wR v') (Rw (v.map nrm) E) g = dLR u (v' ++ v.map nrm) E g := by
      rw [dLR_eq, Dw_append, Dw_append, Dw_wR, Dw_wR]
      rw [show Rw (v' ++ v.map nrm) E = Rw v' (Rw (v.map nrm) E) by simp only [Rw, List.foldr_append]]
    rw [hsplit]
    have hU : C6.UnitWords k r u (v' ++ v.map nrm) (u.length + (v' ++ v.map nrm).length) := by
      refine ⟨hu, fun X hX => ?_, rfl⟩
      rcases List.mem_append.1 hX with h | h
      · exact hv' X h
      · obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 h
        exact nrm_unit (hv Y hY)
    have hb := hCf (u.length + (v' ++ v.map nrm).length) u (v' ++ v.map nrm) hU g hgGV hgε
    have hlenw : (wL u ++ wR v').length = u.length + v'.length := by simp [wL, wR]
    have hexp : 3 * (r + 1) * (u.length + (v' ++ v.map nrm).length) =
        3 * (r + 1) * v.length + 3 * (r + 1) * (wL u ++ wR v').length := by
      rw [hlenw, List.length_append, List.length_map]; ring
    rw [hexp] at hb
    have hX' : 0 ≤ gN g ^ (3 * (r + 1) * v.length + 3 * (r + 1) * (wL u ++ wR v').length) :=
      pow_nonneg hX _
    have hi : u.length + (v' ++ v.map nrm).length < n + v.length + 1 := by
      rw [List.length_append, List.length_map]; omega
    have hCi : Cf (u.length + (v' ++ v.map nrm).length) ≤
        ∑ j ∈ Finset.range (n + v.length + 1), |Cf j| :=
      (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |Cf j|)
        (fun j _ => abs_nonneg _) (Finset.mem_range.2 hi))
    have hnorm : ‖(((v.map nz).prod : ℝ) : ℂ)‖ = |(v.map nz).prod| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm]
    calc |(v.map nz).prod| * ‖dLR u (v' ++ v.map nrm) E g‖
        ≤ |(v.map nz).prod| * (Cf (u.length + (v' ++ v.map nrm).length) *
            gN g ^ (3 * (r + 1) * v.length + 3 * (r + 1) * (wL u ++ wR v').length)) :=
          mul_le_mul_of_nonneg_left hb (abs_nonneg _)
      _ ≤ |(v.map nz).prod| * ((∑ j ∈ Finset.range (n + v.length + 1), |Cf j|) *
            gN g ^ (3 * (r + 1) * v.length + 3 * (r + 1) * (wL u ++ wR v').length)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hCi hX') (abs_nonneg _)
      _ = _ := by ring
  · intro g₀ hg₀
    obtain ⟨f', hf', V, hV, hgV, he⟩ := lss_of_ckOn hE1 hSsub g₀ hg₀
    refine ⟨Rw v f', ?_, V, hV, hgV, fun g' hg' hg'V => rw_congr_on_open_of_eq_on_GV hV he v hv g' hg' hg'V⟩
    rw [← Dw_wR]
    exact cdw _ hf'

end fac

end Formalism.FourierDecayAlt.P.AdmissibleLieWords
end
end

section

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.AdmissibleLieWords
open scoped ComplexConjugate Matrix

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

def nuG (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) : Fin (2 * r + k + 1) → ℂ :=
  unitH k r (PI.UnitaryGroupMassFormula.GsFr.omW k r z z' g)

def nuG' (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) : Fin (2 * r + k + 1) → ℂ :=
  unitH k r (PI.UnitaryGroupMassFormula.GsFr.omW' k r z z' g)

def PpG (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) : B.Mat k r :=
  PI.UnitaryGroupMassFormula.GsFr.Pm k r z' - PI.UnitaryGroupMassFormula.GsFr.Rk k r (nuG' z z' g) (nuG' z z' g) * PI.UnitaryGroupMassFormula.GsFr.Pm k r z'

def ioG (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) : B.Mat k r :=
  PI.UnitaryGroupMassFormula.GsFr.Phi k r z z' g * PpG z z' g

def posG (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : Set (B.Mat k r) :=
  {g | g ∈ B.GV k r ∧ 0 < Gf k r z z' g}

def geG (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (ε : ℝ) : Set (B.Mat k r) :=
  {g | g ∈ B.GV k r ∧ ε ≤ Gf k r z z' g}

def GeomSmooth : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → C2.StdZ k r z → C2.StdZ k r z' →
    B.CkOn ⊤ (posG k r z z') (nuG z z') ∧ B.CkOn ⊤ (posG k r z z') (nuG' z z') ∧
      B.CkOn ⊤ (posG k r z z') (ioG z z')

def GeomEqvNu : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → C2.StdZ k r z → C2.StdZ k r z' →
    ∀ h ∈ UWset k r z, ∀ n ∈ Nset k r, ∀ h' ∈ UWset k r z', ∀ n' ∈ Nset k r, ∀ g ∈ posG k r z z',
      nuG z z' g = h *ᵥ nuG z z' (h⁻¹ * n⁻¹ * g * n' * h') ∧
        nuG' z z' g = h' *ᵥ nuG' z z' (h⁻¹ * n⁻¹ * g * n' * h')

def GeomEqvIo : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → C2.StdZ k r z → C2.StdZ k r z' →
    ∀ h ∈ UWset k r z, ∀ n ∈ Nset k r, ∀ h' ∈ UWset k r z', ∀ n' ∈ Nset k r, ∀ g ∈ posG k r z z',
      ioG z z' g = h * ioG z z' (h⁻¹ * n⁻¹ * g * n' * h') * h'⁻¹

def GeomAtGq : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), 1 ≤ k →
    C2.StdZ k r z → C2.StdZ k r z' → IsSection k r z z' μsec →
    ∀ (c : Fin r → ℂ) (ζ : ℂ), (∀ l, c l ≠ 0) → Tz k r z * Tz k r z' < Complex.normSq ζ →
      nuG z z' (bigCell k r c (μsec ζ)) = phD c • nu0 k r z z' μsec ζ ∧
        nuG' z z' (bigCell k r c (μsec ζ)) = conj (phD c) • nu0' k r z z' μsec ζ ∧
          ioG z z' (bigCell k r c (μsec ζ)) = io0 k r z z' μsec ζ

def GeomBd0 : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → C2.StdZ k r z → C2.StdZ k r z' →
    ∃ C : ℝ, ∀ g ∈ posG k r z z', ‖nuG z z' g‖ ≤ C ∧ ‖nuG' z z' g‖ ≤ C ∧ ‖ioG z z' g‖ ≤ C

def UBLInvSqrt : Prop :=
  ∀ (k r d : ℕ) (P : B.Mat k r → ℂ), U.IsPolyDeg d P → ∀ (S : Set (B.Mat k r)), S ⊆ B.GV k r →
    ∀ c : ℝ, 0 < c → (∀ g ∈ S, c ≤ (P g).re) → ∀ n : ℕ,
      UBL (fun g => (((Real.sqrt (P g).re)⁻¹ : ℝ) : ℂ)) S n 0 d

def GeomUBL : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → C2.StdZ k r z → C2.StdZ k r z' → ∀ ε : ℝ, 0 < ε →
    (∃ e γ : ℕ, e ≤ 4 * (r + 1) ∧ γ ≤ 2 * (r + 1) ∧ ∀ n, UBL (nuG z z') (geG k r z z' ε) n e γ) ∧
    (∃ e γ : ℕ, e ≤ 4 * (r + 1) ∧ γ ≤ 2 * (r + 1) ∧ ∀ n, UBL (nuG' z z') (geG k r z z' ε) n e γ) ∧
    (∃ e γ : ℕ, e ≤ 4 * (r + 1) ∧ γ ≤ 2 * (r + 1) ∧ ∀ n, UBL (ioG z z') (geG k r z z' ε) n e γ)

def GeomAssemble : Prop :=
  GeomSmooth → GeomEqvNu → GeomEqvIo → GeomAtGq → GeomBd0 → GeomUBL → SSnGeom

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom
end
