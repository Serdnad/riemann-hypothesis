module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle041
public import GroundTheory.GlobalFields.TateThesis.EulerFactorsFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle016
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle026
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle015
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle040
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle001
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle044
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AnalyticVectorExponentialSeries
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle045
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle043
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
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
import Mathlib.Topology.Sheaves.Init
import GroundTheory.AutomorphicForms.GL2.FiniteIdeleDecomp
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule

@[expose] public section

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.CompanionTheory.HeckeBridge GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar)
open Formalism.L2.Host (unif atFin unif_spec)


theorem _root_.GlobalTheory.T.hecke_gauss_sum_local_term : ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E) (hu : IsUnitary χ) (v : HeightOneSpectrum (𝓞 E)) (m : ℕ), m ≠ 0 → ExpAt χ v m → ∑ᶠ r : 𝓞 E ⧸ v.asIdeal ^ m, (toHecke χ hu).finiteTest v (algebraMap E (v.adicCompletion E) ((Quotient.out r : 𝓞 E) : E)) * psiAt v (((atFin v (unif v ^ (m + diffExp v)) : (v.adicCompletion E)ˣ) : v.adicCompletion E)⁻¹ * algebraMap E (v.adicCompletion E) ((Quotient.out r : 𝓞 E) : E)) = gaussSumAt χ v m (unif v ^ (m + diffExp v)) := by
  first | exact @GlobalTheory.CompanionTheory.HeckeBridge.GaussSum.finiteTest_sum_eq_gaussSumAt | exact GlobalTheory.CompanionTheory.HeckeBridge.GaussSum.finiteTest_sum_eq_gaussSumAt | (intros; apply GlobalTheory.CompanionTheory.HeckeBridge.GaussSum.finiteTest_sum_eq_gaussSumAt <;> assumption)
end

section

namespace GlobalTheory.CompanionTheory.Published

theorem bernsteinZelevinskyFiniteness : GlobalTheory.Published.BernsteinZelevinskyFiniteness :=
  fun k _ _ _ _ => ⟨GlobalTheory.T.irreducible_smooth_admissible_GL k, GlobalTheory.T.jacquet_module_finite_length k, GlobalTheory.T.parabolic_induction_finite_length k, GlobalTheory.T.parabolic_induction_contragredient k⟩

end GlobalTheory.CompanionTheory.Published
end

section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

theorem _root_.GlobalTheory.T.analytic_vector_exponential_series : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) (hc : ∀ v, ContinuousOn (fun g => π g v) G) {v : H} (hs : IsSmoothVec G π v) (hw : WordBound G π v), ∃ r : ℝ, 0 < r ∧ ∀ X ∈ HCSS.lieOf G, mnorm X < r → HasSum (fun m : ℕ => ((m.factorial : ℂ)⁻¹) • (dRep π X)^[m] v) (π (NormedSpace.exp X) v) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.hasSum_orbit_of_wordBound | exact GlobalTheory.CompanionTheory.Hypotheses₂.HCA.hasSum_orbit_of_wordBound | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.HCA.hasSum_orbit_of_wordBound <;> assumption)
end

section

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Bracket

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def rightMul (Y : Matrix (Fin n) (Fin n) ℂ) : (Fin n → Fin n → ℂ) →L[ℝ] (Fin n → Fin n → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => Matrix.of.symm (Matrix.of z * Y)
      map_add' := fun x y => by
        ext a b
        simp [Matrix.mul_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun r x => by
        ext a b
        simp [Matrix.mul_apply, Finset.mul_sum, mul_assoc] }

theorem rightMul_apply (Y : Matrix (Fin n) (Fin n) ℂ) (z : Fin n → Fin n → ℂ) :
    rightMul Y z = Matrix.of.symm (Matrix.of z * Y) := rfl

open scoped Matrix.Norms.Operator in
theorem hasDerivAt_entry (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => (NormedSpace.exp (t • X)) i j) (X i j) 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)
  exact L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h

theorem hasDerivAt_curve (z : Fin n → Fin n → ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => (Matrix.of.symm (Matrix.of z * NormedSpace.exp (t • X)) : Fin n → Fin n → ℂ))
      (rightMul X z) 0 := by
  rw [hasDerivAt_pi]
  intro a
  rw [hasDerivAt_pi]
  intro b
  simp only [rightMul_apply, Matrix.of_symm_apply, Matrix.mul_apply, Matrix.of_apply]
  exact HasDerivAt.fun_sum (fun c _ => (hasDerivAt_entry X c b).const_mul (z a c))

def one : Fin n → Fin n → ℂ := Matrix.of.symm (1 : Matrix (Fin n) (Fin n) ℂ)

theorem of_one : Matrix.of (one (n := n)) = 1 := by exact Matrix.of.apply_symm_apply _

section Smooth

variable {G : Set (Matrix (Fin n) (Fin n) ℂ)} {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {v : H}
  {F : (Fin n → Fin n → ℂ) → H}

theorem hasDerivAt_along (hG : IsLinRed G) (hF : ContDiff ℝ ∞ F)
    (hFv : ∀ z, Matrix.of z ∈ G → π (Matrix.of z) v = F z) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ HCSS.lieOf G) {z : Fin n → Fin n → ℂ} (hz : Matrix.of z ∈ G) :
    HasDerivAt (fun t : ℝ => π (Matrix.of z * NormedSpace.exp (t • X)) v)
      (fderiv ℝ F z (rightMul X z)) 0 := by
  have hd : HasFDerivAt F (fderiv ℝ F z) (Matrix.of.symm (Matrix.of z * NormedSpace.exp ((0 : ℝ) • X))) := by
    have : (Matrix.of.symm (Matrix.of z * NormedSpace.exp ((0 : ℝ) • X)) : Fin n → Fin n → ℂ) = z := by
      simp
    rw [this]
    exact (hF.differentiable (by simp) z).hasFDerivAt
  have h := hd.comp_hasDerivAt (0 : ℝ) (hasDerivAt_curve z X)
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  have hm : Matrix.of z * NormedSpace.exp (t • X) ∈ G := hG.mul_mem _ hz _ (hX t)
  have := hFv (Matrix.of.symm (Matrix.of z * NormedSpace.exp (t • X))) (by simpa only [Matrix.of.apply_symm_apply] using hm)
  simpa only [Matrix.of.apply_symm_apply, Function.comp_def] using this

theorem hasDerivAt_exp_along (hG : IsLinRed G) (hF : ContDiff ℝ ∞ F)
    (hFv : ∀ z, Matrix.of z ∈ G → π (Matrix.of z) v = F z) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ HCSS.lieOf G) :
    HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) v) (fderiv ℝ F one (rightMul X one)) 0 := by
  have h := hasDerivAt_along hG hF hFv hX (z := one) (by rw [of_one]; exact hG.one_mem)
  simpa [of_one] using h

theorem dRep_eq (hG : IsLinRed G) (hF : ContDiff ℝ ∞ F)
    (hFv : ∀ z, Matrix.of z ∈ G → π (Matrix.of z) v = F z) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ HCSS.lieOf G) : dRep π X v = fderiv ℝ F one (rightMul X one) :=
  (hasDerivAt_exp_along hG hF hFv hX).deriv

theorem rep_dRep (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) (hF : ContDiff ℝ ∞ F)
    (hFv : ∀ z, Matrix.of z ∈ G → π (Matrix.of z) v = F z) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ HCSS.lieOf G) {z : Fin n → Fin n → ℂ} (hz : Matrix.of z ∈ G) :
    π (Matrix.of z) (dRep π X v) = fderiv ℝ F z (rightMul X z) := by
  have h1 := hasDerivAt_exp_along hG hF hFv hX
  have h2 := ((π (Matrix.of z)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  have h3 := hasDerivAt_along hG hF hFv hX hz
  rw [dRep_eq hG hF hFv hX]
  refine HasDerivAt.unique ?_ h3
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  have := hrep.2 _ hz _ (hX t)
  simp [this]

theorem dRep_dRep (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) (hF : ContDiff ℝ ∞ F)
    (hFv : ∀ z, Matrix.of z ∈ G → π (Matrix.of z) v = F z) {X Y : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ HCSS.lieOf G) (hY : Y ∈ HCSS.lieOf G) :
    dRep π X (dRep π Y v) =
      fderiv ℝ (fderiv ℝ F) one (rightMul X one) (rightMul Y one) +
        fderiv ℝ F one (rightMul Y (rightMul X one)) := by
  have hF1 : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_cast)
  have hdF : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) one) one :=
    (hF1.differentiable (by simp) one).hasFDerivAt
  have hG1 := hdF.clm_apply (rightMul Y).hasFDerivAt
  have hc := hasDerivAt_curve (one (n := n)) X
  have h0 : (Matrix.of.symm (Matrix.of (one (n := n)) * NormedSpace.exp ((0 : ℝ) • X)) : Fin n → Fin n → ℂ) = one := by
    simp [one]
  have h := hG1.comp_hasDerivAt_of_eq (0 : ℝ) hc h0.symm
  have h' : HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) (dRep π Y v)) _ 0 :=
    h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => by
      have := rep_dRep hG hrep hF hFv hY (z := Matrix.of.symm (NormedSpace.exp (t • X)))
        (by simpa only [Matrix.of.apply_symm_apply] using hX t)
      simpa only [Matrix.of.apply_symm_apply, of_one, one_mul, Function.comp_def] using this)
  refine h'.deriv.trans ?_
  simp [add_comm]

end Smooth

theorem dRep_bracket {G : Set (Matrix (Fin n) (Fin n) ℂ)} {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {v : H} (hv : IsSmoothVec G π v)
    {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) (hY : Y ∈ HCSS.lieOf G) :
    dRep π (X * Y - Y * X) v = dRep π X (dRep π Y v) - dRep π Y (dRep π X v) := by
  obtain ⟨F, hF, hFv⟩ := hv
  have hZ : X * Y - Y * X ∈ HCSS.lieOf G := (GlobalTheory.T.lie_algebra_of_linear_group_closed hG).2.2.1 X Y hX hY
  have hsymm : IsSymmSndFDerivAt ℝ F one :=
    (hF.contDiffAt).isSymmSndFDerivAt (by
      simp only [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.2 le_top)
  rw [dRep_dRep hG hrep hF hFv hX hY, dRep_dRep hG hrep hF hFv hY hX, dRep_eq hG hF hFv hZ,
    hsymm.eq (rightMul X one) (rightMul Y one), add_sub_add_left_eq_sub, ← map_sub]
  congr 1
  simp only [rightMul_apply, Matrix.of.apply_symm_apply, of_one, one_mul]
  ext a b
  rfl

theorem smooth_bracket : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {v : H} (hv : IsSmoothVec G π v) {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) (hY : Y ∈ HCSS.lieOf G), dRep π (X * Y - Y * X) v = dRep π X (dRep π Y v) - dRep π Y (dRep π X v) :=
  fun hG hrep _ hv _ _ hX hY => dRep_bracket hG hrep hv hX hY

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Bracket

end
end

section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

theorem _root_.GlobalTheory.T.derived_action_additive : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {u v : H} (hu : IsSmoothVec G π u) (hv : IsSmoothVec G π v) {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) (hY : Y ∈ HCSS.lieOf G), dRep π (X + Y) v = dRep π X v + dRep π Y v ∧ dRep π X (u + v) = dRep π X u + dRep π X v ∧ ∀ c : ℂ, dRep π X (c • v) = c • dRep π X v := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.SmoothLin.dRep_linear | exact GlobalTheory.CompanionTheory.Hypotheses₂.HCA.SmoothLin.dRep_linear | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.HCA.SmoothLin.dRep_linear <;> assumption)
end

section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.WordExpand

variable {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem isSmoothVec_add {u v : H} (hu : IsSmoothVec G π u) (hv : IsSmoothVec G π v) :
    IsSmoothVec G π (u + v) := by
  obtain ⟨F, hF, hF'⟩ := hu
  obtain ⟨K, hK, hK'⟩ := hv
  exact ⟨fun z => F z + K z, hF.add hK, fun z hz => by rw [map_add (f := _), hF' z hz, hK' z hz]⟩

theorem isSmoothVec_smul (c : ℂ) {v : H} (hv : IsSmoothVec G π v) :
    IsSmoothVec G π (c • v) := by
  obtain ⟨F, hF, hF'⟩ := hv
  exact ⟨fun z => c • F z, hF.const_smul c, fun z hz => by rw [map_smul, hF' z hz]⟩

theorem isSmoothVec_zero : IsSmoothVec G π (0 : H) :=
  ⟨fun _ => 0, contDiff_const, fun z _ => map_zero _⟩

theorem isSmoothVec_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → H)
    (hf : ∀ i, IsSmoothVec G π (f i)) : IsSmoothVec G π (∑ i ∈ s, c i • f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isSmoothVec_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact isSmoothVec_add (isSmoothVec_smul _ (hf a)) ih

variable {d : ℕ} {b : Fin d → Matrix (Fin n) (Fin n) ℂ}

theorem word_smooth (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π)
    (hb : ∀ i, b i ∈ HCSS.lieOf G) (p : List (Fin d)) {w : H} (hw : IsSmoothVec G π w) :
    IsSmoothVec G π (p.foldr (fun i w => dRep π (b i) w) w) := by
  induction p with
  | nil => exact hw
  | cons i p ih => exact (hasDerivAt_dRep_and_isSmoothVec hG hrep ih (hb i)).2

theorem list_smooth (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π)
    (l : List (Matrix (Fin n) (Fin n) ℂ)) (hl : ∀ X ∈ l, X ∈ HCSS.lieOf G) {v : H}
    (hv : IsSmoothVec G π v) : IsSmoothVec G π (l.foldr (dRep π) v) := by
  induction l with
  | nil => exact hv
  | cons X l ih =>
    exact (hasDerivAt_dRep_and_isSmoothVec hG hrep
      (ih fun Y hY => hl Y (List.mem_cons_of_mem _ hY)) (hl X List.mem_cons_self)).2

theorem word_add (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π)
    (hb : ∀ i, b i ∈ HCSS.lieOf G) (p : List (Fin d)) {u v : H} (hu : IsSmoothVec G π u)
    (hv : IsSmoothVec G π v) :
    p.foldr (fun i w => dRep π (b i) w) (u + v) =
      p.foldr (fun i w => dRep π (b i) w) u + p.foldr (fun i w => dRep π (b i) w) v := by
  induction p with
  | nil => rfl
  | cons i p ih =>
    simp only [List.foldr_cons]
    rw [ih]
    exact (SmoothLin.dRep_linear hG hrep (word_smooth hG hrep hb p hu)
      (word_smooth hG hrep hb p hv) (hb i) (hb i)).2.1

theorem word_smul (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π)
    (hb : ∀ i, b i ∈ HCSS.lieOf G) (p : List (Fin d)) (c : ℂ) {v : H}
    (hv : IsSmoothVec G π v) :
    p.foldr (fun i w => dRep π (b i) w) (c • v) =
      c • p.foldr (fun i w => dRep π (b i) w) v := by
  induction p with
  | nil => rfl
  | cons i p ih =>
    simp only [List.foldr_cons]
    rw [ih]
    exact (SmoothLin.dRep_linear hG hrep (word_smooth hG hrep hb p hv)
      (word_smooth hG hrep hb p hv) (hb i) (hb i)).2.2 c

theorem word_sum (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π)
    (hb : ∀ i, b i ∈ HCSS.lieOf G) (p : List (Fin d)) {ι : Type} (s : Finset ι) (c : ι → ℂ)
    (f : ι → H) (hf : ∀ i, IsSmoothVec G π (f i)) :
    p.foldr (fun i w => dRep π (b i) w) (∑ j ∈ s, c j • f j) =
      ∑ j ∈ s, c j • p.foldr (fun i w => dRep π (b i) w) (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := word_smul hG hrep hb p (0 : ℂ) (isSmoothVec_zero (G := G) (π := π) (H := H))
    simpa using h
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      word_add hG hrep hb p (isSmoothVec_smul _ (hf a)) (isSmoothVec_sum s c f hf),
      word_smul hG hrep hb p _ (hf a), ih]

theorem mnorm_nonneg (X : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ mnorm X :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem prod_mnorm_nonneg (l : List (Matrix (Fin n) (Fin n) ℂ)) : 0 ≤ (l.map mnorm).prod := by
  induction l with
  | nil => simp
  | cons X l ih =>
    simp only [List.map_cons, List.prod_cons]
    exact mul_nonneg (mnorm_nonneg X) ih

theorem mixed_bound (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π)
    (hb : ∀ i, b i ∈ HCSS.lieOf G)
    (hsp : ∀ X ∈ HCSS.lieOf G, ∃ r : Fin d → ℝ, X = ∑ i, r i • b i)
    (D : ℝ) (hD0 : 0 ≤ D) (hD : ∀ r : Fin d → ℝ, ∑ i, |r i| ≤ D * mnorm (∑ i, r i • b i))
    (hexp : ∀ (r : Fin d → ℝ) (w : H), IsSmoothVec G π w →
      dRep π (∑ i, r i • b i) w = ∑ i, (r i : ℂ) • dRep π (b i) w)
    {v : H} (hv : IsSmoothVec G π v) (C : ℝ) (hC : 0 < C)
    (hbound : ∀ l : List (Fin d),
      ‖l.foldr (fun i w => dRep π (b i) w) v‖ ≤ C ^ (l.length + 1) * l.length.factorial)
    (l : List (Matrix (Fin n) (Fin n) ℂ)) (hl : ∀ X ∈ l, X ∈ HCSS.lieOf G) (p : List (Fin d)) :
    ‖p.foldr (fun i w => dRep π (b i) w) (l.foldr (dRep π) v)‖ ≤
      C ^ (p.length + l.length + 1) * (p.length + l.length).factorial * D ^ l.length *
        (l.map mnorm).prod := by
  induction l generalizing p with
  | nil => simpa using hbound p
  | cons X l ih =>
    have hl' : ∀ Y ∈ l, Y ∈ HCSS.lieOf G := fun Y hY => hl Y (List.mem_cons_of_mem _ hY)
    have hX : X ∈ HCSS.lieOf G := hl X List.mem_cons_self
    have hw : IsSmoothVec G π (l.foldr (dRep π) v) := list_smooth hG hrep l hl' hv
    obtain ⟨r, hr⟩ := hsp X hX
    have e1 : dRep π X (l.foldr (dRep π) v) =
        ∑ i, (r i : ℂ) • dRep π (b i) (l.foldr (dRep π) v) := by
      rw [hr]
      exact hexp r _ hw
    have hsm : ∀ i, IsSmoothVec G π (dRep π (b i) (l.foldr (dRep π) v)) := fun i =>
      (hasDerivAt_dRep_and_isSmoothVec hG hrep hw (hb i)).2
    have e2 : p.foldr (fun i w => dRep π (b i) w) (dRep π X (l.foldr (dRep π) v)) =
        ∑ i, (r i : ℂ) • (p ++ [i]).foldr (fun i w => dRep π (b i) w) (l.foldr (dRep π) v) := by
      rw [e1, word_sum hG hrep hb p _ _ _ hsm]
      simp [List.foldr_append]
    have hih : ∀ i, ‖(p ++ [i]).foldr (fun i w => dRep π (b i) w) (l.foldr (dRep π) v)‖ ≤
        C ^ (p.length + (l.length + 1) + 1) * (p.length + (l.length + 1)).factorial *
          D ^ l.length * (l.map mnorm).prod := by
      intro i
      have h := ih hl' (p ++ [i])
      rw [List.length_append, List.length_singleton,
        show p.length + 1 + l.length = p.length + (l.length + 1) by omega] at h
      exact h
    have hK : 0 ≤ C ^ (p.length + (l.length + 1) + 1) * (p.length + (l.length + 1)).factorial *
        D ^ l.length * (l.map mnorm).prod :=
      mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hC.le _) (Nat.cast_nonneg _))
        (pow_nonneg hD0 _)) (prod_mnorm_nonneg l)
    have hsum : ∑ i, |r i| ≤ D * mnorm X := by
      rw [hr]
      exact hD r
    show ‖p.foldr (fun i w => dRep π (b i) w) (dRep π X (l.foldr (dRep π) v))‖ ≤ _
    rw [e2]
    calc ‖∑ i, (r i : ℂ) • (p ++ [i]).foldr (fun i w => dRep π (b i) w) (l.foldr (dRep π) v)‖
        ≤ ∑ i, |r i| * (C ^ (p.length + (l.length + 1) + 1) *
            (p.length + (l.length + 1)).factorial * D ^ l.length * (l.map mnorm).prod) := by
          refine norm_sum_le_of_le _ fun i _ => ?_
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hih i) (abs_nonneg _)
      _ = (∑ i, |r i|) * (C ^ (p.length + (l.length + 1) + 1) *
            (p.length + (l.length + 1)).factorial * D ^ l.length * (l.map mnorm).prod) :=
          (Finset.sum_mul _ _ _).symm
      _ ≤ (D * mnorm X) * (C ^ (p.length + (l.length + 1) + 1) *
            (p.length + (l.length + 1)).factorial * D ^ l.length * (l.map mnorm).prod) :=
          mul_le_mul_of_nonneg_right hsum hK
      _ = _ := by
          simp only [List.length_cons, List.map_cons, List.prod_cons]
          ring

theorem wordBound_of_basis {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {d : ℕ}
    (b : Fin d → Matrix (Fin n) (Fin n) ℂ) (hb : ∀ i, b i ∈ HCSS.lieOf G)
    (hsp : ∀ X ∈ HCSS.lieOf G, ∃ r : Fin d → ℝ, X = ∑ i, r i • b i)
    (D : ℝ) (hD0 : 0 ≤ D) (hD : ∀ r : Fin d → ℝ, ∑ i, |r i| ≤ D * mnorm (∑ i, r i • b i))
    (hexp : ∀ (r : Fin d → ℝ) (w : H), IsSmoothVec G π w →
      dRep π (∑ i, r i • b i) w = ∑ i, (r i : ℂ) • dRep π (b i) w)
    {v : H} (hv : IsSmoothVec G π v) (C : ℝ) (hC : 0 < C)
    (hbound : ∀ l : List (Fin d),
      ‖l.foldr (fun i w => dRep π (b i) w) v‖ ≤ C ^ (l.length + 1) * l.length.factorial) :
    WordBound G π v := by
  have hD1 : (1 : ℝ) ≤ D + 1 := by linarith
  refine ⟨C * (D + 1), by positivity, fun l hl => ?_⟩
  have h := mixed_bound hG hrep hb hsp D hD0 hD hexp hv C hC hbound l hl []
  simp only [List.foldr_nil, List.length_nil, Nat.zero_add] at h
  refine h.trans ?_
  have hP := prod_mnorm_nonneg l
  have hpow : D ^ l.length ≤ (D + 1) ^ (l.length + 1) :=
    (pow_le_pow_left₀ hD0 (by linarith) _).trans (pow_le_pow_right₀ hD1 (Nat.le_succ _))
  have hCk : 0 ≤ C ^ (l.length + 1) := pow_nonneg hC.le _
  have hf : (0 : ℝ) ≤ l.length.factorial := Nat.cast_nonneg _
  rw [mul_pow]
  calc C ^ (l.length + 1) * l.length.factorial * D ^ l.length * (l.map mnorm).prod
      = (C ^ (l.length + 1) * l.length.factorial * (l.map mnorm).prod) * D ^ l.length := by ring
    _ ≤ (C ^ (l.length + 1) * l.length.factorial * (l.map mnorm).prod) *
          (D + 1) ^ (l.length + 1) :=
        mul_le_mul_of_nonneg_left hpow (mul_nonneg (mul_nonneg hCk hf) hP)
    _ = _ := by ring

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.WordExpand

end
end
