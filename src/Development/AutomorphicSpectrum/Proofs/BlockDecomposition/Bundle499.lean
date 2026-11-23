module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle224
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle442
import Formalism.SharpRestriction.GlobalSchurBounds.LocalCountingBounds
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.CalcSteps
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionalCalculusJointCurve
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle269
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle453
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle455
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle424
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.OnlyIsotropic
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle119
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle472
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle117
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SatakePowerNonvanishing
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.Bundle001
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.Bundle001
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle473
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle474
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
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle216
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulEqOfRangeLe
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.QuotVanish

@[expose] public section

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.WSum

variable {D : D7} {r : ℕ}

def rs (σ : (D.what₂.Tau → ℂ) →+ AE D) (s : ℝ) : AE D := σ fun _ => (s : ℂ)

theorem rs_add (σ : (D.what₂.Tau → ℂ) →+ AE D) (s t : ℝ) : rs σ (s + t) = rs σ s + rs σ t := by
  unfold rs
  rw [← map_add (f := _)]
  congr 1
  funext x
  simp

theorem rs_zero (σ : (D.what₂.Tau → ℂ) →+ AE D) : rs σ 0 = 0 := by
  unfold rs
  have : (fun _ : D.what₂.Tau => ((0 : ℝ) : ℂ)) = 0 := by funext; simp
  rw [this, map_zero]

theorem finPart_cA (z : AE D) :
    finPart D (cA D z) = sigR (Af D.host.F) D.sp.cm.sig (finPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x => rfl
  | add a b ha hb => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), ha, hb]

theorem cA_rs {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) (s : ℝ) :
    cA D (rs σ s) = rs σ s := by
  refine sub_eq_zero.1 (hσ.ext _ ?_ fun τ => ?_)
  · have h0 : finPart D (rs σ s) = 0 := hσ.fin _
    rw [RingHom.map_sub, finPart_cA, h0, map_zero, sub_zero]
  · have hcm := Formalism.MainNotions.UnusedSlot34.isCMExt_D D
    rw [RingHom.map_sub, RingHom.map_sub, GlobalTheory.PhaseReal.infPart_cA,
      GlobalTheory.Mem.VolExists.infEmb_sigR hcm (hσ.inf τ)]
    unfold rs
    rw [hσ.comp]
    simp

theorem continuous_rs {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) :
    Continuous (rs σ) :=
  hσ.cont.comp (continuous_pi fun _ => Complex.continuous_ofReal)

def path {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) (a : HermE D r) :
    ℝ →+ hermA D r where
  toFun s := ⟨rs σ s • a.1.map (incA D), by
    show adj (rs σ s • a.1.map (incA D)) = rs σ s • a.1.map (incA D)
    rw [adj_smul, cA_rs hσ]
    congr 1
    exact GlobalTheory.CompanionTheory.HermPoisson.rat_mem_hermA a⟩
  map_zero' := by
    apply Subtype.ext
    show rs σ 0 • a.1.map (incA D) = 0
    rw [rs_zero, zero_smul]
  map_add' s t := by
    apply Subtype.ext
    show rs σ (s + t) • a.1.map (incA D) = rs σ s • a.1.map (incA D) + rs σ t • a.1.map (incA D)
    rw [rs_add, add_smul]

def lam (θ : InfFam D) (α : D.host.F) (t : AE D) : ℝ :=
  -∑ τ, (θ τ (infPart D (incA D (algebraMap D.host.F D.host.E α) * t))).re

def multM (θ : InfFam D) (α : D.host.F) (V : HSp D) (a : HermE D r) (y : Mx D V.rank r) : ℝ :=
  lam θ α (Matrix.trace (HMul.hMul (a.1.map (incA D)) (inner V y y) : Mx D r r))

def pairF (θ : InfFam D) (α : D.host.F) (a β : HermE D r) : ℝ :=
  lam θ α (incA D (Matrix.trace (β.1 * a.1)))

end GlobalTheory.CompanionTheory.WSum
end
end

section

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty ENNReal

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.FcSmooth

variable {n : ℕ}

theorem isSec_comb (E : KMod n) (c : ℂ) {f f' : Mat n → E.V} (h : IsSec E f) (h' : IsSec E f') :
    IsSec E (fun y => c • f y + f' y) := by
  intro g hg k
  simp only [h g hg k, h' g hg k, map_add (f := _), map_smul]

section

variable [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)

theorem word_est (hAE : AlgEst) (hL : LgFacts) (hU : Unimod) (hR : RCalc) (hC : CalcSteps)
    (h : C₀(ℝ, ℂ)) (hh : ∀ m : ℕ, ∃ h' : C₀(ℝ, ℂ), ∀ y, h' y = (y : ℂ) ^ m * h y) :
    haveI := FiniteDimensional.complete ℂ E.V
    ∀ (Ω : Msob μ E.V →ₗ[ℂ] Msob μ E.V) (T : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ) (F : FCalc (Lp E.V 2 μ) (Msob μ E.V) Ω T),
      (∀ (f : Mat n → E.V) (hf : cls μ f ∈ Msob μ E.V), Sob μ f → (Ω ⟨cls μ f, hf⟩ : Lp E.V 2 μ) = cls μ (Om f)) →
      ∀ w : List (Bool × Fin n × Fin n), ∃ C : ℝ, ∀ f f' : Mat n → E.V, IsSec E f' → Sob μ f' →
        cls μ f' = F.Φ h (cls μ f) → ‖cls μ (Rw w f')‖ ≤ C * ‖cls μ f‖ := by
  haveI := FiniteDimensional.complete ℂ E.V
  intro Ω T F hΩ w
  obtain ⟨-, -, -, -, hCF, -, -, -, -, -, -, -, hOF, hIb, -⟩ := hC
  choose hm hhm using hh
  obtain ⟨C₁, hC₁⟩ := (GlobalTheory.T.right_word_laplacian_power_bound) n μ E.V hL hU hR hAE hCF hIb w
  obtain ⟨Q, hQ⟩ := (GlobalTheory.T.laplacian_casimir_relation) n E hR hOF
  choose Cj hCj using (GlobalTheory.T.laplacian_power_casimir_bound) n μ E Q hL hU hR hCF hQ
  refine ⟨|C₁| * ∑ j ∈ range (w.length + 1), |Cj j| * ∑ i ∈ range (j + 1), ‖hm i‖, ?_⟩
  intro f f' hsec hS hcl
  have hsob : ∀ i, Sob μ (Om^[i] f') := by
    intro i
    induction i with
    | zero => exact hS
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact GlobalTheory.CompanionTheory.SobOpsPf.sob_Om ih
  have hit : ∀ i, cls μ (Om^[i] f') = F.Φ (hm i) (cls μ f) := by
    intro i
    induction i with
    | zero =>
      have : hm 0 = h := by ext y; simp [hhm]
      simpa [this] using hcl
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      have hmem : cls μ (Om^[i] f') ∈ Msob μ E.V := Submodule.subset_span ⟨_, hsob i, rfl⟩
      rw [← hΩ _ hmem (hsob i)]
      exact F.omega (hm i) (hm (i + 1)) (fun y => by simp only [hhm]; ring) _ _ ih
  have hn : ∀ i, ‖cls μ (Om^[i] f')‖ ≤ ‖hm i‖ * ‖cls μ f‖ := by
    intro i
    rw [hit]
    exact ((F.Φ (hm i)).le_opNorm _).trans (mul_le_mul_of_nonneg_right (F.norm_le _) (norm_nonneg _))
  have hj : ∀ j, ‖cls μ (Lap^[j] f')‖ ≤ (|Cj j| * ∑ i ∈ range (j + 1), ‖hm i‖) * ‖cls μ f‖ := by
    intro j
    have hs : ∑ i ∈ range (j + 1), ‖cls μ (Om^[i] f')‖ ≤ (∑ i ∈ range (j + 1), ‖hm i‖) * ‖cls μ f‖ := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun i _ => hn i
    have h0 : 0 ≤ ∑ i ∈ range (j + 1), ‖cls μ (Om^[i] f')‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    calc _ ≤ Cj j * ∑ i ∈ range (j + 1), ‖cls μ (Om^[i] f')‖ := hCj j f' hS hsec
      _ ≤ |Cj j| * ∑ i ∈ range (j + 1), ‖cls μ (Om^[i] f')‖ :=
        mul_le_mul_of_nonneg_right (le_abs_self _) h0
      _ ≤ |Cj j| * ((∑ i ∈ range (j + 1), ‖hm i‖) * ‖cls μ f‖) :=
        mul_le_mul_of_nonneg_left hs (abs_nonneg _)
      _ = _ := by ring
  have h0 : 0 ≤ ∑ j ∈ range (w.length + 1), ‖cls μ (Lap^[j] f')‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hs : ∑ j ∈ range (w.length + 1), ‖cls μ (Lap^[j] f')‖ ≤
      (∑ j ∈ range (w.length + 1), |Cj j| * ∑ i ∈ range (j + 1), ‖hm i‖) * ‖cls μ f‖ := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun j _ => hj j
  calc _ ≤ C₁ * ∑ j ∈ range (w.length + 1), ‖cls μ (Lap^[j] f')‖ := hC₁ f' hS
    _ ≤ |C₁| * ∑ j ∈ range (w.length + 1), ‖cls μ (Lap^[j] f')‖ :=
      mul_le_mul_of_nonneg_right (le_abs_self _) h0
    _ ≤ |C₁| * ((∑ j ∈ range (w.length + 1), |Cj j| * ∑ i ∈ range (j + 1), ‖hm i‖) * ‖cls μ f‖) :=
      mul_le_mul_of_nonneg_left hs (abs_nonneg _)
    _ = _ := by ring

end

theorem smoothOp : SmoothOp := by
  intro n _ _ μ _ E
  haveI := FiniteDimensional.complete ℂ E.V
  intro Ω T F hL hU hR hS hAE hC hΩ h hh
  have hW := word_est μ E hAE hL hU hR hC h hh Ω T F hΩ
  choose Cw hCw using hW
  obtain ⟨S, Cs, hb⟩ := GlobalTheory.CompanionTheory.CurveJ.sup_bound hS n μ
  have hkeep := (GlobalTheory.T.functional_calculus_on_sobolev) n μ E Ω T F hL hU hR hS hC hΩ h
  refine ⟨|Cs| * ∑ w ∈ S, |Cw w|, fun x hx => ?_⟩
  obtain ⟨xs, hxs, hlim⟩ := mem_closure_iff_seq_limit.1 hx
  choose fs hfS hfsec hfcl using hxs
  choose a haS hasec hacl using fun k => hkeep (fs k) (hfS k) (hfsec k)
  have hacl' : ∀ k, cls μ (a k) = F.Φ h (xs k) := fun k => by rw [hacl, hfcl]

  have hdiff : ∀ w k l, ‖cls μ (Rw w (a k)) - cls μ (Rw w (a l))‖ ≤ |Cw w| * ‖xs k - xs l‖ := by
    intro w k l
    have c1 := GlobalTheory.CompanionTheory.CurveJ.sob_comb (-1) (haS l) (haS k)
    have c2 := GlobalTheory.CompanionTheory.CurveJ.sob_comb (-1) (hfS l) (hfS k)
    have e1 : cls μ (fun y => (-1 : ℂ) • fs l y + fs k y) = xs k - xs l := by
      have := c2.2 []
      simp only [Rw, id] at this
      rw [this, hfcl, hfcl]
      simp [sub_eq_neg_add]
    have e2 : cls μ (fun y => (-1 : ℂ) • a l y + a k y) = F.Φ h (cls μ (fun y => (-1 : ℂ) • fs l y + fs k y)) := by
      have := c1.2 []
      simp only [Rw, id] at this
      rw [this, hacl', hacl', e1, map_sub]
      simp [sub_eq_neg_add]
    have b := hCw w _ _ (isSec_comb E (-1) (hasec l) (hasec k)) c1.1 e2
    rw [c1.2 w, e1] at b
    have e3 : (-1 : ℂ) • cls μ (Rw w (a l)) + cls μ (Rw w (a k)) = cls μ (Rw w (a k)) - cls μ (Rw w (a l)) := by
      simp [sub_eq_neg_add]
    rw [e3] at b
    exact b.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _))
  have hcs : CauchySeq xs := hlim.cauchySeq
  have hcau : ∀ w, CauchySeq fun k => cls μ (Rw w (a k)) := by
    intro w
    rw [Metric.cauchySeq_iff] at hcs ⊢
    intro ε hε
    have hpos : 0 < |Cw w| + 1 := by positivity
    obtain ⟨N, hN⟩ := hcs (ε / (|Cw w| + 1)) (div_pos hε hpos)
    refine ⟨N, fun k hk l hl => ?_⟩
    have h1 := hN k hk l hl
    rw [dist_eq_norm] at h1 ⊢
    have h2 := hdiff w k l
    rw [lt_div_iff₀ hpos] at h1
    nlinarith [norm_nonneg (xs k - xs l), abs_nonneg (Cw w)]
  obtain ⟨b, hbS, hbt, hbp⟩ := (GlobalTheory.T.sobolev_space_complete) n μ E.V hS a haS hcau
  refine ⟨b, hbS, ?_, ?_, ?_⟩
  · intro g hg k
    have hgk : g * k.1 ∈ GLs n := by
      have hk : (k.1 : Mat n).det ≠ 0 := by
        intro h0
        have := congrArg Matrix.det (Matrix.mem_unitaryGroup_iff.1 k.2)
        rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
        exact zero_ne_one this
      show (g * k.1).det ≠ 0
      rw [Matrix.det_mul]
      exact mul_ne_zero hg hk
    have t1 := hbp _ hgk
    have t2 : Tendsto (fun j => a j (g * k.1)) atTop (𝓝 (E.ρ k⁻¹ (b g))) := by
      simp only [fun j => hasec j g hg k]
      exact ((E.ρ k⁻¹).continuous.tendsto _).comp (hbp g hg)
    exact tendsto_nhds_unique t1 t2
  · have t1 := hbt []
    simp only [Rw, id] at t1
    have t2 : Tendsto (fun k => cls μ (a k)) atTop (𝓝 (F.Φ h x)) := by
      simp only [hacl']
      exact ((F.Φ h).continuous.tendsto _).comp hlim
    exact tendsto_nhds_unique t1 t2
  · have h1 : (1 : Mat n) ∈ GLs n := by simp [GLs]
    have t1 : Tendsto (fun k => ‖a k 1‖) atTop (𝓝 ‖b 1‖) := (hbp 1 h1).norm
    have t2 : Tendsto (fun k => (|Cs| * ∑ w ∈ S, |Cw w|) * ‖xs k‖) atTop (𝓝 ((|Cs| * ∑ w ∈ S, |Cw w|) * ‖x‖)) :=
      hlim.norm.const_mul _
    refine le_of_tendsto_of_tendsto' t1 t2 fun k => ?_
    have b1 := hb E.V (a k) (haS k) 1 h1
    have h0 : 0 ≤ ∑ w ∈ S, ‖cls μ (Rw w (a k))‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hs : ∑ w ∈ S, ‖cls μ (Rw w (a k))‖ ≤ (∑ w ∈ S, |Cw w|) * ‖xs k‖ := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun w _ => ?_
      have := hCw w (fs k) (a k) (hasec k) (haS k) (by rw [hacl', hfcl])
      rw [hfcl] at this
      exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _))
    calc _ ≤ Cs * ∑ w ∈ S, ‖cls μ (Rw w (a k))‖ := b1
      _ ≤ |Cs| * ∑ w ∈ S, ‖cls μ (Rw w (a k))‖ := mul_le_mul_of_nonneg_right (le_abs_self _) h0
      _ ≤ |Cs| * ((∑ w ∈ S, |Cw w|) * ‖xs k‖) := mul_le_mul_of_nonneg_left hs (abs_nonneg _)
      _ = _ := by ring

end GlobalTheory.CompanionTheory.FcSmooth
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise

theorem _root_.GlobalTheory.T.idempotent_lattice_decomposition : ∀ (R : Type) [Ring R], (∀ x y : R, x * y = y * x) → ∀ (σ : R →+* R), (∀ x, σ (σ x) = x) → ∀ (m : ℕ) (P : (Fin m → SignType) → R), (∀ e, P e * P e = P e) → (∀ e, P e * σ (P e) = 0) → (∀ p, p * p = p → p * σ p = 0 → ∃ e, P e = p) → Function.Injective P → P 0 = 0 → (∀ e e', P (sMeet e e') = P e * P e') → (∀ e e', SLe e e' → P e * P e' = P e) → (∀ e, P e = ∑ j, P (Pi.single j (e j))) ∧ ∀ j, P (Pi.single j (-1)) = σ (P (Pi.single j 1)) := by
  first | exact @GlobalTheory.CompanionTheory.TorusCh.isotropicIdempotent_signs | exact GlobalTheory.CompanionTheory.TorusCh.isotropicIdempotent_signs | (intros; apply GlobalTheory.CompanionTheory.TorusCh.isotropicIdempotent_signs <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise

theorem _root_.GlobalTheory.T.log_abs_eq_log_idele_module : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (s : (Ad E)ˣ), logAbs (s : Ad E) = Real.log (GroundTheory.Global.IdeleGroup.ideleModule E s : ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.TorusCh.logAbs_eq_log_ideleModule | exact GlobalTheory.CompanionTheory.TorusCh.logAbs_eq_log_ideleModule | (intros; apply GlobalTheory.CompanionTheory.TorusCh.logAbs_eq_log_ideleModule <;> assumption)
end

section

open GlobalTheory.PRep PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.Cass

theorem sphericalProduct_A4 : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G], PositivityTheory.SphericalProduct.A4 G := by
  intro G _ _ _
  unfold PositivityTheory.SphericalProduct.A4
  intro D V _ _ π hπ hex
  obtain ⟨t, ht⟩ := hex
  refine ⟨fun v => GlobalTheory.CompanionTheory.Cass.proj_mem_fixed_piN G D V π v, ?_⟩
  have hsm : GlobalTheory.PRep.IsSmooth π := by
    unfold GlobalTheory.PRep.IsAdmissible at hπ
    exact hπ.1
  have hH := GlobalTheory.T.hecke_character_exists_unique
  unfold PositivityTheory.Lbc.HeckeExistsUnique at hH
  obtain ⟨U, hU, -⟩ := hH G D.J D.isOpen_J D.isCompact_J V π hsm (t : G)
  exact GlobalTheory.T.jacquet_projection_surjective_holds G D V π hπ t ht U hU

end GlobalTheory.CompanionTheory.Cass
end

section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct

theorem _root_.GlobalTheory.T.satake_power_nonvanishing : PositivityTheory.SphericalProduct.SatPowNonvan := by
  first | exact @GlobalTheory.CompanionTheory.SatPow.satPowNonvan | exact GlobalTheory.CompanionTheory.SatPow.satPowNonvan | (intros; apply GlobalTheory.CompanionTheory.SatPow.satPowNonvan <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise

theorem _root_.GlobalTheory.T.centralizer_compact_reduction : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (d : GL (Fin n) E) (C : Set (GA E n)), IsCompact C → ∃ C' : Set (GA E n), IsCompact C' ∧ ∀ t ∈ adCent d, t ∈ ((ratGL E n).range : Set (GA E n)) * C → t ∈ (ratCent d : Set (GA E n)) * C' := by
  first | exact @GlobalTheory.CompanionTheory.TorusCh.exists_isCompact_ratCent_mul | exact GlobalTheory.CompanionTheory.TorusCh.exists_isCompact_ratCent_mul | (intros; apply GlobalTheory.CompanionTheory.TorusCh.exists_isCompact_ratCent_mul <;> assumption)
end

section

noncomputable section

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

namespace GlobalTheory.CompanionTheory.SignLine

theorem signOne : PositivityTheory.RgBcC.RealD.SignOne := by
  intro V _ _ S A hA hS h1
  haveI : FiniteDimensional ℂ S := Module.finite_of_finrank_pos (by rw [h1]; exact one_pos)
  obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.mp h1
  set B : S →ₗ[ℂ] S := A.restrict hS with hBdef
  obtain ⟨c, hc⟩ := hv (B v)
  have hBw : ∀ w : S, B w = c • w := by
    intro w
    obtain ⟨d, rfl⟩ := hv w
    rw [map_smul, ← hc, smul_comm]
  have hcc : c * c = 1 := by
    have h2 : B (B v) = v := by
      apply Subtype.ext
      show A (A (v : V)) = v
      have := congrArg (fun f : V →ₗ[ℂ] V => f v) hA
      simpa using this
    rw [hBw (B v), hBw v, smul_smul] at h2
    have h3 : (c * c - 1) • v = 0 := by rw [sub_smul, h2, one_smul, sub_self]
    rcases smul_eq_zero.mp h3 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hv0
  refine ⟨c, mul_self_eq_one_iff.mp hcc, ?_⟩
  have hB : B = c • LinearMap.id := LinearMap.ext fun w => by rw [hBw]; rfl
  rw [trOn, dite_eq_left hS]
  change LinearMap.trace ℂ S B = c
  rw [hB, map_smul, LinearMap.trace_id]
  simp [h1]

end GlobalTheory.CompanionTheory.SignLine
end
end

section

open PositivityTheory.RgBcC.RealD (kF)

theorem _root_.GlobalTheory.T.center_acts_by_scalar_on_cyclic : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (F1 F2 : Fin n → Fin n → Module.End ℂ V), (∀ x : V, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ x ∈ S ∧ ∀ a b, ∀ w ∈ S, kF F1 F2 a b w ∈ S) → ∀ (z : Module.End ℂ V), (∀ a b, z * F1 a b = F1 a b * z ∧ z * F2 a b = F2 a b * z) → ∀ (ev : V →ₗ[ℂ] ℂ) (c : ℂ), (∀ v, ev (z v) = c * ev v) → (∀ S : Submodule ℂ V, FiniteDimensional ℂ S → (∀ a b, ∀ w ∈ S, kF F1 F2 a b w ∈ S) → (∀ w ∈ S, ev w = 0) → ∀ w ∈ S, w = 0) → ∀ x : V, z x = c • x := by
  first | exact @GlobalTheory.CompanionTheory.ModelS.eq_smul_of_commute_of_ev | exact GlobalTheory.CompanionTheory.ModelS.eq_smul_of_commute_of_ev | (intros; apply GlobalTheory.CompanionTheory.ModelS.eq_smul_of_commute_of_ev <;> assumption)
end

section

open PositivityTheory.RgBcC.RealD (alg kF)

theorem GlobalTheory.T.exists_k_finite_submodule_containing :
    ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
      (F1 F2 : Fin n → Fin n → Module.End ℂ V), Formalism.REAL.GlRel F1 → Formalism.REAL.GlRel F2 →
      (∀ a b c d, F1 a b * F2 c d = F2 c d * F1 a b) → ∀ f : V,
      (∀ x : V, ∃ T ∈ alg F1 F2, T f = x) → ∀ S₀ : Submodule ℂ V,
      FiniteDimensional ℂ S₀ → f ∈ S₀ → (∀ a b, ∀ w ∈ S₀, kF F1 F2 a b w ∈ S₀) →
      ∀ x : V, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ x ∈ S ∧
        ∀ a b, ∀ w ∈ S, kF F1 F2 a b w ∈ S :=
  @GlobalTheory.CompanionTheory.ModelS.LocFin.cyclic_locFin
end

section

open PositivityTheory.RgBcC.RealD (gelA)

theorem _root_.GlobalTheory.T.gelfand_invariant_commute_of_commute :
    ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
      (E : Fin n → Fin n → Module.End ℂ V) (T : Module.End ℂ V),
      (∀ a b, T * E a b = E a b * T) → ∀ m : ℕ, gelA E m * T = T * gelA E m :=
  GlobalTheory.CompanionTheory.ModelS.gelA_commute_of_units
end

section

open PositivityTheory.RgBcC.RealD (gelA)

theorem GlobalTheory.T.gelfand_invariant_eval_lowest :
    ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
      (E : Fin n → Fin n → Module.End ℂ V),
      Formalism.REAL.GlRel E → ∀ (ev : V →ₗ[ℂ] ℂ) (x : Fin n → ℂ),
        (∀ a b, b < a → ∀ v, ev (E a b v) = 0) →
        (∀ a v, ev (E a a v) = x a * ev v) →
        ∀ (m : ℕ) (v : V), ev (gelA E m v) =
          GlobalTheory.Dec.gelfVal (fun a => x a + ((n : ℂ) - 1) / 2 - ((a : ℕ) : ℂ)) m * ev v :=
  GlobalTheory.CompanionTheory.EvGel.ev_gelA
end
