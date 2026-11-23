module

import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle381
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.ElementaryCosets.CosetMap
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Archimedean
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle240
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Mathlib.Basic.Complex.Basic
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothVecUnitaryModule
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.VectorComplexifiedDerivativeCommutator
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle173
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle378
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle312
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle380
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle316
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle379
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle317
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageVanishesOpenCell
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle286
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.L2DecayOfCountEscape
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.Bundle001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm

@[expose] public section

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.LbElem.TorComm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem stdBlocks_ones_eq (N : ℕ) (a : Fin N) (i : Fin (ones N a)) :
    stdBlocks (ones N) (sum_ones N) ⟨a, i⟩ = a := by
  have hi : (i : ℕ) = 0 := by
    have := i.isLt
    simp only [ones] at this
    omega
  apply Fin.ext
  rw [stdBlocks_val]
  simp [ones, hi]

theorem offDiag_of_mem {N : ℕ} {x : GL (Fin N) k} (hx : x ∈ Tor k N) {i j : Fin N} (hij : i ≠ j) :
    (x : Matrix (Fin N) (Fin N) k) i j = 0 := by
  apply GlobalTheory.CompanionTheory.LbElem.ConjMonomial.tor_offDiag <;> assumption

theorem diag_ne_zero {N : ℕ} (x : GL (Fin N) k)
    (h : ∀ i j : Fin N, i ≠ j → (x : Matrix (Fin N) (Fin N) k) i j = 0) (i : Fin N) :
    (x : Matrix (Fin N) (Fin N) k) i i ≠ 0 := by
  have hM : (x : Matrix (Fin N) (Fin N) k) =
      Matrix.diagonal fun l => (x : Matrix (Fin N) (Fin N) k) l l := by
    ext a b
    by_cases hab : a = b
    · subst hab
      simp
    · rw [Matrix.diagonal_apply_ne _ hab]
      exact h a b hab
  have hdet : (x : Matrix (Fin N) (Fin N) k).det ≠ 0 := (Matrix.isUnits_det_units x).ne_zero
  rw [hM, Matrix.det_diagonal] at hdet
  exact Finset.prod_ne_zero_iff.mp hdet i (Finset.mem_univ i)

theorem mem_of_offDiag {N : ℕ} (x : GL (Fin N) k)
    (h : ∀ i j : Fin N, i ≠ j → (x : Matrix (Fin N) (Fin N) k) i j = 0) : x ∈ Tor k N := by
  apply GlobalTheory.CompanionTheory.LbElem.ConjMonomial.mem_tor_of_offDiag <;> assumption

theorem eq_diagonal {N : ℕ} (M : Matrix (Fin N) (Fin N) k)
    (h : ∀ i j : Fin N, i ≠ j → M i j = 0) : M = Matrix.diagonal fun i => M i i := by
  ext a b
  by_cases hab : a = b
  · subst hab
    simp
  · rw [Matrix.diagonal_apply_ne _ hab]
    exact h a b hab

theorem mul_comm_of_mem {N : ℕ} {a b : GL (Fin N) k} (ha : a ∈ Tor k N) (hb : b ∈ Tor k N) :
    a * b = b * a := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul,
    eq_diagonal (a : Matrix (Fin N) (Fin N) k) (fun i j hij => offDiag_of_mem ha hij),
    eq_diagonal (b : Matrix (Fin N) (Fin N) k) (fun i j hij => offDiag_of_mem hb hij),
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem tor_comm_and_mem_iff : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], ∀ (N : ℕ),
    (∀ a ∈ PositivityTheory.Lbc.Tor k N, ∀ b ∈ PositivityTheory.Lbc.Tor k N, a * b = b * a) ∧
      ∀ x : GL (Fin N) k, x ∈ PositivityTheory.Lbc.Tor k N ↔
        ∀ i j : Fin N, i ≠ j → (x : Matrix (Fin N) (Fin N) k) i j = 0 := by
  intro k _ _ _ _ N
  exact ⟨fun a ha b hb => mul_comm_of_mem ha hb,
    fun x => ⟨fun hx i j hij => offDiag_of_mem hx hij, mem_of_offDiag x⟩⟩

end GlobalTheory.CompanionTheory.LbElem.TorComm

end
end

section

open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

namespace GlobalTheory.CompanionTheory.Conc.LevelU

theorem exists_level : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) (L : Subgroup (GL (Fin N) (Af E))), IsOpen (L : Set (GL (Fin N) (Af E))) →
  ∃ U : Subgroup (AdelicGLn.integralFiniteGL E N), IsOpen (U : Set (AdelicGLn.integralFiniteGL E N)) ∧ ∀ u : U, ∃ k ∈ L,
    finEmb E N ((u : AdelicGLn.integralFiniteGL E N) : AdelicGLn.FiniteAdelicGL E N) = finGL E N k := by
  intro E _ _ _ N L hL
  refine ⟨L.subgroupOf (AdelicGLn.integralFiniteGL E N), hL.preimage continuous_subtype_val, ?_⟩
  intro u
  exact ⟨_, Subgroup.mem_subgroupOf.1 u.2, GlobalTheory.CompanionTheory.AutLevel.finEmb_eq_finGL E N _⟩

end GlobalTheory.CompanionTheory.Conc.LevelU
end

section

open MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.AutomorphicL2Convolution

private theorem descend_eq_sec_lemma {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {Γ : Subgroup G} [DiscreteTopology Γ]
    {φ : G → ℂ} (hφ : LeftInv Γ φ) (q : Quot Γ) : descend Γ φ q = φ (sec Γ q) := by
  have h2 : mk Γ (Quotient.out q) = mk Γ (sec Γ q) := (Quotient.out_eq q).trans (mk_sec q).symm
  obtain ⟨γ, hγ⟩ := mk_eq_iff.1 h2
  show φ (Quotient.out q) = φ (sec Γ q)
  rw [← hγ, hφ _ γ.2]

private theorem descend_rmul_lemma_2 {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {Γ : Subgroup G} [DiscreteTopology Γ]
    {φ : G → ℂ} (hφ : LeftInv Γ φ) (g : G) (q : Quot Γ) :
    descend Γ φ (rmul Γ g q) = φ (sec Γ q * g) := by
  rw [descend_eq_sec_lemma hφ]
  have h1 : rmul Γ g q = mk Γ (sec Γ q * g) := by
    rw [← rmul_mk, mk_sec]
  have h2 : mk Γ (sec Γ (rmul Γ g q)) = mk Γ (sec Γ q * g) := (mk_sec _).trans h1
  obtain ⟨γ, hγ⟩ := mk_eq_iff.1 h2
  rw [← hγ, hφ _ γ.2]

private theorem coeFn_R_lemma_3 {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {Γ : Subgroup G} [DiscreteTopology Γ]
    {μ : Measure G} [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {φ : G → ℂ} (h : MemL2Quotient Γ μ φ) (g : G) :
    ∀ᵐ q ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ),
      (((R Γ μ) g) h.toL2 : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)) q = φ (sec Γ q * g) := by
  have h2 : (fun q => (h.toL2 : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)) (rmul Γ g q)) =ᵐ[GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ]
      fun q => descend Γ φ (rmul Γ g q) :=
    (measurePreserving_rmul g).quasiMeasurePreserving.ae_eq_comp h.coeFn_toL2
  refine (coeFn_R g h.toL2).trans (h2.trans (Filter.Eventually.of_forall fun q => ?_))
  exact descend_rmul_lemma_2 h.1 g q

private theorem integral_norm_sq_lemma_4 {α : Type} [MeasurableSpace α] {m : Measure α} (F : Lp ℂ 2 m) :
    ∫ q, ‖F q‖ ^ 2 ∂m = ‖F‖ ^ 2 := by
  have h1 := MeasureTheory.L2.inner_def (𝕜 := ℂ) F F
  simp only [inner_self_eq_norm_sq_to_K] at h1
  simp_rw [← RCLike.ofReal_pow] at h1
  rw [integral_ofReal] at h1
  exact (RCLike.ofReal_inj.mp h1).symm

private theorem setIntegral_norm_le_lemma_5 {α : Type} [MeasurableSpace α] {m : Measure α} {S : Set α}
    (hS : m S < ∞) (F : Lp ℂ 2 m) :
    ∫ q in S, ‖F q‖ ∂m ≤ ((∫ q in S, (1 : ℝ) ∂m) + ‖F‖ ^ 2) / 2 := by
  haveI : IsFiniteMeasure (m.restrict S) := isFiniteMeasure_restrict.2 hS.ne
  have hsq : Integrable (fun q => ‖F q‖ ^ 2) m := (Lp.memLp F).norm.integrable_sq
  have hint1 : Integrable (fun q => (1 + ‖F q‖ ^ 2) / 2) (m.restrict S) :=
    ((integrable_const (1 : ℝ)).add hsq.restrict).div_const 2
  calc ∫ q in S, ‖F q‖ ∂m ≤ ∫ q in S, (1 + ‖F q‖ ^ 2) / 2 ∂m := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun q => norm_nonneg (F q)) hint1
          (Filter.Eventually.of_forall fun q => ?_)
        nlinarith [sq_nonneg (‖F q‖ - 1)]
    _ = ((∫ q in S, (1 : ℝ) ∂m) + ∫ q in S, ‖F q‖ ^ 2 ∂m) / 2 := by
        rw [integral_div, integral_add (integrable_const (1 : ℝ)) hsq.restrict]
    _ ≤ ((∫ q in S, (1 : ℝ) ∂m) + ‖F‖ ^ 2) / 2 := by
        have := setIntegral_le_integral (s := S) hsq (Filter.Eventually.of_forall fun q => by positivity)
        rw [integral_norm_sq_lemma_4 F] at this
        linarith

theorem memL2_convolution_mem {G L : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [DiscreteTopology Γ]
    (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μ] [Group L]
    [TopologicalSpace L] [IsTopologicalGroup L] [SecondCountableTopology L] [T2Space L] [LocallyCompactSpace L]
    [MeasurableSpace L] [BorelSpace L] (ν : Measure L) [IsFiniteMeasureOnCompacts ν] (j : L →* G)
    (hj : Continuous j) (D : L → ℂ) (hD : Continuous D) (hDc : HasCompactSupport D) (φ ψ : G → ℂ)
    (_hφ : Continuous φ) (h : MemL2Quotient Γ μ φ) (hψ : ∀ g, ψ g = ∫ y, φ (g * j y) * D y ∂ν) :
    ∃ h' : MemL2Quotient Γ μ ψ, ∀ W : Submodule ℂ (L2 Γ μ), IsSubrep (R Γ μ) W → h.toL2 ∈ W → h'.toL2 ∈ W := by
  classical
  have hLφ : LeftInv Γ φ := h.1
  have hπ' : GlobalTheory.OpTrace.IsUnitaryRep ((R Γ μ).comp j) :=
    ⟨fun y w => norm_R (j y) w, fun w => (continuous_R w).comp hj⟩
  have hDint : Integrable D ν := hD.integrable_of_hasCompactSupport hDc
  obtain ⟨hTint, hTv⟩ := isRepOp_of_integrable (μ := ν) hπ' hDint h.toL2
  set T := GlobalTheory.OpTrace.repOp ((R Γ μ).comp j) ν D with hTdef
  have hLψ : LeftInv Γ ψ := by
    intro γ hγ g
    rw [hψ (γ * g), hψ g]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show φ (γ * g * j y) * D y = φ (g * j y) * D y
    rw [mul_assoc γ g (j y), hLφ γ hγ]
  have hmeasH : Measurable fun p : L × Quot Γ => φ (sec Γ p.2 * j p.1) * D p.1 :=
    (_hφ.measurable.comp ((measurableEmbedding_sec.measurable.comp measurable_snd).mul
      (hj.measurable.comp measurable_fst))).mul (hD.measurable.comp measurable_fst)
  have hprod : ∀ S : Set (Quot Γ), MeasurableSet S → GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ S < ∞ →
      Integrable (fun p : L × Quot Γ => φ (sec Γ p.2 * j p.1) * D p.1)
        (ν.prod ((GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ).restrict S)) := by
    intro S hS hSf
    haveI : IsFiniteMeasure ((GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ).restrict S) := isFiniteMeasure_restrict.2 hSf.ne
    rw [integrable_prod_iff hmeasH.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun y => ?_, ?_⟩
    · have hc := coeFn_R_lemma_3 h (j y)
      refine ((((Lp.memLp (((R Γ μ) (j y)) h.toL2 : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ))).restrict S).integrable
        one_le_two).mul_const (D y)).congr ?_
      exact ae_restrict_of_ae (hc.mono fun q hq => by simp only [hq])
    · refine Integrable.mono'
        (hDint.norm.mul_const (((∫ q in S, (1 : ℝ) ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)) +
          ‖(h.toL2 : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ))‖ ^ 2) / 2))
        (hmeasH.norm.aestronglyMeasurable.integral_prod_right') (Filter.Eventually.of_forall fun y => ?_)
      have hc := coeFn_R_lemma_3 h (j y)
      rw [Real.norm_of_nonneg (integral_nonneg fun q => norm_nonneg _)]
      have e1 : ∫ q, ‖φ (sec Γ q * j y) * D y‖ ∂((GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ).restrict S)
          = (∫ q in S, ‖(((R Γ μ) (j y)) h.toL2 : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)) q‖ ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)) * ‖D y‖ := by
        simp_rw [norm_mul]
        rw [integral_mul_const]
        congr 1
        exact integral_congr_ae (ae_restrict_of_ae (hc.mono fun q hq => by simp only [hq]))
      have hb := setIntegral_norm_le_lemma_5 hSf ((((R Γ μ) (j y)) h.toL2 : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)))
      have hn : ‖(((R Γ μ) (j y)) h.toL2 : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ))‖
          = ‖(h.toL2 : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ))‖ := norm_R _ _
      rw [hn] at hb
      show ∫ q, ‖φ (sec Γ q * j y) * D y‖ ∂((GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ).restrict S) ≤ _
      rw [e1, mul_comm _ (‖D y‖)]
      exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)
  have hkey : (fun q => (T h.toL2 : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)) q) =ᵐ[GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ]
      fun q => ψ (sec Γ q) := by
    refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite ?_ ?_ ?_
    · intro S hS hSf
      haveI : IsFiniteMeasure ((GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ).restrict S) := isFiniteMeasure_restrict.2 hSf.ne
      exact ((Lp.memLp (T h.toL2 : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ))).restrict S).integrable one_le_two
    · intro S hS hSf
      exact (hprod S hS hSf).integral_prod_right.congr
        (Filter.Eventually.of_forall fun q => (hψ (sec Γ q)).symm)
    · intro S hS hSf
      have hSf' : GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ S ≠ ∞ := hSf.ne
      have hstep : ∀ y, ⟪indicatorConstLp 2 hS hSf' (1 : ℂ),
          (D y • ((((R Γ μ).comp j) y h.toL2 : L2 Γ μ) : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)))⟫_ℂ
          = ∫ q in S, φ (sec Γ q * j y) * D y ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) := by
        intro y
        have hc := coeFn_R_lemma_3 h (j y)
        rw [inner_smul_right, L2.inner_indicatorConstLp_one, integral_mul_const, mul_comm (D y)]
        congr 1
        exact integral_congr_ae (ae_restrict_of_ae (hc.mono fun q hq => by
          simp only [MonoidHom.comp_apply]; exact hq))
      calc ∫ q in S, (T h.toL2 : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)) q ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)
          = ⟪indicatorConstLp 2 hS hSf' (1 : ℂ), (T h.toL2 : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ))⟫_ℂ :=
            (L2.inner_indicatorConstLp_one hS hSf' _).symm
        _ = ⟪indicatorConstLp 2 hS hSf' (1 : ℂ),
              ((∫ y, D y • ((R Γ μ).comp j) y h.toL2 ∂ν : L2 Γ μ) : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ))⟫_ℂ := by
            rw [hTv]; rfl
        _ = ∫ y, ⟪indicatorConstLp 2 hS hSf' (1 : ℂ),
              (D y • ((((R Γ μ).comp j) y h.toL2 : L2 Γ μ) : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)))⟫_ℂ ∂ν :=
            (integral_inner hTint _).symm
        _ = ∫ y, ∫ q in S, φ (sec Γ q * j y) * D y ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) ∂ν :=
            integral_congr_ae (Filter.Eventually.of_forall hstep)
        _ = ∫ q in S, ∫ y, φ (sec Γ q * j y) * D y ∂ν ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) :=
            integral_integral_swap (hprod S hS hSf)
        _ = ∫ q in S, ψ (sec Γ q) ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) :=
            integral_congr_ae (Filter.Eventually.of_forall fun q => (hψ (sec Γ q)).symm)
  have hae : descend Γ ψ =ᵐ[GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ] fun q => (T h.toL2 : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)) q :=
    Filter.EventuallyEq.trans (Filter.Eventually.of_forall fun q => descend_eq_sec_lemma hLψ q) hkey.symm
  have hmem : MemL2Quotient Γ μ ψ := ⟨hLψ, MemLp.ae_eq hae.symm (Lp.memLp _)⟩
  refine ⟨hmem, fun W hW hvW => ?_⟩
  have hEq : hmem.toL2 = T h.toL2 := Lp.ext (hmem.coeFn_toL2.trans hae)
  rw [hEq]
  exact IsSubrep.map_mem_of_isRepOp (π := (R Γ μ).comp j) ⟨hW.1, fun y w hw => hW.2 (j y) w hw⟩
    (isRepOp_of_integrable hπ' hDint) hvW

end GlobalTheory.CompanionTheory.AutomorphicL2Convolution
end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.CompactAvg

theorem invariant_forms_separate_fixed :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (J : Subgroup G),
      IsCompact (J : Set G) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ G V), IsSmooth π → ∀ u ∈ fixed π J,
      (∀ l : Module.Dual ℂ V, (∀ x ∈ J, l ∘ₗ π x = l) → l u = 0) → u = 0 := by
  intro G _ _ _ J hJ V _ _ π hπ u hu hl
  obtain ⟨E, -, hfix, -, hinv, -⟩ := GlobalTheory.T.compact_fixed_vector_projection G J hJ V π hπ
  by_contra hne
  have hex : ∃ l0 : Module.Dual ℂ V, l0 u ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hne ((Module.forall_dual_apply_eq_zero_iff ℂ u).1 hall)
  obtain ⟨l0, hl0⟩ := hex
  have hzero : (l0 ∘ₗ E) u = 0 := by
    refine hl (l0 ∘ₗ E) fun x hx => ?_
    rw [LinearMap.comp_assoc, hinv x hx]
  apply hl0
  simpa [hfix u hu] using hzero

end GlobalTheory.CompanionTheory.CompactAvg
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

theorem _root_.GlobalTheory.T.product_single_nonzero_factor_equiv : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {h N : ℕ} (Y : Fin h → IrrGL (k := k)) (hd : ∑ a, (Y a).1 = N) (i₀ : Fin h), (∀ i, i ≠ i₀ → (Y i).1 = 0) → ∃ z : IrrCl (GL (Fin N) k), (⟨N, z⟩ : IrrGL (k := k)) = Y i₀ ∧ Nonempty ((prodIrr Y hd).Equiv z.rep.ρ) := by
  first | exact @GlobalTheory.CompanionTheory.FineProd.ProdSingle.prodIrr_single | exact GlobalTheory.CompanionTheory.FineProd.ProdSingle.prodIrr_single | (intros; apply GlobalTheory.CompanionTheory.FineProd.ProdSingle.prodIrr_single <;> assumption)
end

section

open scoped InnerProductSpace
open Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.SmoothVecMod

noncomputable section

namespace GlobalTheory.CompanionTheory.SmoothVecGl

theorem unitAct_glRel : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ),
    Formalism.REAL.GlRel (fun a b => GlobalTheory.SmoothVecMod.unitAct hσ a b) := by
  intro n ε H _ _ σ hσ
  have key : ∀ a b (u : smoothVec ε σ), ∀ g ∈ UJset ε,
      σ g (unitAct hσ a b u) = EabV ε a b (fun g => σ g u) g :=
    fun a b u g hg => rep_eabV hσ u.2 a b hg
  intro a b c d
  ext u
  have h := eabGlV_of (rdLinV_of vector_right_derivative_extends)
    (rdBracketV_of vector_right_derivative_extends (rdSmoothV_of vector_right_derivative_extends)) (rdSmoothV_of vector_right_derivative_extends)
    n ε H (fun g => σ g u) a b c d 1 u.2 inUJ_one
  rw [← eabV_congr (key c d u) a b inUJ_one, ← eabV_congr (key a b u) c d inUJ_one] at h
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub]
  rw [unitAct_coe hσ a b, unitAct_coe hσ c d (unitAct hσ a b u), h]
  split_ifs <;> simp [unitAct_coe]

end GlobalTheory.CompanionTheory.SmoothVecGl
end
end

section

open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.CoefSmooth

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem coef_smoothOnG (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (v : GlobalTheory.SmoothVecMod.smoothVec ε σ) (w : H) :
    Formalism.REAL.SmoothOnG ε (fun g => ⟪w, σ g (v : H)⟫_ℂ) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := v.2 g₀ hg₀
  refine ⟨U, fun x => ⟪w, F x⟫_ℂ, hU, hgU, ?_, fun g hg hgJ => ?_⟩
  · exact (((innerSL ℂ w).restrictScalars ℝ).contDiff.comp_contDiffOn hF)
  · exact congrArg (fun z => ⟪w, z⟫_ℂ) (hfF g hg hgJ)

theorem coef_smooth : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (v : GlobalTheory.SmoothVecMod.smoothVec ε σ) (w : H),
    Formalism.REAL.SmoothOnG ε (fun g => ⟪w, σ g (v : H)⟫_ℂ) :=
  fun n ε H _ _ σ v w => coef_smoothOnG n ε H σ v w

end GlobalTheory.CompanionTheory.CoefSmooth
end
end

section

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)

theorem _root_.GlobalTheory.T.top_graded_quotient_injective_map : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {W : X.Opens} {d : ℕ} (t : Fin d → Γ(X, W)) (s : ℕ) (E : Frame (sP (KS q s {W})) d)
    (ε : Γ(X, W) ≃+* (sP (KS q s {W})).A.obj E.D), IsLoc q s t E ε → ∀ (σ : ∀ T, E.D ⟶ T) (r : ℤ), r = d → d + 1 ≤ s →
    letI := (strV q W).toAlgebra
    ∃ φ : HQ (KS q s {W}) r (r + 1) d →ₗ[K] Γ(X, W), Function.Injective φ ∧ ∀ (y : Γ(X, W)) (c : HQ (KS q s {W}) r (r + 1) d),
      CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {W}) r) (sFil (KS q s {W}) (r + 1)) (E.form σ id (ε y)) c → φ c = y := by
  first | exact @GlobalTheory.CompanionTheory.ConeLocal.coef_map | exact GlobalTheory.CompanionTheory.ConeLocal.coef_map | (intros; apply GlobalTheory.CompanionTheory.ConeLocal.coef_map <;> assumption)
end

section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair


theorem _root_.GlobalTheory.T.mirabolic_pairing_conductor_bound : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (c : kˣ) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ), Continuous ψ → HasConductor ψ c → IsSmooth T → IsSmooth T' → TwInv T T' B s → ∀ (g : GL (Fin (n + 1)) k) (v : V) (v' : V'), ∃ r : kˣ, ∀ t : kˣ, valuation k ((c * t⁻¹ : kˣ) : k) ≤ valuation k (r : k) → ∀ t' : kˣ, (∀ x ∈ box (n + 1) t, (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x ∈ box (n + 1) t') → JJ ν ψ T B {x | (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x ∈ box (n + 1) t'} v v' = JJ ν ψ T B (box (n + 1) t : Set (Fin (n + 1) → k)) v v' := by
  first | exact @GlobalTheory.CompanionTheory.MirPair.JJ_preimage_box_eq_JJ_box | exact GlobalTheory.CompanionTheory.MirPair.JJ_preimage_box_eq_JJ_box | (intros; apply GlobalTheory.CompanionTheory.MirPair.JJ_preimage_box_eq_JJ_box <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

theorem _root_.GlobalTheory.T.fibre_function_locally_constant_compact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W), IsSmooth τ → IsSmooth σ → ∀ (f : cIndSpace (HPG k i t) (hRep τ σ)) (g : GL (Fin (i + t)) k), IsLocallyConstant (fibV f g) ∧ HasCompactSupport (fibV f g) := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.fibV_main | exact GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.fibV_main | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.fibV_main <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

theorem _root_.GlobalTheory.T.average_vanishes_open_cell : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (f : XS τ σ) (h0 : eO ψ f = 0)
    (p : Mir k ((i + 1) + t + 1)) (hp : p ∉ Cl k i t),
  AvgVanish (HPG k (i + 1) (t + 1)) (sigX τ σ) (MirUin k ((i + 1) + t + 1)) (mirChar k ψ ((i + 1) + t)) f p := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.LocO.main | exact GlobalTheory.CompanionTheory.BZPhiPG.LocO.main | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.LocO.main <;> assumption)
end
