module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle256
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle287
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle257
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle285
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaLatticeImageRationalHomLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle286
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StarMulOfMemKc
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle076
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle015
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle035
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle097
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle102
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle105
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle109
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle111
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle018
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle100
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle288
import Formalism.GradedWeylDivisibility.FinalD
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle289
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

@[expose] public section

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
open GlobalTheory.EvenTheta GlobalTheory.ThetaTransl

theorem _root_.GlobalTheory.T.sigmaStarCubeDerivWeierstrassP_parameterSeries_bounded : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), g.Ok → IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar →
    g3 g.abelian₂ ∈ Qbar → TaylorLogMetric.discr g.abelian₂ = 1 → AlgEnt (sgStar g.abelian₂) → ∀ v, v ∉ g.abelian₂ → wpF g.abelian₂ v ∈ Qbar →
      AlgEnt (sqThD g.abelian₂ v) ∧ ∃ w : PowerSeries ℂ_[p], BddSer w ∧
        g.atU (sqThD g.abelian₂ v) = ePhi1 g.lam g.abelian₂ g.C g.wq ^ 3 * w := by
  first | exact @GlobalTheory.ThetaTransl.CubeSer.sqThD_atU | exact GlobalTheory.ThetaTransl.CubeSer.sqThD_atU | (intros; apply GlobalTheory.ThetaTransl.CubeSer.sqThD_atU <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries

theorem _root_.GlobalTheory.T.frobeniusStickelberger_defect_padic_of_complex : ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (f : Fin 3 → ℂ → ℂ) (s : ℂ → ℂ), (∀ j, AlgEnt (f j)) → AlgEnt s → GlobalTheory.FrobStick.defect (fun j => GlobalTheory.FrobStick.tay (f j)) (GlobalTheory.FrobStick.tay s) = 0 → GlobalTheory.FrobStick.defect (fun j => GL3Theta.ser1 lam (f j)) (GL3Theta.ser1 lam s) = 0 := by
  first | exact @GlobalTheory.FrobStickMap.defect_ser1_eq_zero_of_defect_tay_eq_zero | exact GlobalTheory.FrobStickMap.defect_ser1_eq_zero_of_defect_tay_eq_zero | (intros; apply GlobalTheory.FrobStickMap.defect_ser1_eq_zero_of_defect_tay_eq_zero <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries

theorem _root_.GlobalTheory.T.sigmaStar_cube_columns_model_parameter_series : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), IsWq g.W g.wq → IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar → g3 g.abelian₂ ∈ Qbar → AlgEnt (sgStar g.abelian₂) → ∀ v, v ∉ g.abelian₂ → wpF g.abelian₂ v ∈ Qbar → AlgEnt (GlobalTheory.FrobStick.colA g.abelian₂) ∧ AlgEnt (GlobalTheory.FrobStick.colB g.abelian₂ v) ∧ g.atU (sgStar g.abelian₂) = PowerSeries.C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * PowerSeries.X * ePhi1 g.lam g.abelian₂ g.C g.wq ∧ g.atU (GlobalTheory.FrobStick.colA g.abelian₂) = PowerSeries.C (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 3) * PowerSeries.X ^ 3 * ePhi1 g.lam g.abelian₂ g.C g.wq ^ 3 ∧ g.atU (GlobalTheory.FrobStick.colB g.abelian₂ v) = PowerSeries.C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * ePhi1 g.lam g.abelian₂ g.C g.wq ^ 3 * (PowerSeries.X * g.wq⁻¹ + PowerSeries.C (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 2 * g.C.r) * PowerSeries.X ^ 3) := by
  first | exact @GlobalTheory.FrobStick.colAB_atU | exact GlobalTheory.FrobStick.colAB_atU | (intros; apply GlobalTheory.FrobStick.colAB_atU <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries

theorem _root_.GlobalTheory.T.sigmaStarCube_wpDeriv_model_parameter_series : (∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p) (F : ℂ → ℂ), AlgEnt F → AlgEnt (deriv F) ∧ PowerSeries.derivative (R := ℂ_[p]) (g.atU F) = PowerSeries.C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * omegaW g.W g.wq * g.atU (deriv F)) → ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), IsWq g.W g.wq → IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar → g3 g.abelian₂ ∈ Qbar → AlgEnt (sgStar g.abelian₂) → ∀ v, v ∉ g.abelian₂ → wpF g.abelian₂ v ∈ Qbar → AlgEnt (GlobalTheory.FrobStick.colC g.abelian₂ v) ∧ g.atU (GlobalTheory.FrobStick.colC g.abelian₂ v) = ePhi1 g.lam g.abelian₂ g.C g.wq ^ 3 * g.wq⁻¹ * (PowerSeries.C g.W.a₁ * PowerSeries.X + PowerSeries.C g.W.a₃ * PowerSeries.X ^ 3 * g.wq - 2) := by
  first | exact @GlobalTheory.FrobStick.colC_atU | exact GlobalTheory.FrobStick.colC_atU | (intros; apply GlobalTheory.FrobStick.colC_atU <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

theorem _root_.GlobalTheory.T.exists_thetaLattice_correspondence_weilOperator : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → δ ≠ 0 → ∀ (N N' : ℕ) (e0 : VC D N N' → ℂ) (W : WeilO D cc δ N N' e0) (g h k : GA D N) (g' h' k' : GA D N') (L₁ L₂ M₁ M₂ : Lat D N) (L₁' L₂' M₁' M₂' : Lat D N'), Moves D (h : GL (Fin N) (AE D)) L₁ → Moves D (h' : GL (Fin N') (AE D)) L₁' → Moves D ((g * h : GA D N) : GL (Fin N) (AE D)) L₂ → Moves D ((g' * h' : GA D N') : GL (Fin N') (AE D)) L₂' → Moves D (k : GL (Fin N) (AE D)) M₁ → Moves D (k' : GL (Fin N') (AE D)) M₁' → Moves D ((g * k : GA D N) : GL (Fin N) (AE D)) M₂ → Moves D ((g' * k' : GA D N') : GL (Fin N') (AE D)) M₂' → ∀ F ∈ TT D (tor0 D cc δ) N N', ∃ f : La D (tor0 D cc δ) M₁ M₁' → La D (tor0 D cc δ) M₂ M₂', (∀ x : La D (tor0 D cc δ) M₁ M₁', W.Om g g' (Wd D (tor0 D cc δ) (x : VC D N N') F) = Wd D (tor0 D cc δ) (f x : VC D N N') (W.Om g g' F)) ∧ (∀ x y : La D (tor0 D cc δ) M₁ M₁', (x : VC D N N') - (y : VC D N N') ∈ La D (tor0 D cc δ) L₁ L₁' ↔ (f x : VC D N N') - (f y : VC D N N') ∈ La D (tor0 D cc δ) L₂ L₂') ∧ ∀ y : La D (tor0 D cc δ) M₂ M₂', ∃ x : La D (tor0 D cc δ) M₁ M₁', (f x : VC D N N') - (y : VC D N N') ∈ La D (tor0 D cc δ) L₂ L₂' := by
  first | exact @GlobalTheory.WeilCorr.exists_corr | exact GlobalTheory.WeilCorr.exists_corr | (intros; apply GlobalTheory.WeilCorr.exists_corr <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

theorem _root_.GlobalTheory.T.thetaLattice_image_rationalHomLattice : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), δ ≠ 0 → ∀ (N N' : ℕ), Function.Injective (pt D (tor0 D cc δ) δ : Matrix (Fin N') (Fin N) D.host.E → VC D N N') ∧ (∀ (L : Lat D N) (L' : Lat D N') (x : VC D N N'), x ∈ La D (tor0 D cc δ) L L' ↔ ∃ z ∈ RL D cc L L', x = pt D (tor0 D cc δ) δ z) ∧ (∀ (L' : Lat D N') (z : Matrix (Fin N') (Fin N) D.host.E), z ∈ RL D cc (stdL D N) L' ↔ ∀ j, (fun i => z i j) ∈ Submodule.span (𝓞 D.host.E) {v | ∃ t ∈ Iid D cc, ∃ y ∈ L', v = t • y}) ∧ ∀ (L : Lat D N), SD D L → ∀ (z : Matrix (Fin N') (Fin N) D.host.E), z ∈ RL D cc L (stdL D N') ↔ ∀ i, z i ∈ Submodule.span (𝓞 D.host.E) {v | ∃ t ∈ Iid D cc, ∃ y ∈ L, v = t • fun j => D.host.conj (y j)} := by
  first | exact @GlobalTheory.ThetaLatImage.theta_lattice_image | exact GlobalTheory.ThetaLatImage.theta_lattice_image | (intros; apply GlobalTheory.ThetaLatImage.theta_lattice_image <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators

theorem _root_.GlobalTheory.T.exists_homLattice_commensurable_orthonormal : ∀ (D : D7) (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), OnB D b → SD D L → SD D L' → ∃ k : ℕ, 0 < k ∧ Comm D b k (YYl D L L' : Set (Matrix (Fin N') (Fin N) D.host.E)) := by
  first | exact @GlobalTheory.ThetaConj.exists_comm_YYl | exact GlobalTheory.ThetaConj.exists_comm_YYl | (intros; apply GlobalTheory.ThetaConj.exists_comm_YYl <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower GlobalTheory.CartanInt Matrix MeasureTheory
open Filter Topology

namespace GlobalTheory.CartanInt.ExpLocal

attribute [local instance] GlobalTheory.CompactDualExists.sumNormedAddCommGroup
  GlobalTheory.CompactDualExists.sumNormedSpace

theorem l1_eq_norm {n : Type} [Fintype n] (A : Matrix n n ℂ) : l1 A = ‖A‖ :=
  (GlobalTheory.CompactDualExists.sum_norm_def A).symm

theorem exists_exp_approx (n : Type) [Fintype n] [DecidableEq n] :
    ∃ r : ℝ, 0 < r ∧ ∀ Y : Matrix n n ℂ, ‖Y‖ < r →
      ‖NormedSpace.exp Y - 1 - Y‖ ≤ 1 / 21 * ‖Y‖ := by
  have h := (GlobalTheory.CompactDualExists.exp_strict (n := n)).hasFDerivAt
  have h2 := h.isLittleO.def (c := 1 / 21) (by norm_num)
  obtain ⟨r, hr, H⟩ := Metric.eventually_nhds_iff_ball.1 h2
  refine ⟨r, hr, fun Y hY => ?_⟩
  have h3 := H Y (mem_ball_zero_iff.2 hY)
  rw [NormedSpace.exp_zero, sub_zero] at h3
  exact h3

theorem exp_log_near_one : ∀ (p q : ℕ), ∃ ρ : ℝ, 0 < ρ ∧ (∀ Y : Mat p q, l1 Y < ρ → l1 (NormedSpace.exp Y - 1) ≤ 21 / 20 * l1 Y) ∧ ∀ g : UpqT p q, l1 (UpqT.mat g - 1) < ρ → ∃ X : lieU p q, UpqT.mat g = NormedSpace.exp (X : Mat p q) ∧ l1 (X : Mat p q) ≤ 21 / 20 * l1 (UpqT.mat g - 1) := by
  intro p q
  obtain ⟨r, hr, H⟩ := exists_exp_approx (Fin p ⊕ Fin q)
  have hN := GlobalTheory.ExpBallNhds.exp_ballU_mem_nhds p q r hr
  rw [GlobalTheory.UpqTopology.isInducing_mat.nhds_eq_comap, Filter.mem_comap] at hN
  obtain ⟨T, hT, hsub⟩ := hN
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hT
  refine ⟨min r ε, lt_min hr hε, fun Y hY => ?_, fun g hg => ?_⟩
  · rw [l1_eq_norm] at hY
    rw [l1_eq_norm, l1_eq_norm]
    have h1 := H Y (hY.trans_le (min_le_left _ _))
    have h2 := norm_le_norm_add_norm_sub' (NormedSpace.exp Y - 1) Y
    have h3 := norm_nonneg Y
    linarith
  · rw [l1_eq_norm] at hg
    have hg' : UpqT.mat g ∈ Metric.ball (UpqT.mat (1 : UpqT p q)) ε := by
      rw [mem_ball_iff_norm, mat_one]
      exact hg.trans_le (min_le_right _ _)
    obtain ⟨X, hX, hgX⟩ := hsub (show g ∈ UpqT.mat ⁻¹' T from hball hg')
    refine ⟨X, hgX, ?_⟩
    have hX' : l1 (X : Mat p q) < r := hX
    rw [l1_eq_norm] at hX'
    rw [l1_eq_norm, l1_eq_norm, hgX]
    have h1 := H X hX'
    have h2 := norm_le_norm_add_norm_sub (NormedSpace.exp (X : Mat p q) - 1) (X : Mat p q)
    linarith

end GlobalTheory.CartanInt.ExpLocal
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower Matrix MeasureTheory

noncomputable section
namespace GlobalTheory.CartanInt

variable {p q : ℕ}

theorem isInvInvariant_of_right {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant] : μ.IsInvInvariant := by
  constructor
  let c : ENNReal := Measure.haarScalarFactor μ.inv μ
  have hc : μ.inv = c • μ := Measure.isMulLeftInvariant_eq_smul μ.inv μ
  have h1 : Measure.map Inv.inv (Measure.map Inv.inv μ) = c ^ 2 • μ := by
    rw [← Measure.inv_def μ, hc, Measure.map_smul c continuous_inv.measurable.aemeasurable, ← Measure.inv_def μ, hc, smul_smul, pow_two]
  have μeq : μ = c ^ 2 • μ := by
    rw [Measure.map_map continuous_inv.measurable continuous_inv.measurable] at h1
    simpa only [inv_involutive, Function.Involutive.comp_self, Measure.map_id] using h1
  have K : TopologicalSpace.PositiveCompacts G := Classical.arbitrary _
  have h2 : c ^ 2 * μ K = 1 ^ 2 * μ K := by
    conv_rhs => rw [μeq]
    simp
  have h3 : c ^ 2 = 1 ^ 2 :=
    (ENNReal.mul_left_inj (Measure.measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
          K.isCompact.measure_lt_top.ne).1 h2
  have h4 : c = 1 := (ENNReal.pow_right_strictMono two_ne_zero).injective h3
  rw [hc, h4, one_smul]

theorem isUnit_mat (g : UpqT p q) : IsUnit (UpqT.mat g) := Units.isUnit _

theorem isCompact_Kc : IsCompact (Kc p q) := by
  have h : Kc p q = ⋂ a, ⋂ b, ⋂ (_ : ¬ sameBlock a b), {x : UpqT p q | UpqT.mat x a b = 0} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    exact Iff.rfl
  have hcl : IsClosed (Kc p q) := by
    rw [h]
    refine isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun _ => ?_
    exact isClosed_eq (GlobalTheory.UpqTopology.continuous_mat.matrix_elem a b) continuous_const
  have hc : IsCompact (Set.univ.pi fun _ : Ix p q => Set.univ.pi fun _ : Ix p q => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  refine (GlobalTheory.UpqTopology.isClosedEmbedding_mat.isCompact_preimage (K := _) hc).of_isClosed_subset hcl ?_
  intro x hx a _ b _
  simpa using entry_norm_bound_of_unitary (Matrix.mem_unitaryGroup_iff'.2 (star_mul_of_mem_Kc hx)) a b

theorem exists_action (L : Mat p q → (Fin p → Fin q → ℂ)) (hL : ContinuousOn L {g | IsUnit g})
    (hLk : ∀ (k : Mat p q) (B : Fin p → Fin q → ℂ), kᴴ * k = 1 → L (k * NormedSpace.exp (pY B)) = B)
    (g : UpqT p q) : ∃ ψ : (Fin p → Fin q → ℂ) → (Fin p → Fin q → ℂ), Continuous ψ ∧ Function.Bijective ψ ∧
      ∀ B, ∃ κ ∈ Kc p q, eP B * g = κ * eP (ψ B) := by
  obtain ⟨i1, -⟩ := GlobalTheory.UpqTopology.upq_lcsc p q
  let ψ : UpqT p q → (Fin p → Fin q → ℂ) → (Fin p → Fin q → ℂ) := fun g B => L (UpqT.mat (eP B * g))
  have key : ∀ (x κ : UpqT p q) (B' : Fin p → Fin q → ℂ), κ ∈ Kc p q → x = κ * eP B' →
      L (UpqT.mat x) = B' := by
    intro x κ B' hκ hx
    rw [hx, mat_mul, mat_eP]
    exact hLk _ _ (star_mul_of_mem_Kc hκ)
  have dec : ∀ g B, ∃ κ ∈ Kc p q, eP B * g = κ * eP (ψ g B) := by
    intro g B
    obtain ⟨κ, hκ, B', h⟩ := exists_cartan (eP B * g)
    have : ψ g B = B' := key _ κ B' hκ h
    exact ⟨κ, hκ, by rw [this]; exact h⟩
  have inv : ∀ g B, ψ g⁻¹ (ψ g B) = B := by
    intro g B
    obtain ⟨κ, hκ, h⟩ := dec g B
    refine key _ κ⁻¹ B ((Ksg p q).inv_mem hκ) ?_
    rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, ← h, mul_inv_cancel_right]
  refine ⟨ψ g, ?_, ?_, dec g⟩
  · exact hL.comp_continuous
      (GlobalTheory.UpqTopology.continuous_mat.comp (continuous_eP.mul continuous_const)) fun B => isUnit_mat _
  · refine Function.bijective_iff_has_inverse.2 ⟨ψ g⁻¹, inv g, fun B => ?_⟩
    have := inv g⁻¹ B
    rwa [inv_inv] at this

theorem haar_polar : ∀ (p q : ℕ) (m : Measure (UpqT p q)), m.IsHaarMeasure → ∃ (c : ℝ) (mK : Measure (UpqT p q)), 0 < c ∧ IsProbabilityMeasure mK ∧ mK (Kc p q)ᶜ = 0 ∧ (∀ k ∈ Kc p q, Measure.map (fun x => k * x) mK = mK) ∧ ∀ f : UpqT p q → ENNReal, Measurable f → ∫⁻ g, f g ∂m = ENNReal.ofReal c * ∫⁻ B : Fin p → Fin q → ℂ, (∫⁻ k, f (k * eP B) ∂mK) * ENNReal.ofReal (polJ (pY B)) := by
  intro p q m hm
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.UpqTopology.upq_lcsc p q
  haveI := GlobalTheory.UpqUnimodular.isMulRightInvariant_of_isHaarMeasure p q m hm
  haveI := isInvInvariant_of_right m
  obtain ⟨mK, hprob, hK0, hleft, hright⟩ :=
    GlobalTheory.exists_biinvariant_probability_on_compact_subgroup (UpqT p q) (Ksg p q) isCompact_Kc
  obtain ⟨L, hLc, hL⟩ := GlobalTheory.PolarLogCont.exists_continuousOn_polar_log p q
  have hpos : ∀ B : Fin p → Fin q → ℂ, 0 < polJ (pY B) := fun B => one_pos.trans_le (one_le_polJ _)
  have hJc : Continuous fun B : Fin p → Fin q → ℂ => polJ (pY B) := (continuous_polJ p q).comp continuous_pY
  have hJm : Measurable fun B : Fin p → Fin q → ℂ => ENNReal.ofReal (polJ (pY B)) :=
    ENNReal.measurable_ofReal.comp hJc.measurable
  have hdet : ∀ B : Fin p → Fin q → ℂ, LinearMap.det (sP (pY B)) = polJ (pY B) :=
    fun B => det_sinhc_eq_polarJacobian p q _ (SinhcPres.sAd_pY p q B)
  have hem : Measurable (eP : (Fin p → Fin q → ℂ) → UpqT p q) := continuous_eP.measurable
  haveI : IsLocallyFiniteMeasure
      ((volume : Measure (Fin p → Fin q → ℂ)).withDensity fun B => ENNReal.ofReal (polJ (pY B))) :=
    IsLocallyFiniteMeasure.withDensity_ofReal hJc
  obtain ⟨c, hc, hf⟩ := GlobalTheory.Twist.lintegral_haar_eq_transversal (UpqT p q) (Fin p → Fin q → ℂ) m mK
    (volume.withDensity fun B => ENNReal.ofReal (polJ (pY B))) (Kc p q) eP hem hK0 hright
    (by
      intro h0
      rw [withDensity_eq_zero_iff hJm.aemeasurable] at h0
      haveI : (volume : Measure (Fin q → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
      haveI : (volume : Measure (Fin p → Fin q → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
      haveI : (ae (volume : Measure (Fin p → Fin q → ℂ))).NeBot :=
        ae_neBot.2 fun h => (isOpen_univ.measure_ne_zero (volume : Measure (Fin p → Fin q → ℂ))
          Set.univ_nonempty) (by rw [h]; rfl)
      obtain ⟨B, hB⟩ := h0.exists
      exact absurd hB (by simpa using hpos B))
    (by
      intro C hC
      have hcomp : IsCompact (L '' (UpqT.mat '' C)) :=
        (hC.image GlobalTheory.UpqTopology.continuous_mat).image_of_continuousOn (hLc.mono (by
          rintro _ ⟨x, -, rfl⟩; exact isUnit_mat x))
      refine lt_of_le_of_lt (measure_mono ?_) hcomp.measure_lt_top
      rintro B ⟨k, hk, hB⟩
      refine ⟨_, ⟨_, hB, rfl⟩, ?_⟩
      rw [mat_mul, mat_eP]
      exact hL _ B (star_mul_of_mem_Kc hk))
    (by
      intro g
      obtain ⟨ψ, hψc, hψb, hψ⟩ := exists_action L hLc hL g
      refine ⟨ψ, hψc.measurable, GlobalTheory.map_withDensity_of_jacobian p q _ ψ hJc hψc hψb ?_, hψ⟩
      have := jacobian_action_p p q (UpqT.mat g) ψ hψc (fun B => by
          obtain ⟨κ, hκ, h⟩ := hψ B
          obtain ⟨U, hU, V, hV, hm⟩ := (mem_Kc_iff κ).1 hκ
          refine ⟨U, hU, V, hV, ?_⟩
          have := congrArg UpqT.mat h
          rwa [mat_mul, mat_mul, mat_eP, mat_eP, hm] at this)
        (fun B => by rw [hdet]; exact hpos B) (SinhcPres.sAd_pY p q)
        (fun B => hasStrictFDerivAt_exp_two_pY p q B (hasDerivAt_exp_two_add_smul p q (pY B)))
      simpa only [hdet] using this)
  refine ⟨c, mK, hc, hprob, hK0, hleft, fun f hfm => ?_⟩
  rw [hf f hfm, lintegral_withDensity_eq_lintegral_mul _ hJm]
  · congr 1
    refine lintegral_congr fun B => ?_
    simp only [Pi.mul_apply, mul_comm]
  · exact Measurable.lintegral_prod_right' (f := fun z : (Fin p → Fin q → ℂ) × UpqT p q => f (z.2 * eP z.1))
      (hfm.comp (measurable_snd.mul (hem.comp measurable_fst)))

end GlobalTheory.CartanInt
end
end

section

noncomputable section
namespace GlobalTheory.CartanInt.UnitLog
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower GlobalTheory.CartanInt Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator

theorem norm_entry_le {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (a b : n) :
    ‖A a b‖ ≤ ‖A‖ := by
  have h := A.l2_opNorm_mulVec (EuclideanSpace.single b (1 : ℂ))
  have h2 := PiLp.norm_apply_le ((EuclideanSpace.equiv n ℂ).symm (A *ᵥ (EuclideanSpace.single b (1 : ℂ)))) a
  simp only [PiLp.norm_single, norm_one, mul_one] at h
  refine le_trans ?_ (h2.trans h)
  simp

theorem exists_log {n : Type} [Fintype n] [DecidableEq n] (u : Matrix n n ℂ)
    (hu : u ∈ unitary (Matrix n n ℂ)) :
    ∃ H : Matrix n n ℂ, Hᴴ = H ∧ ‖H‖ ≤ Real.pi ∧ u = NormedSpace.exp (Complex.I • H) ∧
      ∀ J, Commute u J → Commute (star u) J → Commute H J := by
  have hn : IsStarNormal u := isStarNormal_of_mem_unitary hu
  have hfin : (spectrum ℂ u).Finite := Matrix.finite_spectrum u
  have hsph : ∀ z ∈ spectrum ℂ u, ‖z‖ = 1 := fun z hz => by
    simpa using spectrum.subset_circle_of_unitary hu hz
  refine ⟨cfc (fun z : ℂ => (Complex.arg z : ℂ)) u, ?_, ?_, ?_, fun J h1 h2 => h1.cfc h2 _⟩
  · rw [← Matrix.star_eq_conjTranspose, ← cfc_star]
    refine cfc_congr fun z _ => ?_
    simp
  · refine norm_cfc_le Real.pi_pos.le fun z _ => ?_
    simpa using Complex.abs_arg_le_pi z
  · rw [← cfc_const_mul Complex.I _ u (hf := hfin.continuousOn _),
      ← CFC.exp_eq_normedSpace_exp (𝕜 := ℂ), ← Complex.exp_eq_exp_ℂ,
      ← cfc_comp' Complex.exp _ u (hf := hfin.continuousOn _)]
    conv_lhs => rw [← cfc_id' ℂ u]
    refine cfc_congr fun z hz => ?_
    have := Complex.norm_mul_exp_arg_mul_I z
    rw [hsph z hz, mul_comm _ Complex.I] at this
    simpa using this.symm

theorem isKC_iff_commute {p q : ℕ} (X : Mat p q) : IsKC X ↔ Commute X (Formalism.UG.Jpq p q) := by
  constructor
  · intro h
    ext a b
    have h1 := h a b
    rcases a with i | i <;> rcases b with j | j <;>
      simp_all [sameBlock, Formalism.UG.Jpq, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
  · intro h a b hab
    have h1 := congrFun (congrFun h.eq a) b
    rcases a with i | i <;> rcases b with j | j <;>
      simp [sameBlock, Formalism.UG.Jpq, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply] at h1 hab ⊢
    · linear_combination (-1 / 2 : ℂ) * h1
    · linear_combination (1 / 2 : ℂ) * h1

theorem exists_unitlog : ∀ (p q : ℕ) (k : UpqT p q), k ∈ Kc p q → ∃ H : Mat p q, Hᴴ = H ∧ IsKC H ∧
    (∀ a b, ‖H a b‖ ≤ Real.pi) ∧ UpqT.mat k = NormedSpace.exp (Complex.I • H) := by
  intro p q k hk
  have hu : (UpqT.mat k : Mat p q) ∈ unitary (Mat p q) :=
    Matrix.mem_unitaryGroup_iff'.2 (star_mul_of_mem_Kc hk)
  obtain ⟨H, h1, h2, h3, h4⟩ := exists_log _ hu
  refine ⟨H, h1, (isKC_iff_commute H).2 (h4 _ ((isKC_iff_commute _).1 hk) ?_),
    fun a b => (norm_entry_le H a b).trans h2, h3⟩
  rw [Matrix.star_eq_conjTranspose, ← mat_inv_of_mem_Kc hk]
  exact (isKC_iff_commute _).1 ((Ksg p q).inv_mem hk)

end GlobalTheory.CartanInt.UnitLog
end
end

section

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching
open Formalism.MainNotions.PrimeDegreeVariant (embGL Interlace)
open scoped DirectSum

namespace GlobalTheory.Branching

theorem finrank_nablaSq_eq_card (K : Type) [Field K] (N : ℕ) (lam : DomWeight N) :
    Module.finrank K (nablaSq K N lam) = Nat.card (ssIdx N N lam.natW) := by
  obtain ⟨b, ⟨hli, hb, -⟩, -⟩ := sSBasis K N N lam.natW
  have : Finite (ssIdx N N lam.natW) := (sSIdxFinite N N _).to_subtype
  have := Fintype.ofFinite (ssIdx N N lam.natW)
  unfold nablaSq
  rw [← hb, finrank_span_eq_card hli, Nat.card_eq_fintype_card]

theorem finrank_le_finrank_directSum_below (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) :
    Module.finrank ℂ (nablaSq ℂ N lam) ≤ Module.finrank ℂ (⨁ mu : Below h lam, nablaSq ℂ n mu.1) := by
  obtain ⟨F, hF⟩ := GlobalTheory.Branching.exists_ssIdx_injective n N h lam
  have := Fintype.ofFinite (Below h lam)
  have : ∀ mu : Below h lam, Finite (ssIdx n n mu.1.natW) := fun mu => (sSIdxFinite n n _).to_subtype
  rw [Module.finrank_directSum, finrank_nablaSq_eq_card]
  simp only [finrank_nablaSq_eq_card]
  rw [← Nat.card_sigma]
  exact Nat.card_le_card_of_injective F hF

end GlobalTheory.Branching
end

section

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching
open Formalism.MainNotions.PrimeDegreeVariant (embGL Interlace)
open scoped DirectSum

namespace GlobalTheory.Branching

theorem zpow_mul_eq_iff_toNat (d x y : ℂ) (hd : d ≠ 0) (a b : ℤ) :
    d ^ a * x = d ^ b * y ↔ d ^ (a - b).toNat * x = d ^ (b - a).toNat * y := by
  have ha : d ^ a = d ^ (min a b) * d ^ (a - b).toNat := by
    rw [← zpow_natCast, ← zpow_add₀ hd]; congr 1; omega
  have hb : d ^ b = d ^ (min a b) * d ^ (b - a).toNat := by
    rw [← zpow_natCast, ← zpow_add₀ hd]; congr 1; omega
  rw [ha, hb, mul_assoc, mul_assoc, mul_right_inj' (zpow_ne_zero _ hd)]

theorem exists_coef_sqRep (n : ℕ) (mu : DomWeight n) (f : nablaSq ℂ n mu)
    (l : Module.Dual ℂ (nablaSq ℂ n mu)) :
    ∃ P : MvPolynomial (Fin n × Fin n) ℂ, ∀ g : GL (Fin n) ℂ,
      l (sqRep ℂ n mu g f) = (g : Matrix (Fin n) (Fin n) ℂ).det ^ mu.detShift *
        eval (fun x => (g : Matrix (Fin n) (Fin n) ℂ) x.1 x.2) P := by
  obtain ⟨L, hL⟩ := LinearMap.exists_extend l
  obtain ⟨P, hP⟩ := GlobalTheory.Branching.rowAct_coef_poly_and_unitary_dense.1 n n f L
  refine ⟨rename Prod.swap P, fun g => ?_⟩
  rw [← hL, LinearMap.comp_apply, Submodule.subtype_apply, sqRep_coe, sqAct, map_smul, hP, eval_rename]
  simp only [detPow, smul_eq_mul, Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply]
  rfl

theorem intertwining_gl_of_unitary (n : ℕ) (mu nu : DomWeight n)
    (φ : (smallRep (unitaryIncl n) mu).IntertwiningMap (smallRep (unitaryIncl n) nu))
    (g : GL (Fin n) ℂ) (f : nablaSq ℂ n mu) :
    φ (sqRep ℂ n mu g f) = sqRep ℂ n nu g (φ f) := by
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro l
  rw [map_sub, sub_eq_zero]
  obtain ⟨P, hP⟩ := exists_coef_sqRep n mu f (l ∘ₗ φ.toLinearMap)
  obtain ⟨Q, hQ⟩ := exists_coef_sqRep n nu (φ f) l
  let D : MvPolynomial (Fin n × Fin n) ℂ := (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ).det
  have hD : ∀ m : Matrix (Fin n) (Fin n) ℂ, eval (fun x => m x.1 x.2) D = m.det := by
    intro m
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp
  have key : ∀ g : GL (Fin n) ℂ, l (φ (sqRep ℂ n mu g f)) = l (sqRep ℂ n nu g (φ f)) ↔
      eval (fun x => (g : Matrix (Fin n) (Fin n) ℂ) x.1 x.2)
        (D ^ (mu.detShift - nu.detShift).toNat * P - D ^ (nu.detShift - mu.detShift).toNat * Q) = 0 := by
    intro g
    have h1 : l (φ (sqRep ℂ n mu g f)) = _ := hP g
    rw [h1, hQ, zpow_mul_eq_iff_toNat _ _ _ (Matrix.GeneralLinearGroup.det_ne_zero g)]
    simp only [map_sub, map_mul, map_pow, hD, sub_eq_zero]
  have hz := GlobalTheory.Branching.rowAct_coef_poly_and_unitary_dense.2 n _ fun u hu =>
    (key (unitaryIncl n ⟨u, hu⟩)).1 (congrArg l (φ.isIntertwining _ _ ⟨u, hu⟩ f))
  rw [key, hz, map_zero]

end GlobalTheory.Branching
end
