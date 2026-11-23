module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle005
public import Formalism.LocalToGlobal.HermitianForms.Bundle002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle256
public import Formalism.LocalRingCardinality.Bundle003
public import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocBases
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle009
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalLatticeFiltrationSizeProperties
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle123
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DeepRegionExponents
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle011
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle318
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle184
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingReindex
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle180
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle288
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle012
public import Formalism.FlagUnipotentLattices.CardSubmodulesAndLinearEquivBounds
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedFramesPerpendicularVectors
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle015
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.InfCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RankOneTensors
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle127
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BigCellChartDifferentialSkewAndFrobenius
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermOp
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle014
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle026
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle002
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff

@[expose] public section

section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G

theorem record_facts : ∀ (D : D7) (u : D.what₂.Word), SplitsIn D.host.E (D.mem u).A.T ∧ (∀ i, SplitsIn D.host.E (D.host.g i)) ∧ (∀ i, (D.mem u).A.T ≠ D.host.g i) ∧ Module.finrank ℚ D.host.E = 2 * D.R.f ∧ D.R.N 0 = D.R.k ∧ IsHerm (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) ∧ (gramN D 0 (Nat.zero_le _)).det ≠ 0 := by
  intro D u
  refine ⟨(GlobalTheory.HostSplit.split_of_one_mod D.R D.host _ (D.mem u).A.T_prime (D.T_mod_cond u)).1,
    D.nd.g_split, D.T_ne_g u, ?_, D.R.N_zero, ?_,
    (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D 0 (Nat.zero_le _)).ne_zero⟩
  · rw [D.host.finrank_cmField, Ranks.f, Ranks.n]
    ring
  · let _ := D.host.cmStar
    have h := D.sp.baseGram_isHermitian
    refine Matrix.ext fun i j => ?_
    exact congrFun (congrFun h (Fin.cast D.R.N_zero i)) (Fin.cast D.R.N_zero j)

end GlobalTheory.St.G
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.Deep GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.DeepFamilyGap

theorem one_mem_NA (I : AutInst) (W : Submodule I.E (Fin I.n → I.E)) : (1 : I.GA) ∈ I.NA W := by
  unfold AutInst.NA
  refine ⟨fun v => ?_, ?_⟩
  · have hdet : IsUnit (I.P v).det := by
      first
      | exact (Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v)
      | exact I.P_unit v
    have hg : I.P v * uMat ((1 : I.GA).1 v) * (I.P v)⁻¹ = 1 := by
      rw [show uMat ((1 : I.GA).1 v) = 1 from rfl, mul_one]
      exact Matrix.mul_nonsing_inv _ hdet
    rw [hg]
    unfold AutInst.InUnipRad
    simp
    intro x _
    unfold Formalism.UG.hform
    simp
  · have hf : I.fmat (1 : I.GA).2 = 1 := by
      first
      | rfl
      | simp
      | exact map_one _
    rw [hf]
    unfold AutInst.InUnipRad
    simp
    intro x _
    unfold Formalism.UG.hform
    simp

theorem self_mem_omega (I : AutInst) (x : I.GA) (W : Submodule I.E (Fin I.n → I.E)) {ρ : ℝ} (h : 0 ≤ ρ) :
    x ∈ omega I x W ρ := by
  refine ⟨rfl, fun _ => 0, fun _ => 0, fun v => ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie (I.ε v)).zero_mem,
    (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie (I.ε v)).zero_mem⟩, ?_, fun v => by simp, fun s t => ⟨1, ?_, fun v => ?_⟩⟩
  · simpa [GlobalTheory.SobolevBound.hs_eq_trace] using h
  · exact one_mem_NA I W
  · rw [smul_zero, smul_zero, NormedSpace.exp_zero, mul_one, mul_one]
    exact one_mul _

theorem beP_nonneg (n : ℕ) (b : ℝ) (P : ℕ) : 0 ≤ beP n b P := by
  unfold beP
  positivity

theorem monotone₂ (n : ℕ) (b : ℝ) {P Q : ℕ} (h : P ≤ Q) : beP n b P ≤ beP n b Q := by
  unfold beP
  have : (P : ℝ) ≤ Q := by exact_mod_cast h
  linarith

theorem iterate (B : RowsAut) (b ρ M β : ℝ) (P₀ : ℕ) (D : ℕ)
    (T : Fin D → (B.Hs →L[ℂ] B.I.L2 B.μf B.fund)) (Fr : Fin D → B.Hs → B.I.GA → ℂ) (x : B.I.GA)
    (W : Submodule B.I.E (Fin B.I.n → B.I.E)) (hg : 1 ≤ B.g) (hW : B.I.IsIsot W)
    (hcov : ∀ ν : B.I.Ginf, ((ν, 1) : B.I.GA) ∈ B.I.NA W → ∃ γ ∈ B.I.GFset, ∃ k ∈ B.I.Kg B.g,
      ∃ y ∈ omega B.I x W ρ, ((ν, 1) : B.I.GA) * x = γ * y * (1, k))
    (hS : ∀ P, StepBoundAt B b P) (hR : ∀ i, IsReps B (T i) (Fr i))
    (hC : ∀ i u, B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext (T i u))) (hρ : 0 ≤ ρ) (hM : 0 ≤ M)
    (hβ : beP B.I.n b P₀ ≤ β)
    (h0 : ∀ y ∈ omega B.I x W ρ, ∀ u ∈ VP B P₀, ‖vv B Fr u y‖ ≤ M * ‖u‖) :
    ∀ k P : ℕ, P + k = P₀ → ∀ y ∈ omega B.I x W ρ, ∀ u ∈ VP B P,
      ‖vv B Fr u y‖ ≤ (2 * ρ * Real.sqrt B.I.f * β) ^ k * M * ‖u‖ := by
  have hβ0 : 0 ≤ β := le_trans (beP_nonneg _ _ _) hβ
  have hc0 : 0 ≤ 2 * ρ * Real.sqrt B.I.f * β :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hρ) (Real.sqrt_nonneg _)) hβ0
  intro k
  induction k with
  | zero =>
    intro P hP y hy u hu
    have hPP : P = P₀ := by simpa using hP
    subst hPP
    simpa using h0 y hy u hu
  | succ k ih =>
    intro P hP y hy u hu
    have hP' : (P + 1) + k = P₀ := by omega
    have hM' : 0 ≤ (2 * ρ * Real.sqrt B.I.f * β) ^ k * M := mul_nonneg (pow_nonneg hc0 _) hM
    have key := GlobalTheory.DeepStep.step_bound B b ρ ((2 * ρ * Real.sqrt B.I.f * β) ^ k * M) P D T Fr x W hg hW
      hcov (hS P) hR hC hM' (ih (P + 1) hP') y hy u hu
    have hle : beP B.I.n b P ≤ β := le_trans (monotone₂ _ _ (by omega : P ≤ P₀)) hβ
    calc ‖vv B Fr u y‖
        ≤ 2 * ρ * Real.sqrt B.I.f * beP B.I.n b P * ((2 * ρ * Real.sqrt B.I.f * β) ^ k * M) * ‖u‖ := key
      _ ≤ 2 * ρ * Real.sqrt B.I.f * β * ((2 * ρ * Real.sqrt B.I.f * β) ^ k * M) * ‖u‖ := by
          gcongr
      _ = (2 * ρ * Real.sqrt B.I.f * β) ^ (k + 1) * M * ‖u‖ := by ring

theorem mult_le {n τ t : ℝ} (hn : 1 ≤ n) (hτ : 0 < τ) (hτ1 : τ < 1 / 2) (ht : τ / 2 ≤ t) :
    1 + 4 * Real.sqrt n / t ^ 2 ≤ 17 * Real.sqrt n / τ ^ 2 := by
  have hs : 1 ≤ Real.sqrt n := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hn
  have ht0 : 0 < t := by linarith
  have hτt : τ ^ 2 ≤ 4 * t ^ 2 := by nlinarith
  have h1 : 4 * Real.sqrt n / t ^ 2 ≤ 16 * Real.sqrt n / τ ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have h2 : 1 ≤ Real.sqrt n / τ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have h3 : 17 * Real.sqrt n / τ ^ 2 = 16 * Real.sqrt n / τ ^ 2 + Real.sqrt n / τ ^ 2 := by ring
  linarith

theorem deep_bound_family : ∀ (B : RowsAut) (Cg : ℝ) (n₀ : ℕ) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ) (c : InfinitePlace B.I.F → ℝ) (x : B.I.GA) (D : ℕ) (T : Fin D → (B.Hs →L[ℂ] B.I.L2 B.μf B.fund)) (Fr : Fin D → B.Hs → B.I.GA → ℂ), 8 ≤ n₀ → 1 ≤ q → CountHyp B Cg n₀ d p q b → (∀ v, IsGauge (B.I.ε v) (c v)) → least B.I x < tauStar B q b → (∀ i, IsReps B (T i) (Fr i)) → (∀ i u, ‖T i u‖ = ‖u‖) → (∀ i u, B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext (T i u))) → ‖vv B Fr (B.tens B.w) x‖ ^ 2 ≤ (2 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.radRh B q (least B.I x) * Real.sqrt B.I.f * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B)) ^ (16 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) * (6 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B)) ^ GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B * Real.exp B.I.f * (17 * Real.sqrt B.I.n / least B.I x ^ 2) ^ (2 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) * (D : ℝ) * (∏ v, c v) / (B.μf (B.I.Kg B.g)).toReal := by
  intro B Cg n₀ d p q b c x D T Fr hn₀ hq hCH hc hτ hR hiso hcusp
  obtain ⟨hDS, -, hn₀n, hq2, -, -, hb2, -, -, hg, -⟩ := id hCH
  obtain ⟨-, hrd, hf, -, -, -, hrk, -, -, -, -, htau, -⟩ :=
    GlobalTheory.Dec.countHyp_numerics B Cg n₀ d p q b hn₀ hCH
  obtain ⟨htau2, hb19⟩ := htau hq
  have hn8 : 8 ≤ B.I.n := le_trans hn₀ hn₀n
  have hn1 : 1 ≤ B.I.n := by omega
  have hτpos : 0 < least B.I x :=
    ((GlobalTheory.CountSteps.steps B.I x 1 one_pos).2.2.2.2.2.2.2.2 hn1).1
  have hτhalf : least B.I x < 1 / 2 := lt_trans hτ htau2
  have hτ1 : tau1 B.I x = least B.I x := min_eq_right hτhalf.le
  obtain ⟨W, hW, hcov⟩ := GlobalTheory.DeepCover.unipotent_orbit_cover B.I x B.g q hg hn1
    (fun v => (hrk v).le) hτhalf
  have hτX : least B.I x ≤ ((B.I.n : ℝ) * B.I.f * B.I.rd * B.g * b)⁻¹ ^ (11 * q) := hτ.le
  have hex := GlobalTheory.deep_region_exponents B.I.n B.I.f q B.I.rd B.g b (least B.I x) hn8 hf hq hq2 hrd hb2
    (by exact_mod_cast hg) hτpos hτX
  have hrho : GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.radRh B q (least B.I x) ≤ Real.log 2 := hex.1
  have hρ0 : 0 ≤ GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.radRh B q (least B.I x) := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.radRh
    have hg0 : (1 : ℝ) ≤ B.g := by exact_mod_cast hg
    exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
      (Real.sqrt_nonneg _)) (by linarith)) (by linarith)) (Real.rpow_nonneg (by linarith) _))
      (by norm_num)
  have hS : ∀ P, StepBoundAt B b P := GlobalTheory.T.discreteSeries_stepBound_of_countingHypotheses B Cg n₀ d p q b hn₀ hCH
  have hβ : beP B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + B.I.n ^ 2 * B.I.f) =
      GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) := rfl
  have hβ0 : 0 ≤ GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) := by
    rw [← hβ]; exact beP_nonneg _ _ _
  have hβle : beP B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) ≤
      GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) := by
    rw [← hβ]; exact monotone₂ _ _ (Nat.le_add_right _ _)
  have hc0 : 0 < ∏ v, c v := Finset.prod_pos fun v _ => GlobalTheory.SobolevBound.gauge_pos (hc v)
  have hN : B.I.n ^ 2 * B.I.f = GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B := rfl
  have hK0 : 0 ≤ (6 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B)) ^ GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B * Real.exp B.I.f * (17 * Real.sqrt B.I.n / least B.I x ^ 2) ^ (2 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) * (D : ℝ) * (∏ v, c v) / (B.μf (B.I.Kg B.g)).toReal :=
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (by linarith) _)
      (Real.exp_pos _).le) (pow_nonneg (by positivity) _)) (Nat.cast_nonneg _)) hc0.le)
      ENNReal.toReal_nonneg
  have h0 : ∀ y ∈ omega B.I x W (GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.radRh B q (least B.I x)),
      ∀ u ∈ VP B (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B), ‖vv B Fr u y‖ ≤
        Real.sqrt ((6 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B)) ^ GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B * Real.exp B.I.f * (17 * Real.sqrt B.I.n / least B.I x ^ 2) ^ (2 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) * (D : ℝ) * (∏ v, c v) / (B.μf (B.I.Kg B.g)).toReal) * ‖u‖ := by
    intro y hy u hu
    have hs := GlobalTheory.SobolevBound.sobolev_bound B b c (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) D T Fr hn8 hg hb19 hc hS
      hR hiso y u hu
    rw [hβ, hN] at hs
    have ht : least B.I x / 2 ≤ tau1 B.I y := by
      rw [← hτ1]; exact GlobalTheory.OmegaLeast.half_truncatedLeastLatticeSize_le_unipotentNeighbourhood B.I x W _ hn1 hrho y hy
    have hm := mult_le (n := (B.I.n : ℝ)) (by exact_mod_cast hn1) hτpos hτhalf ht
    have hle : ‖vv B Fr u y‖ ^ 2 ≤ ((6 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B)) ^ GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B * Real.exp B.I.f * (17 * Real.sqrt B.I.n / least B.I x ^ 2) ^ (2 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) * (D : ℝ) * (∏ v, c v) / (B.μf (B.I.Kg B.g)).toReal) * ‖u‖ ^ 2 := by
      refine hs.trans ?_
      gcongr
    have := Real.sqrt_le_sqrt hle
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul hK0, Real.sqrt_sq (norm_nonneg _)] at this
  have key := GlobalTheory.DeepFamilyGap.iterate B b (GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.radRh B q (least B.I x)) _ _
    (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) D T Fr x W hg hW hcov hS hR hcusp hρ0 (Real.sqrt_nonneg _) hβle h0
    (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) 0 (by simp) x (self_mem_omega B.I x W hρ0) (B.tens B.w)
    (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.tens_w_mem B hDS 0).1
  rw [(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.tens_w_mem B hDS 0).2, mul_one] at key
  have hA0 : 0 ≤ 2 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.radRh B q (least B.I x) * Real.sqrt B.I.f *
      GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hρ0) (Real.sqrt_nonneg _)) hβ0
  have hsq := pow_le_pow_left₀ (norm_nonneg _) key 2
  rw [mul_pow, ← pow_mul, Real.sq_sqrt hK0] at hsq
  refine hsq.trans (le_of_eq ?_)
  rw [show 8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B * 2 = 16 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B by ring]
  ring

end GlobalTheory.DeepFamilyGap
end
end

section

open scoped Classical ENNReal Pointwise NNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.measure_eq_of_strictFundamentalSetsPlacewise : ∀ (ι : Type) [Fintype ι] (k r : ℕ) (Γ Ω₁ Ω₂ : Set (ι → Formalism.QuantumDeterminants.Mt k r)),
    Γ.Countable → (fun _ => Matrix.of.symm 1) ∈ Γ → (∀ m ∈ Γ, ∀ m' ∈ Γ, GlobalTheory.DegVol.mulP m m' ∈ Γ) →
    (∀ m ∈ Γ, (fun v => Matrix.of.symm (Matrix.of (m v))⁻¹) ∈ Γ) →
    (∀ m ∈ Γ, ∀ v, Matrix.of (m v) ∈ Formalism.QuantumDeterminants.Nset k r) →
    GlobalTheory.DegVol.IsFund Γ (GlobalTheory.DegVol.RP k r (fun _ => 1)) Ω₁ → GlobalTheory.DegVol.IsFund Γ (GlobalTheory.DegVol.RP k r (fun _ => 1)) Ω₂ →
    Measure.pi (fun _ : ι => GlobalTheory.Amp.lebN k r) Ω₁ = Measure.pi (fun _ : ι => GlobalTheory.Amp.lebN k r) Ω₂ := by
  first | exact @GlobalTheory.FundEq.measure_eq | exact GlobalTheory.FundEq.measure_eq | (intros; apply GlobalTheory.FundEq.measure_eq <;> assumption)
end

section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.fixed_frames_perpendicular_vectors : ∀ (D : D7) (u u' : D.what₂.Word) (F0 : Fb D u) (Λ : LatV D), Stand D u u' → IsBase D u F0 → IsRowLat D F0 Λ → IsSplit D F0 Λ → ∀ (P : LatW D) (φ : P →ₗ[𝓞 D.host.E] (hS D).V) (Z : GramM D), (∀ p, φ p ∈ XLam Λ (lf D F0)) → P ≤ L0X D Λ (lf D F0) → ∀ F' ∈ FixSet D Λ (lf D F0) ((Tu D u' : ℕ) : D.host.E) Z P φ, ∃ w : Fin (D.R.rS + 1) → (D.sp.X 0).V, (∀ b, IsWcomp D P (frame F' b) (w b) ∧ w b ∈ dualInH (D.sp.X 0).hT (perpW D (L0X D Λ (lf D F0)) P)) ∧ ((Tu D u : ℕ) : D.host.E) * (D.sp.X 0).hT (∑ b, Formalism.HermitianLatticeCounting.LatticeSumBounds.cofVec (Z.submatrix Fin.castSucc id) b • w b) (∑ b, Formalism.HermitianLatticeCounting.LatticeSumBounds.cofVec (Z.submatrix Fin.castSucc id) b • w b) = Gmat D ((Tu D u : ℕ) : D.host.E) ((Tu D u' : ℕ) : D.host.E) Z := by
  first | exact @GlobalTheory.LoopC.WMem.main | exact GlobalTheory.LoopC.WMem.main | (intros; apply GlobalTheory.LoopC.WMem.main <;> assumption)
end

section

noncomputable section
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf
namespace GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem eqC_holds : EqC := by
  intro D X Y u t₁ t₂ h1 h2 h
  obtain ⟨l, m, l', m', c⟩ := t₁
  obtain ⟨l₂, m₂, l₂', m₂', c₂⟩ := t₂
  simp only at h1 h2
  subst h1 h2
  have hc : c = c₂ := by
    rw [← Quot.out_eq c, ← Quot.out_eq c₂]
    exact Quot.sound h
  subst hc
  rfl
end GlobalTheory.TypeAsm
end
end

section

noncomputable section
open scoped Classical ENNReal Pointwise
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full

namespace GlobalTheory.RowsOrb

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D)

def Wb : Submodule D.host.E (VS D).V where
  carrier := {v | ∀ a, (VS D).hT (X.eX a) v = 0 ∧ (VS D).hT (X.fY a) v = 0}
  add_mem' := by
    intro x y hx hy a
    exact ⟨by rw [map_add (f := _), (hx a).1, (hy a).1, add_zero], by rw [map_add (f := _), (hx a).2, (hy a).2, add_zero]⟩
  zero_mem' := fun a => ⟨map_zero _, map_zero _⟩
  smul_mem' := by
    intro c x hx a
    exact ⟨by rw [map_smul, (hx a).1, smul_zero], by rw [map_smul, (hx a).2, smul_zero]⟩

theorem mem_Wb (v : (VS D).V) : v ∈ Wb X ↔ ∀ a, (VS D).hT (X.eX a) v = 0 ∧ (VS D).hT (X.fY a) v = 0 := Iff.rfl

def hb : Wb X →ₗ⋆[D.host.E] Wb X →ₗ[D.host.E] D.host.E := GlobalTheory.Mass.hRes (VS D).hT (Wb X)

def zb (u : D.what₂.Word) : Wb X := ⟨X.zu u, fun a => X.zu_orth u a⟩

def Ub (u : D.what₂.Word) : Submodule D.host.E (Wb X) :=
  GlobalTheory.Mass.perp (hb X) (Submodule.span D.host.E {zb X u})

def hU (u : D.what₂.Word) : Ub X u →ₗ⋆[D.host.E] Ub X u →ₗ[D.host.E] D.host.E := GlobalTheory.Mass.hRes (hb X) (Ub X u)

def Lmap (u : D.what₂.Word) (Λ : Submodule (𝓞 D.host.E) (VS D).V) : Submodule (𝓞 D.host.E) (Wb X) :=
  GlobalTheory.Mass.latIn (Wb X) (Λ ⊔ GlobalTheory.HermLat.rs (𝓞 D.host.E) (GlobalTheory.TypeAsm.F0 X u).X)

abbrev Gz (u : D.what₂.Word) : Subgroup (Formalism.HermitianLatticesTheory.isom (hb X)) :=
  MulAction.stabilizer (Formalism.HermitianLatticesTheory.isom (hb X)) (zb X u)

theorem hb_apply (x y : Wb X) : hb X x y = (VS D).hT (x : (VS D).V) (y : (VS D).V) := rfl

theorem zb_coe (u : D.what₂.Word) : ((zb X u : Wb X) : (VS D).V) = X.zu u := rfl

theorem hU_apply (u : D.what₂.Word) (x y : Ub X u) :
    hU X u x y = (VS D).hT ((x : Wb X) : (VS D).V) ((y : Wb X) : (VS D).V) := rfl

theorem mem_Ub (u : D.what₂.Word) (x : Wb X) : x ∈ Ub X u ↔ (VS D).hT (X.zu u) (x : (VS D).V) = 0 := by
  unfold Ub GlobalTheory.Mass.perp
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro H
    exact H (zb X u) (Submodule.mem_span_singleton_self _)
  · intro H y hy
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hy
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply]
    change _ • (VS D).hT (X.zu u) (x : (VS D).V) = 0
    rw [H, smul_zero]

theorem mem_Lmap (u : D.what₂.Word) (Λ : Submodule (𝓞 D.host.E) (VS D).V) (w : Wb X) :
    w ∈ Lmap X u Λ ↔ (w : (VS D).V) ∈ Λ ⊔ GlobalTheory.HermLat.rs (𝓞 D.host.E) (GlobalTheory.TypeAsm.F0 X u).X := Iff.rfl

end GlobalTheory.RowsOrb
end
end

section

noncomputable section

open scoped Classical InnerProductSpace
open MeasureTheory NumberField Formalism.BasicNotions

namespace GlobalTheory.TensHS

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hsNormSq_eq_sum_std {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup V']
    [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V'] (A : V' →L[ℂ] V) :
    Formalism.MainNotions.S.hsNormSq A = Formalism.L2.SG.RealObj.hs2 A := by
  unfold Formalism.MainNotions.S.hsNormSq Formalism.MainNotions.S.hsInner Formalism.L2.SG.RealObj.hs2
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_self_eq_norm_sq_to_K]
  norm_cast

theorem hsNormSq_of_tens {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word)
    (A : X.Vpi u' →L[ℂ] X.Vpi u) (J : ∀ v, X.Vloc u' v →L[ℂ] X.Vloc u v)
    (hA : ∀ y, A (X.tensU u' y) = X.tensU u (fun v => J v (y v))) :
    Formalism.MainNotions.S.hsNormSq A = ∏ v, Formalism.MainNotions.S.hsNormSq (J v) := by
  obtain ⟨hon, hsp⟩ := Formalism.L2.SG.RealObj.EnergyCut.tens_onb X u'
  let B := OrthonormalBasis.mk hon hsp
  have hB : ∀ i, B i = X.tensU u' (fun v => stdOrthonormalBasis ℂ (X.Vloc u' v) (i v)) := fun i => by simp [B]
  rw [hsNormSq_eq_sum_std]
  simp only [hsNormSq_eq_sum_std]
  unfold Formalism.L2.SG.RealObj.hs2
  rw [Formalism.L2.SG.RealObj.InfCut.hsb_indep (stdOrthonormalBasis ℂ (X.Vpi u')) B]
  simp only [hB, hA, Formalism.L2.SG.RealObj.RankOneTensors.norm_tens (X.tensU u) (X.tensU_inner u), ← Finset.prod_pow]
  rw [Fintype.prod_sum]

theorem hsNormSq_nonneg {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup V']
    [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V'] (A : V' →L[ℂ] V) : 0 ≤ Formalism.MainNotions.S.hsNormSq A := by
  rw [hsNormSq_eq_sum_std]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

theorem tensC_holds : GlobalTheory.TypeAsm.TensC := by
  intro D X u γ νl hσ
  haveI := FiniteDimensional.complete ℂ (X.Vpi u)
  haveI : ∀ v, CompleteSpace (X.Vloc u v) := fun v => FiniteDimensional.complete ℂ (X.Vloc u v)
  haveI := hσ
  have hWc : Continuous (X.Wu u) := (X.Wu_spec u).2.2.1
  have hfac : ∀ y, (Formalism.L2.SG.TermOp.OO (Measure.pi νl) Set.univ (X.Wu u) (X.Wu u) γ) (X.tensU u y) =
      X.tensU u (fun v => (Formalism.L2.SG.RealObj.Jv (νl v) (X.Wloc u v) (X.Wloc u v) (γ v)) (y v)) := by
    intro y
    have h := Formalism.L2.SG.RealObj.RankOneTensors.oo_factor νl (X.tensU u) (X.tensU u) (X.tensU_inner u)
      (X.tensU_inner u) (X.tensU_span u) (X.Wloc u) (X.Wloc u) (X.Wloc_cont u) (X.Wloc_cont u)
      (X.Wu u) (X.Wu u) hWc hWc (X.Wu_tens u) (X.Wu_tens u) γ y
    simpa only [Formalism.L2.SG.RealObj.Jv, Formalism.L2.SG.TermOp.OO, Measure.restrict_univ] using h
  have hhs := hsNormSq_of_tens X u u _ _ hfac
  have hn := Formalism.L2.SG.PackageTie.norm_hsEmb_sq
    (Formalism.L2.SG.TermOp.OO (Measure.pi νl) Set.univ (X.Wu u) (X.Wu u) γ)
  refine le_of_eq ?_
  rw [← Real.sqrt_sq (norm_nonneg _), hn, hhs]
  have hprod : ∏ v, Formalism.MainNotions.S.hsNormSq (Formalism.L2.SG.RealObj.Jv (νl v) (X.Wloc u v) (X.Wloc u v) (γ v)) =
      (∏ v, Real.sqrt (Formalism.MainNotions.S.hsNormSq (Formalism.L2.SG.RealObj.Jv (νl v) (X.Wloc u v) (X.Wloc u v) (γ v)))) ^ 2 := by
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl fun v _ => (Real.sq_sqrt (hsNormSq_nonneg _)).symm
  rw [hprod, Real.sqrt_sq (Finset.prod_nonneg fun v _ => Real.sqrt_nonneg _)]

end GlobalTheory.TensHS
end
end

section

noncomputable section
open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
namespace GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem fundC_holds : FundC := by
  intro D X Y u t
  obtain ⟨K, hK⟩ : ∃ Ω, IsSFund X.B.I (ROinf t) Ω := Formalism.L2.SG.Pf.fundExistsC_holds D X Y u u t
  set Γ0 := Formalism.L2.SG.Pf.ROsub X (X.Fu u) (X.Fu u) t.lam t.lam' t.lin with hΓ0
  refine ⟨K, hK.1, fun r _ => ?_⟩
  obtain ⟨s0, hs0, hs0F⟩ := hK.2.1 r
  refine ⟨s0, ⟨hs0, hs0F⟩, fun s' ⟨hs', hs'F⟩ => ?_⟩
  have h2 : (s0 * s'⁻¹) * (s' * r) ∈ K := by simpa [mul_assoc] using hs0F
  have := hK.2.2 _ hs'F _ (Γ0.mul_mem hs0 (Γ0.inv_mem hs')) h2
  exact (mul_inv_eq_one.1 this).symm

end GlobalTheory.TypeAsm
end
end

section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.CellDens
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.bigCellChartDifferential_skew_and_frobenius : ∀ (k r : ℕ) (v : EE k r), ((dchart k r v)ᴴ * Hpk k r + Hpk k r * dchart k r v = 0) ∧ (∑ i, ∑ j, ‖dchart k r v i j‖ ^ 2) = ‖v.1.1‖ ^ 2 + ‖v.1.2‖ ^ 2 + 2 * (∑ a, ‖v.2.1 a‖ ^ 2) + ‖v.2.2‖ ^ 2 := by
  first | exact @GlobalTheory.CellDens.DNorm.dchart_skew_norm | exact GlobalTheory.CellDens.DNorm.dchart_skew_norm | (intros; apply GlobalTheory.CellDens.DNorm.dchart_skew_norm <;> assumption)
end
