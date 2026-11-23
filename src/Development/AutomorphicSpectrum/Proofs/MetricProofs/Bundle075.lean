module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle013
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ThetaDerivativeBound
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ThetaFunctionSupBound
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.TorsionValueNormEqThetaNorm
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle038
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle043
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle067
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle065
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle061
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle064
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle068
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle063
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsHorizontalTwist
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle070
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle071
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle073
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle037
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentModulusMatrix
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle002
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

theorem _root_.GlobalTheory.T.theta_derivative_bound : ∀ {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {P : RigLB G} {z : Sp ℂ ⟶ S} {g : ℕ} (a : ArchFrame P z g), (∀ l l' : a.u.Λ, ∃ k : ℤ, (a.herm l l').im = k) → (∀ w : Fin g → ℂ, (∀ l : a.u.Λ, ∃ k : ℤ, (a.herm w l).im = k) → w ∈ a.u.Λ) → (∀ l l' : a.u.Λ, a.χ (l + l') = a.χ l * a.χ l' * Complex.exp (Real.pi * Complex.I * (a.herm l l').im)) → ∀ (θ : (Fin g → ℂ) → ℂ) (v : Fin g → ℂ) (n' i : ℕ), a.IsTheta 1 θ → θ ≠ 0 → v ≠ 0 → i ≤ n' → ∃ F, a.IsTheta (3 * n') F ∧ (∀ k < i, iteratedDeriv k (fun τ : ℂ => F (τ • v)) 0 = 0) ∧ iteratedDeriv i (fun τ : ℂ => F (τ • v)) 0 ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.Jump.lefschetz_direction | exact GlobalTheory.CompanionTheory.Ar.Sl.Jump.lefschetz_direction | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.Jump.lefschetz_direction <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

theorem _root_.GlobalTheory.T.theta_function_sup_bound : ∀ {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {P : RigLB G} {z : Sp ℂ ⟶ S} {g : ℕ} (a : ArchFrame P z g), (∀ l l' : a.u.Λ, ∃ k : ℤ, (a.herm l l').im = k) → (∀ w : Fin g → ℂ, (∀ l : a.u.Λ, ∃ k : ℤ, (a.herm w l).im = k) → w ∈ a.u.Λ) → (∀ l l' : a.u.Λ, a.χ (l + l') = a.χ l * a.χ l' * Complex.exp (Real.pi * Complex.I * (a.herm l l').im)) → ∀ (m : ℕ) (θ : (Fin g → ℂ) → ℂ) (Ix : Type) [Fintype Ix] (r : Ix → Fin g → ℂ) (f : Ix → (Fin g → ℂ) → ℂ), 1 ≤ m → a.IsTheta 1 θ → θ ≠ 0 → (∀ w : Fin g → ℂ, (m : ℂ) • w ∈ a.u.Λ → ∃ i, w - r i ∈ a.u.Λ) → (∀ i, (m : ℂ) • r i ∈ a.u.Λ) → (∀ i, a.IsTheta (m ^ 2) (f i)) → (∀ i (w : Fin g → ℂ) (N : ℕ), 1 ≤ N → (N : ℂ) • w ∈ a.u.Λ → a.nrm (m ^ 2) (f i) w = a.nrm 1 θ (r i + (m : ℂ) • w)) → (∀ i w, a.nrm (m ^ 2) (f i) w = a.nrm 1 θ (r i + (m : ℂ) • w)) ∧ ∀ F, a.IsTheta (m ^ 2) F → ∃ c : Ix → ℂ, F = ∑ i, c i • f i := by
  first | exact @GlobalTheory.CompanionTheory.ThetaSpan.theta_span | exact GlobalTheory.CompanionTheory.ThetaSpan.theta_span | (intros; apply GlobalTheory.CompanionTheory.ThetaSpan.theta_span <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

theorem _root_.GlobalTheory.T.torsion_value_norm_eq_theta_norm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (σ : L →+* ℂ) (a : D.Frame σ) (n : ℕ) (s : Out.H0 D.t.PP.L n) (θ : (Fin D.g → ℂ) → ℂ) (y : Over.mk (emb σ) ⟶ D.t.G) (w : Fin D.g → ℂ) (N : ℕ) (T : ℂ), a.IsFn s θ → y.left = a.pt w → TorsVal D.t.PP s y N T → ‖T‖ = a.nrm n θ w ^ (N ^ 2) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.TorsArch.torsVal_norm | exact GlobalTheory.CompanionTheory.Ar.Sl.TorsArch.torsVal_norm | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.TorsArch.torsVal_norm <;> assumption)
end

section

open Matrix Metric GroundTheory.Heights₂.Heights.Regular GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.period_matrix_local_trivialization : ∀ (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L : LogPeriods n a g Λ), ∃ (Q : PeriodPolydisc n a g) (A : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ), (∀ i j, DifferentiableOn ℂ (fun z => A z i j) (ball 0 1)) ∧ (A 0).det ≠ 0 ∧ ∀ w ∈ logCover L.a_le, A (expCover a w) * L.H (expCover a w) * (A (expCover a w))ᴴ = (((Q.τ w).map Complex.im)⁻¹).map Complex.ofReal := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_periodPolydisc_frame | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_periodPolydisc_frame | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_periodPolydisc_frame <;> assumption)
end

section

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)


theorem _root_.GlobalTheory.T.zeroSet_chartIdeal_eq_chartSet : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k),
    IsMultiHomogIdeal Q →
    GroundTheory.Heights₂.Heights.ComplexSets.zeroSet (GlobalTheory.CompanionTheory.Ar.Pub.CxChart.chartIdeal (conePts Q) σ i) =
      chartSet (conePts Q) σ i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.CxChart.zeroSet_chartIdeal_conePts | exact GlobalTheory.CompanionTheory.Ar.Pub.CxChart.zeroSet_chartIdeal_conePts | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.CxChart.zeroSet_chartIdeal_conePts <;> assumption)
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ

theorem _root_.GlobalTheory.T.ball_domain_iff_pos_def : ∀ {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' n g : ℕ} (e : Ix Ψ j j' ≃ Fin g) (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ), t ∈ ballDom q ↔ (1 - (bigZe e q t)ᴴ * bigZe e q t).PosDef := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Univ.mem_ballDom_iff_posDef_bigZe | exact GlobalTheory.CompanionTheory.Ar.Cusp.Univ.mem_ballDom_iff_posDef_bigZe | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Univ.mem_ballDom_iff_posDef_bigZe <;> assumption)
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder


theorem _root_.GlobalTheory.T.adapted_frame_ball_coordinate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (R : RiemLat E g Λ) (A A₀ : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ) (τ : Ψ) (W : Matrix (Fin j') (Fin j) ℂ), (∀ u : Matrix (Sg j j') (Sg j j') ℂ, IsSgU u → IsUnit u.toBlocks₁₁.det ∧ IsUnit u.toBlocks₂₂.det ∧ (1 - moebW u 0 * (moebW u 0)ᴴ) * (u.toBlocks₂₂ * u.toBlocks₂₂ᴴ) = 1 ∧ (1 - moebW u 0 * (moebW u 0)ᴴ).PosDef) → (∀ x y : Fin j' → ℂ, R.ip (C.pPart R τ (A τ *ᵥ Sum.elim 0 x)) (C.pPart R τ (A τ *ᵥ Sum.elim 0 y)) = ((2 * C.c : ℝ) : ℂ) * (star x ⬝ᵥ y)) → C.IsAdapted R A → (A₀ τ)ᴴ * C.sgr τ * A₀ τ = sgI j j' → W = moebW (C.cinv (A₀ τ) τ * A τ) 0 → (∀ v : Fin j → ℂ, C.pPart R τ (A₀ τ *ᵥ Sum.elim v (W *ᵥ v)) = 0) ∧ R.gram (fun b : Fin j' => C.pPart R τ (A₀ τ *ᵥ Sum.elim 0 (Pi.single b 1))) * (1 - W * Wᴴ) = ((2 * C.c : ℝ) : ℂ) • (1 : Matrix (Fin j') (Fin j') ℂ) ∧ (1 - W * Wᴴ).PosDef := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.point_graph_gram | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.point_graph_gram | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.point_graph_gram <;> assumption)
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatEmbEx

theorem zero_mem_ballDom {Ψ : Type} [Fintype Ψ] {j j' n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n) : (0 : Fin n → ℂ) ∈ ballDom q := by
  intro τ
  have : ballMat q 0 τ = 0 := by ext a b; simp [ballMat]
  rw [this]
  simpa using Matrix.PosDef.one

theorem trace_zero_of_int {E : Type} [Field E] [NumberField E] (w : E)
    (hw : ∀ a : 𝓞 E, Algebra.trace ℚ E ((a : E) * w) = 0) : w = 0 := by
  have nd := traceForm_nondegenerate ℚ E
  apply nd.1
  intro a
  have halg : IsAlgebraic ℤ a :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic a)
  obtain ⟨n, hn, hint⟩ := halg.exists_integral_multiple
  have h1 : Algebra.trace ℚ E ((n • a) * w) = 0 := hw ⟨n • a, hint⟩
  have hnq : ((n : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hn
  have h2 : (n • a) * w = ((n : ℚ)) • (w * a) := by
    rw [← Int.cast_smul_eq_zsmul ℚ n a, smul_mul_assoc, mul_comm a w]
  rw [h2, map_smul, smul_eq_mul] at h1
  rw [Algebra.traceForm_apply]
  exact (mul_eq_zero.1 h1).resolve_left hnq

theorem exists_latEmb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (_H : Host E) (F : UnivFam E Ψ j j' n g Λ), Nonempty (LatEmb F) := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ H F
  have h0 : (0 : Fin n → ℂ) ∈ ballDom F.q := zero_mem_ballDom F.q
  obtain ⟨R, hR⟩ : ∃ R, R = F.R 0 := ⟨_, rfl⟩
  have := R.free
  have := R.fin
  have hform : R.form = F.form := by rw [hR]; exact F.form_eq 0
  have hrk := GlobalTheory.T.CM_field_degree_eq_twice_card E Ψ F.σ F.cm
  have hg := GlobalTheory.T.genus_eq_card_mul_signature E Ψ g j j' R.B F.σ F.cm (by rw [hR]; exact F.sig 0 h0)
  obtain ⟨N, hN, e, einj, esmul, hspan⟩ := GlobalTheory.T.lattice_rational_embedding E Λ
  have hpos : 0 < Module.finrank ℚ E := Module.finrank_pos
  have hNj : N = j + j' := by
    rw [R.rank, hrk, hg] at hN
    have hc : 0 < Fintype.card Ψ := by omega
    have : Fintype.card Ψ * N = Fintype.card Ψ * (j + j') := by nlinarith
    exact Nat.eq_of_mul_eq_mul_left hc this
  subst hNj
  have hunim : Function.Bijective F.form := hform ▸ R.unimod
  have halt : ∀ x, F.form x x = 0 := fun x => by rw [← hform]; exact R.alt x
  have hadj : ∀ a a' : 𝓞 E, (a' : E) = IsCMField.complexConj E (a : E) → ∀ x y, F.form (a • x) y = F.form x (a' • y) := by
    rw [← hform]; exact R.adj
  obtain ⟨B, hBe, hBadj, hBskew, hBnd⟩ := GlobalTheory.T.alternating_form_hermitian_descent E Λ (j + j') e einj esmul hspan F.form halt hunim hadj
  obtain ⟨h, m, hm, hmaster, hint⟩ := GlobalTheory.T.skew_hermitian_form_exists E H Λ (j + j') e B hBadj hBskew hBnd
  have hdual := GlobalTheory.T.alternating_form_lattice_compatible E H Λ (j + j') e einj F.form hunim B hBe hBskew hBnd hspan h m hm hmaster
  have hrt : (H.rt : E) ≠ 0 := by
    intro h0
    have h1 : ((H.rt ^ 2 : 𝓞 E) : E) = ((-(H.d : 𝓞 E) : 𝓞 E) : E) := by rw [H.rt_sq]
    have hd : H.d ≠ 0 := H.d_prime.ne_zero
    simp [h0] at h1
    exact hd h1
  have hxi : ((m : E) * (H.rt : E))⁻¹ ≠ 0 := inv_ne_zero (mul_ne_zero (by exact_mod_cast hm) hrt)
  choose eps heps hxieq using fun τ => GlobalTheory.T.embedding_inverse_root_imaginary E H (F.σ τ) m hm
  have hmat : ∀ x y, ((F.form x y : ℤ) : ℚ) = Algebra.trace ℚ E (((m : E) * (H.rt : E))⁻¹ * h.toSesq (e y) (e x)) := by
    intro x y
    have := hmaster 1 (e x) (e y)
    rw [one_mul, one_smul] at this
    rw [this, hBe]
  let lam : Module.Basis (Fin (2 * g)) ℤ Λ := (Module.finBasisOfFinrankEq ℤ Λ R.rank)
  obtain ⟨bas, hbas⟩ := GlobalTheory.T.real_basis_from_lattice_basis E Ψ g (j + j') F.σ F.cm hg Λ e hspan lam
  have hlat : IsLattice E e.range := by
    refine ⟨?_, ?_, ?_⟩
    · rintro a _ ⟨x, rfl⟩
      exact ⟨a • x, esmul a x⟩
    · have : AddGroup.FG Λ := Module.Finite.iff_addGroup_fg.1 inferInstance
      exact (AddGroup.fg_iff_addSubgroup_fg _).1 (inferInstance : AddGroup.FG e.range)
    · rw [eq_top_iff]
      intro v _
      obtain ⟨k, x, hk, hx⟩ := hspan v
      have hk' : (k : E) ≠ 0 := by exact_mod_cast hk
      have : v = (k : E)⁻¹ • e x := by
        rw [hx, Nat.cast_smul_eq_nsmul E k v |>.symm, smul_smul, inv_mul_cancel₀ hk', one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
  have hintegral : IsIntegralOn h e.range := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    exact hint x y
  have hDI : IsDIntegral h (e.range.relIndex (GroundTheory.Heights₂.Heights.FiniteCovolume.dualLattice h e.range)) e.range := ⟨hlat, hintegral, hdual, le_rfl⟩
  have horth : ∀ x y, h.toSesq (e x) (e y) = 0 ↔ ∀ a : 𝓞 E, F.form (a • x) y = 0 := by
    intro x y
    have hsw : h.toSesq (e x) (e y) = 0 ↔ h.toSesq (e y) (e x) = 0 := by
      constructor
      · intro h1
        have h2 := h.isSymm.eq (e x) (e y)
        rw [h1] at h2
        simpa using h2.symm
      · intro h1
        have h2 := h.isSymm.eq (e y) (e x)
        rw [h1] at h2
        simpa using h2.symm
    have hfa : ∀ a : 𝓞 E, ((F.form (a • x) y : ℤ) : ℚ) = Algebra.trace ℚ E ((a : E) * (((m : E) * (H.rt : E))⁻¹ * h.toSesq (e y) (e x))) := by
      intro a
      rw [hmaster (a : E) (e x) (e y), ← hBe, esmul]
    rw [hsw]
    constructor
    · intro h1 a
      have := hfa a
      rw [h1, mul_zero, mul_zero, map_zero] at this
      exact_mod_cast this
    · intro h1
      have : ((m : E) * (H.rt : E))⁻¹ * h.toSesq (e y) (e x) = 0 := by
        apply trace_zero_of_int
        intro a
        rw [← hfa a, h1 a]
        simp
      exact (mul_eq_zero.1 this).resolve_left hxi
  have hcpos : 0 < 1 / ((m : ℝ) * Real.sqrt H.d) := by
    have h1 : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
    have h2 : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    positivity
  exact ⟨{ h := h, e := e, e_inj := einj, e_smul := esmul, Dn := _, integral := hDI, orth := horth,
           xi := ((m : E) * (H.rt : E))⁻¹, c := 1 / ((m : ℝ) * Real.sqrt H.d), c_pos := hcpos, eps := eps, eps_sq := heps,
           xi_eq := hxieq, form_eq := hmat, lam := lam, bas := bas, bas_eq := hbas }⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatEmbEx
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw

theorem _root_.GlobalTheory.T.ptsIntegral_conjLine_eq : PtsIndepStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Q : Ideal (MRing ι)) (e : ℕ) (L : Fin e → HermLine ι) (A : HermLine ι) (s : MRing ι), IsArithVar Q (e + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSectionOn Q A s → ptsIntegral Q (pot fun j => conjLine (L j)) (logNorm (conjLine A) s) = ptsIntegral Q (pot L) (logNorm A s) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Tw.ptsIntegral_conjLine | exact GlobalTheory.CompanionTheory.Ar.Tw.ptsIntegral_conjLine | (intros; apply GlobalTheory.CompanionTheory.Ar.Tw.ptsIntegral_conjLine <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW.TorusAct

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

noncomputable def scaleT (c : K → ℂ) : MvPolynomial K ℂ →ₐ[ℂ] MvPolynomial K ℂ :=
  aeval fun k => C (c k) * X k

omit [Fintype K] in
theorem scaleT_inv_scaleT (c : K → ℂ) (hc : ∀ k, c k ≠ 0) (f : MvPolynomial K ℂ) :
    scaleT (fun k => (c k)⁻¹) (scaleT c f) = f := by
  have h : (scaleT (fun k => (c k)⁻¹)).comp (scaleT c) = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    intro k
    simp only [scaleT, AlgHom.comp_apply, aeval_X, map_mul, algHom_C, AlgHom.id_apply]
    rw [← mul_assoc, algebraMap_eq, ← C_mul, mul_inv_cancel₀ (hc k), C_1, one_mul]
  exact DFunLike.congr_fun h f


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem mConeMap_torus (c : K → ℂ) (z : (Σ k, ι k) → ℂ) (f : MRing ι) :
    mConeMap (fun q : Σ k, ι k => c q.1 * z q) f = scaleT c (mConeMap z f) := by
  have h : mConeMap (fun q : Σ k, ι k => c q.1 * z q) =
      ((scaleT c).restrictScalars ℤ).comp (mConeMap z) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp only [mConeMap, scaleT, AlgHom.comp_apply, aeval_X, AlgHom.restrictScalars_apply, map_mul,
      algHom_C, algebraMap_eq, mul_assoc]
    rw [mul_left_comm]
  rw [h]
  rfl


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem mCoordIdeal_torus (c : K → ℂ) (hc : ∀ k, c k ≠ 0) (z : (Σ k, ι k) → ℂ) :
    mCoordIdeal (fun q : Σ k, ι k => c q.1 * z q) = mCoordIdeal z := by
  ext f
  rw [mCoordIdeal, mCoordIdeal, RingHom.mem_ker, RingHom.mem_ker, mConeMap_torus]
  constructor
  · intro h
    have := congrArg (scaleT fun k => (c k)⁻¹) h
    rwa [scaleT_inv_scaleT c hc, map_zero] at this
  · intro h
    rw [h, map_zero]

theorem isValueAt_torus {x : (Σ k, ι k) → Ω} {s : Ω} {z : (Σ k, ι k) → ℂ} {v : ℂ} (c : K → ℂ)
    (hc : ∀ k, c k ≠ 0) (hv : IsValueAt x s z v) :
    IsValueAt x s (fun q : Σ k, ι k => c q.1 * z q) v := by
  obtain ⟨d, g, h, hg, hh, hy, he, h0, rfl⟩ := hv
  have hu : (∏ k, c k ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)
  refine ⟨d, g, h, hg, hh, hy, he, ?_, ?_⟩
  · rw [eval_smul_homog h d hh]
    exact mul_ne_zero hu h0
  · rw [eval_smul_homog g d hg, eval_smul_homog h d hh, mul_div_mul_left _ _ hu]

theorem isValueAt_of_torus {x : (Σ k, ι k) → Ω} {s : Ω} {z : (Σ k, ι k) → ℂ} {v : ℂ} (c : K → ℂ)
    (hc : ∀ k, c k ≠ 0) (hv : IsValueAt x s (fun q : Σ k, ι k => c q.1 * z q) v) :
    IsValueAt x s z v := by
  have h := isValueAt_torus (fun k => (c k)⁻¹) (fun k => inv_ne_zero (hc k)) hv
  have e : (fun q : Σ k, ι k => (c q.1)⁻¹ * (c q.1 * z q)) = z := by
    funext q
    exact inv_mul_cancel_left₀ (hc q.1) _
  rwa [e] at h

theorem valAt_torus {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (c : K → ℂ) (hc : ∀ k, c k ≠ 0)
    (hz : z ∈ mcPts (mCoordIdeal x))
    (hcz : (fun q : Σ k, ι k => c q.1 * z q) ∈ mcPts (mCoordIdeal x)) (s : Ω) :
    valAt x s (fun q : Σ k, ι k => c q.1 * z q) = valAt x s z := by
  by_cases h : ∃ v, IsValueAt x s z v
  · obtain ⟨v, hv⟩ := h
    rw [valAt_eq hz hv, valAt_eq hcz (isValueAt_torus c hc hv)]
  · have h' : ¬ ∃ v, IsValueAt x s (fun q : Σ k, ι k => c q.1 * z q) v :=
      fun ⟨v, hv⟩ => h ⟨v, isValueAt_of_torus c hc hv⟩
    rw [valAt, valAt, dite_eq_right h, dite_eq_right h']

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (x : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) (c : K → ℂ), (∀ k, c k ≠ 0) →
    mCoordIdeal (fun q : Σ k, ι k => c q.1 * z q) = mCoordIdeal z ∧
      (z ∈ mcPts (mCoordIdeal x) → (fun q : Σ k, ι k => c q.1 * z q) ∈ mcPts (mCoordIdeal x) ∧
        ∀ s : Ω, valAt x s (fun q : Σ k, ι k => c q.1 * z q) = valAt x s z) := by
  intro K _ ι _ Ω _ x z c hc
  refine ⟨mCoordIdeal_torus c hc z, fun hz => ?_⟩
  have hcz := mcPts_smul (CoordinateConeArithVar.isMultiHomogIdeal x) c hc hz
  exact ⟨hcz, valAt_torus c hc hz hcz⟩

end GlobalTheory.CompanionTheory.Ar.PB.StepW.TorusAct
end

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.integral_fibre_sum_change_of_variables : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) (q : X → Fin e → ℂ) (S : Set X) (G : X → ℝ), (∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S) = 0) → (∀ x ∉ S, ∀ j, x ∈ (A.chart j).source → AnalyticAt ℂ (q ∘ (A.chart j).symm) (A.chart j x) ∧ LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) (A.chart j x) : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0) → (∀ y, (q ⁻¹' {y} \ S).Finite) → (∀ x ∉ S, ∀ i k, x ∈ (A.chart k).source → ContDiffAt ℝ 2 ((Φ i).φ x ∘ (A.chart k).symm) (A.chart k x)) → MIntegrable A Φ G → Integrable (fun y => ∑ᶠ x ∈ q ⁻¹' {y} \ S, G x * pushDens A Φ q x) ∧ mInt A Φ G = ∫ y, ∑ᶠ x ∈ q ⁻¹' {y} \ S, G x * pushDens A Φ q x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.Push.integrable_mInt_fibreSum | exact GlobalTheory.CompanionTheory.Ar.Giv.Push.integrable_mInt_fibreSum | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.Push.integrable_mInt_fibreSum <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.finite_fibres_of_analytic_local_diffeo : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) (q : X → Fin e → ℂ) (S : Set X) (G : X → ℝ), (∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S) = 0) → (∀ x ∉ S, ∀ j, x ∈ (A.chart j).source → AnalyticAt ℂ (q ∘ (A.chart j).symm) (A.chart j x) ∧ LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) (A.chart j x) : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0) → (∀ y, (q ⁻¹' {y} \ S).Finite) → (∀ x ∉ S, ∀ i k, x ∈ (A.chart k).source → ContDiffAt ℝ 2 ((Φ i).φ x ∘ (A.chart k).symm) (A.chart k x)) → (∀ j, AEStronglyMeasurable (fun u => G ((A.chart j).symm u) * locDens A Φ j u) (volume.restrict (A.chart j).target)) → ∀ Pt : ChartPartition A, ∫⁻ y, ENNReal.ofReal (∑ᶠ x ∈ q ⁻¹' {y} \ S, |G x * pushDens A Φ q x|) = ∑ j, ∫⁻ u in (A.chart j).target, ENNReal.ofReal |Pt.χ j ((A.chart j).symm u) * G ((A.chart j).symm u) * locDens A Φ j u| := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.Push.lintegral_absFibre_eq | exact GlobalTheory.CompanionTheory.Ar.Giv.Push.lintegral_absFibre_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.Push.lintegral_absFibre_eq <;> assumption)
end
