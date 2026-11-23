module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle101
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle123
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle134
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle103
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.FiniteEtaleSurjectiveOfPullback
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle078
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle152
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle162
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle154
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle161
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle129
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle121
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle122
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle128
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.MemMCoordIdealOfAevalEqZero
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Bundle001
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogPeriodStatement
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001

@[expose] public section

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.NormFib

theorem shear_mul {N : ℕ} {ca cb : Fin N} (hne : ca ≠ cb) (s t : ℂ) :
    (1 + Matrix.single cb ca s : Matrix (Fin N) (Fin N) ℂ) * (1 + Matrix.single cb ca t) =
      1 + Matrix.single cb ca (s + t) := by
  rw [mul_add, add_mul, add_mul, one_mul, mul_one, one_mul, Matrix.single_mul_single_of_ne _ _ _ _ hne,
    Matrix.single_add]
  abel

theorem logNorm_add_weights_eq_logSin : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (k₀ : K), M.blk (τ, a) = some k₀ → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (q : Fin 2 → RW.X → FA.S.X), (∀ x x₀, FA.Re.π x₀ = q 0 x → SameOrbit (FA.Re.R.lift x₀ x₀) (fstPt k₀ (RW.lift x x))) → (∀ x x₀, FA.Re.π x₀ = q 1 x → SameOrbit (FA.Re.R.lift x₀ x₀) (sndPt k₀ (RW.lift x x))) → ∀ f : RW.X → ℝ, IsNormFn M τ a k₀ ca cb RW f → ∀ (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → RW.X) (l : Fin BM.q) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → IsFibreData FA τ a ca cb q Un Gn ΦYn ΦWn l H bp → ∀ z : Fin (d + 2) → ℂ, Fin.tail (Fin.tail z) ∈ Un → z 0 ≠ z 1 → f (ΦWn z) + (1 / 2) * ∑ p, (xiCoef τ a p : ℝ) * ((FA.S.comap some).ph p (q 0 (ΦWn z)) + (FA.S.comap some).ph p (q 1 (ΦWn z))) = logSin (Gn (Fin.tail (Fin.tail z))) (z 0) (z 1) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b ca cb hb hstep hca hcb k₀ hk₀ RW q h0 h1 f hf Un Gn ΦYn ΦWn l H bp hUn hD z hz hne
  have hPos := GlobalTheory.T.two_point_fibre_chart_second K ι Φ y Ψ N j M n d BM FA τ a b ca cb hb hstep hca hcb RW.X q Un Gn ΦYn ΦWn l H bp hUn hD _ hz
  obtain ⟨-, -, -, hbase, hG, hex, hq⟩ := hD
  have hπ := GlobalTheory.T.realisation_bijective_degree_one K ι (d + 1) _ FA.S (mCoordIdeal y) FA.Re FA.deg_one FA.br_empty
  obtain ⟨hq0, hq1⟩ := hq z hz
  generalize hw : Fin.tail (Fin.tail z) = w at hz hPos hq0 ⊢
  obtain ⟨hbO, hH⟩ := hbase w hz
  have hcab : ca ≠ cb := fun e => by
    have : (ca : ℕ) = cb := congrArg Fin.val e
    omega
  have shear := fun s : ℂ => GlobalTheory.T.elementary_factor_properties N j a b ca cb s M.j_le hb hstep hca hcb
  have hflag : ∀ (s : ℂ) (τ' : Ψ), IsBlockDiag j (flagAt H τ ca cb s w τ') ∧ (flagAt H τ ca cb s w τ').det ≠ 0 := by
    intro s τ'
    unfold flagAt
    split_ifs with e
    · refine ⟨(hH τ).1.mul (shear s).1, ?_⟩
      rw [Matrix.det_mul, (shear s).2.1, mul_one]
      exact (hH τ).2
    · exact hH τ'
  obtain ⟨x₀, hx₀⟩ := hπ.2 (q 0 (ΦWn z))
  obtain ⟨x₁, hx₁⟩ := hπ.2 (q 1 (ΦWn z))
  have t0 : Fin.tail (Fin.cons (z 0) w : Fin (d + 1) → ℂ) = w := Fin.tail_cons _ _
  obtain ⟨z₀, o0, b0, ex0⟩ := hex (Fin.cons (z 0) w) (by rw [t0]; exact hz) x₀ (hx₀.trans hq0)
  obtain ⟨z₁, o1, b1, ex1⟩ := hex (Fin.tail z) (by rw [hw]; exact hz) x₁ (hx₁.trans hq1)
  rw [t0] at b0 ex0
  rw [hw] at b1 ex1
  have c0 : (Fin.cons (z 0) w : Fin (d + 1) → ℂ) 0 = z 0 := rfl
  have c1 : (Fin.tail z : Fin (d + 1) → ℂ) 0 = z 1 := rfl
  rw [c0] at ex0
  rw [c1] at ex1

  have L0 : ∀ p, Real.log ((fsHerm ι (M.dy p)).h z₀) + FA.S.ph (some p) (q 0 (ΦWn z)) =
      potAt BM l p (bp w) (flagAt H τ ca cb (z 0) w p.1) := fun p => by
    rw [← hx₀]
    exact GlobalTheory.T.flag_analytic_orbit_off_boundary K ι Φ y Ψ N j M n d BM FA l x₀ z₀ (bp w) p _ hbO o0 b0 (ex0 p.1 p.2) (hflag _ _).1 (hflag _ _).2
  have L1 : ∀ p, Real.log ((fsHerm ι (M.dy p)).h z₁) + FA.S.ph (some p) (q 1 (ΦWn z)) =
      potAt BM l p (bp w) (flagAt H τ ca cb (z 1) w p.1) := fun p => by
    rw [← hx₁]
    exact GlobalTheory.T.flag_analytic_orbit_off_boundary K ι Φ y Ψ N j M n d BM FA l x₁ z₁ (bp w) p _ hbO o1 b1 (ex1 p.1 p.2) (hflag _ _).1 (hflag _ _).2

  have S : ∀ s : ℂ, ∑ p, (xiCoef τ a p : ℝ) * potAt BM l p (bp w) (flagAt H τ ca cb s w p.1) =
      xiPot (Gn w) s - ∑ i : Fin N, (xiCoef τ a (τ, i) : ℝ) * ((if IsProperStep N j i then 0 else
        Real.log ‖facOf N j a (H τ w) i‖) + upsLogAt BM l (τ, i) (bp w)) := fun s =>
    GlobalTheory.T.two_by_two_minor_gram_identity Ψ N j τ a b ca cb (fun τ' => BM.G l τ' (bp w)) (fun τ' => H τ' w)
      (fun p => upsLogAt BM l p (bp w)) s (Gn w) M.j_le hb hstep hca hcb (BM.G_pos l τ _ hbO).1
      (BM.G_pos l τ _ hbO).2 (hH τ).1 (hH τ).2 (hG w hz)

  have ht : z 1 - z 0 ≠ 0 := sub_ne_zero.2 fun e => hne e.symm
  have hz0 : ∀ i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) (BM.F l) (τ, i) z₀ (H τ w * (1 + Matrix.single cb ca (z 0))) := fun i => by
    have := ex0 τ i
    rwa [flagAt, if_pos rfl] at this
  have hz1 : ∀ i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) (BM.F l) (τ, i) z₁ (H τ w * (1 + Matrix.single cb ca (z 0)) *
      (1 + Matrix.single cb ca (z 1 - z 0))) := fun i => by
    have := ex1 τ i
    rwa [flagAt, if_pos rfl, show z 1 = z 0 + (z 1 - z 0) by ring, ← shear_mul hcab, ← Matrix.mul_assoc] at this
  have hgood : M.GoodAt (BM.F l) (mCoordIdeal (basePart M.blk z₀)) := by
    rw [CovMap.mCoordIdeal_eq_of_sameOrbit b0]
    exact BM.good l _ hbO.1
  have hfx := hf (ΦWn z) z₀ z₁ (BM.F l) (H τ w * (1 + Matrix.single cb ca (z 0))) (z 1 - z 0) (BM.isFrame l) hgood
    (orbit_trans (orbit_symm o0) (h0 _ x₀ hx₀)) (orbit_trans (orbit_symm o1) (h1 _ x₁ hx₁))
    ((hH τ).1.mul (shear _).1) (by rw [Matrix.det_mul, (shear _).2.1, mul_one]; exact (hH τ).2) ht hz0 hz1

  have hval : ∀ i, ¬ IsProperStep N j i → valAt M.x ((BM.F l).υ (τ, i)) (basePart M.blk z₀) = upsVal BM l (τ, i) (bp w) := by
    intro i _
    exact (GlobalTheory.T.value_constant_on_orbit _ _ M.Ω M.x _ _ _ (BM.Rb.mem _ _ (BM.Rb.mem_U _)) (orbit_symm b0)).symm
  have hfac : ∀ i, facOf N j a (H τ w * (1 + Matrix.single cb ca (z 0))) i = facOf N j a (H τ w) i :=
    (shear (z 0)).2.2.1 (H τ w)
  have hlog := GlobalTheory.T.log_norm_product_formula N (IsProperStep N j) (z 1 - z 0)
    (fun i => valAt M.x ((BM.F l).υ (τ, i)) (basePart M.blk z₀))
    (fun i => facOf N j a (H τ w * (1 + Matrix.single cb ca (z 0))) i) (fun i => xiCoef τ a (τ, i)) ht
    (fun i hi => by
      refine ⟨?_, GlobalTheory.T.step_factor_ne_zero N j a i _ ((hH τ).1.mul (shear _).1)
        (by rw [Matrix.det_mul, (shear _).2.1, mul_one]; exact (hH τ).2)⟩
      rw [hval i hi]
      exact GlobalTheory.T.unipotent_value_ne_zero K ι Φ y Ψ N j M n d BM l (τ, i) (bp w) hbO.1 ((M.blk_none _).2 hi))
  have hC : ∑ i : Fin N, (xiCoef τ a (τ, i) : ℝ) * (if IsProperStep N j i then 0 else
        Real.log ‖valAt M.x ((BM.F l).υ (τ, i)) (basePart M.blk z₀)‖ +
          Real.log ‖facOf N j a (H τ w * (1 + Matrix.single cb ca (z 0))) i‖) =
      ∑ i : Fin N, (xiCoef τ a (τ, i) : ℝ) * ((if IsProperStep N j i then 0 else
        Real.log ‖facOf N j a (H τ w) i‖) + upsLogAt BM l (τ, i) (bp w)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    by_cases hp : IsProperStep N j i
    · have hn : M.blk (τ, i) ≠ none := fun e => (M.blk_none _).1 e hp
      simp [hp, upsLogAt, hn]
    · have hn : M.blk (τ, i) = none := (M.blk_none _).2 hp
      simp only [hp, if_false, upsLogAt, hn, if_true, hval i hp, hfac i]
      ring
  have hsin := GlobalTheory.T.log_sine_formula (Gn w) (z 0) (z 1) hPos hne
  have hL : normRhs M τ a (BM.F l) z₀ z₁ (H τ w * (1 + Matrix.single cb ca (z 0))) (z 1 - z 0) -
      (1 / 2) * ∑ p, (xiCoef τ a p : ℝ) * (Real.log ((fsHerm ι (M.dy p)).h z₀) + Real.log ((fsHerm ι (M.dy p)).h z₁)) =
      Real.log ‖z 1 - z 0‖ + ∑ i : Fin N, (xiCoef τ a (τ, i) : ℝ) * (if IsProperStep N j i then 0 else
        Real.log ‖valAt M.x ((BM.F l).υ (τ, i)) (basePart M.blk z₀)‖ +
          Real.log ‖facOf N j a (H τ w * (1 + Matrix.single cb ca (z 0))) i‖) := by
    unfold normRhs
    rw [add_sub_cancel_right]
    exact hlog
  have T : ∑ p, (xiCoef τ a p : ℝ) * ((FA.S.comap some).ph p (q 0 (ΦWn z)) + (FA.S.comap some).ph p (q 1 (ΦWn z))) +
      ∑ p, (xiCoef τ a p : ℝ) * (Real.log ((fsHerm ι (M.dy p)).h z₀) + Real.log ((fsHerm ι (M.dy p)).h z₁)) =
      (xiPot (Gn w) (z 0) - ∑ i : Fin N, (xiCoef τ a (τ, i) : ℝ) * ((if IsProperStep N j i then 0 else
        Real.log ‖facOf N j a (H τ w) i‖) + upsLogAt BM l (τ, i) (bp w))) +
      (xiPot (Gn w) (z 1) - ∑ i : Fin N, (xiCoef τ a (τ, i) : ℝ) * ((if IsProperStep N j i then 0 else
        Real.log ‖facOf N j a (H τ w) i‖) + upsLogAt BM l (τ, i) (bp w))) := by
    rw [← S (z 0), ← S (z 1), ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    have e0 : (FA.S.comap some).ph p (q 0 (ΦWn z)) = FA.S.ph (some p) (q 0 (ΦWn z)) := rfl
    have e1 : (FA.S.comap some).ph p (q 1 (ΦWn z)) = FA.S.ph (some p) (q 1 (ΦWn z)) := rfl
    rw [e0, e1, ← L0 p, ← L1 p]
    ring
  rw [hfx, hsin]
  rw [hC] at hL
  linarith

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.NormFib
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem _root_.GlobalTheory.T.two_point_fibre_chart_first : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a ca cb : Fin N) (X : Type) (q : Fin 2 → X → FA.S.X) (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → X) (l : Fin BM.q) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → IsFibreData FA τ a ca cb q Un Gn ΦYn ΦWn l H bp → ∃ zex : (Fin (d + 1) → ℂ) → (Σ k, ι k) → ℂ, (∀ q', AnalyticOnNhd ℂ (fun u => zex u q') {u : Fin (d + 1) → ℂ | Fin.tail u ∈ Un}) ∧ ∀ u : Fin (d + 1) → ℂ, Fin.tail u ∈ Un → zex u ∈ mcPts (mCoordIdeal y) ∧ ∀ x₀, FA.Re.π x₀ = ΦYn u → SameOrbit (FA.Re.R.lift x₀ x₀) (zex u) ∧ SameOrbit (basePart M.blk (zex u)) (BM.Rb.lift (bp (Fin.tail u)) (bp (Fin.tail u))) ∧ ∀ τ' i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) (BM.F l) (τ', i) (zex u) (flagAt H τ ca cb (u 0) (Fin.tail u) τ') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.exact_points_holomorphic | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.exact_points_holomorphic | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.exact_points_holomorphic <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.BaseLift

section General

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω] {n : ℕ}

theorem analytic_eval {G : (Fin n → ℂ) → (Σ k, J k) → ℂ} {T : Set (Fin n → ℂ)}
    (hG : ∀ q, AnalyticOnNhd ℂ (fun w => G w q) T) (f : MRing J) :
    AnalyticOnNhd ℂ (fun w => eval (G w) (map (Int.castRingHom ℂ) f)) T := by
  induction f using MvPolynomial.induction_on with
  | C a => simpa using analyticOnNhd_const
  | add p q hp hq =>
    simp only [map_add (f := _)]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, map_X, eval_X]
    exact hp.mul (hG i)

theorem isOpen_forall_ne {A : Type} [Finite A] {T : Set (Fin n → ℂ)} (hT : IsOpen T)
    {f : A → (Fin n → ℂ) → ℂ} (hf : ∀ a, AnalyticOnNhd ℂ (f a) T) :
    IsOpen {w | w ∈ T ∧ ∀ a, f a w ≠ 0} := by
  have e : {w | w ∈ T ∧ ∀ a, f a w ≠ 0} = T ∩ ⋂ a, (T ∩ f a ⁻¹' {0}ᶜ) := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_compl_iff,
      Set.mem_singleton_iff]
    exact ⟨fun h => ⟨h.1, fun a => ⟨h.1, h.2 a⟩⟩, fun h => ⟨h.1, fun a => (h.2 a).2⟩⟩
  rw [e]
  exact hT.inter (isOpen_iInter_of_finite fun a =>
    (hf a).continuousOn.isOpen_inter_preimage hT isOpen_compl_singleton)

theorem form_notMem_iff (z : (Σ k, J k) → ℂ) {g : MRing J} {d : K → ℕ} (hg : IsMultiHomog g d) :
    g ∉ mCoordIdeal z ↔ eval z (map (Int.castRingHom ℂ) g) ≠ 0 := by
  rw [Ne, form_mem_mCoordIdeal_iff z hg, aeval_def, algebraMap_int_eq, eval₂_eq_eval_map]

theorem exists_normalised {A : Type} [Finite A] (x : (Σ k, J k) → Ω) (c : ∀ k, J k) (s : A → Ω)
    (G : (Fin n → ℂ) → (Σ k, J k) → ℂ) {T : Set (Fin n → ℂ)} (hT : IsOpen T)
    (hG : ∀ q, AnalyticOnNhd ℂ (fun w => G w q) T) (hmem : ∀ w ∈ T, G w ∈ mcPts (mCoordIdeal x))
    {w₀ : Fin n → ℂ} (hw₀ : w₀ ∈ T) (hc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ mCoordIdeal (G w₀))
    (hreg : ∀ a, RegAt x (mCoordIdeal (G w₀)) (s a)) :
    ∃ (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, J k) → ℂ), V ⊆ T ∧ IsOpen V ∧ w₀ ∈ V ∧
      (∀ q, AnalyticOnNhd ℂ (fun w => bl w q) V) ∧
      (∀ a, AnalyticOnNhd ℂ (fun w => valAt x (s a) (bl w)) V) ∧
      ∀ w ∈ V, bl w ∈ mcPts (mCoordIdeal x) ∧ (∀ k, bl w ⟨k, c k⟩ = 1) ∧ SameOrbit (G w) (bl w) ∧
        ∀ a, RegAt x (mCoordIdeal (bl w)) (s a) := by
  choose d g h hg hh hnot heq using hreg
  have hX : ∀ (k : K) (i : J k), IsMultiHomog (X ⟨k, i⟩ : MRing J) (fun k' => if k' = k then 1 else 0) := fun k i =>
    GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_X_single ⟨k, i⟩
  have hx : ∀ a, aeval x (h a) ≠ 0 := fun a e0 => by
    have h1 := (hmem w₀ hw₀).2 _ (mem_mCoordIdeal_of_aeval_eq_zero x (hh a) e0)
    exact (form_notMem_iff _ (hh a)).1 (hnot a) h1
  set bl : (Fin n → ℂ) → (Σ k, J k) → ℂ := fun w p => G w p / G w ⟨p.1, c p.1⟩ with hbl
  set T₁ : Set (Fin n → ℂ) := {w | w ∈ T ∧ ∀ k, G w ⟨k, c k⟩ ≠ 0} with hT₁
  have hT₁o : IsOpen T₁ := isOpen_forall_ne hT fun k => hG ⟨k, c k⟩
  have hT₁T : T₁ ⊆ T := fun w hw => hw.1
  have hblq : ∀ q, AnalyticOnNhd ℂ (fun w => bl w q) T₁ := fun q =>
    ((hG q).mono hT₁T).div ((hG ⟨q.1, c q.1⟩).mono hT₁T) fun w hw => hw.2 q.1
  have hevh : ∀ a, AnalyticOnNhd ℂ (fun w => eval (bl w) (map (Int.castRingHom ℂ) (h a))) T₁ := fun a =>
    analytic_eval hblq (h a)
  have horb : ∀ w ∈ T₁, SameOrbit (G w) (bl w) := fun w hw =>
    ⟨fun k => G w ⟨k, c k⟩, hw.2, funext fun p => by
      have := hw.2 p.1
      simp only [hbl]
      field_simp⟩
  have hw₁ : w₀ ∈ T₁ := ⟨hw₀, fun k e0 => (form_notMem_iff _ (hX k (c k))).1 (hc k) (by simpa using e0)⟩
  refine ⟨{w | w ∈ T₁ ∧ ∀ a, eval (bl w) (map (Int.castRingHom ℂ) (h a)) ≠ 0}, bl,
    fun w hw => hw.1.1, isOpen_forall_ne hT₁o hevh, ⟨hw₁, fun a => ?_⟩, fun q => (hblq q).mono fun w hw => hw.1,
    fun a => ?_, fun w hw => ?_⟩
  · rw [← form_notMem_iff _ (hh a), ← GlobalTheory.CompanionTheory.Ar.PB.CovMap.mCoordIdeal_eq_of_sameOrbit (horb w₀ hw₁)]
    exact hnot a
  · have hV : IsOpen {w | w ∈ T₁ ∧ ∀ a, eval (bl w) (map (Int.castRingHom ℂ) (h a)) ≠ 0} :=
      isOpen_forall_ne hT₁o hevh
    have hsub : {w | w ∈ T₁ ∧ ∀ a, eval (bl w) (map (Int.castRingHom ℂ) (h a)) ≠ 0} ⊆ T₁ :=
      fun w hw => hw.1
    refine AnalyticOnNhd.congr hV (((analytic_eval hblq (g a)).mono hsub).div
      ((hevh a).mono hsub) fun w hw => hw.2 a) fun w hw => ?_
    have hz : bl w ∈ mcPts (mCoordIdeal x) := mem_mcPts_of_sameOrbit
      (GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal x) (orbit_symm (horb w hw.1)) (hmem w hw.1.1)
    exact (valAt_eq hz ⟨d a, g a, h a, hg a, hh a, hx a, heq a, hw.2 a, rfl⟩).symm
  · have hz : bl w ∈ mcPts (mCoordIdeal x) := mem_mcPts_of_sameOrbit
      (GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal x) (orbit_symm (horb w hw.1)) (hmem w hw.1.1)
    exact ⟨hz, fun k => div_self (hw.1.2 k), horb w hw.1,
      fun a => ⟨d a, g a, h a, hg a, hh a, (form_notMem_iff _ (hh a)).2 (hw.2 a), heq a⟩⟩

end General

theorem exists_baseChart (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ]
    (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ)
    (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (F : FrameData ι Ψ N M.Ω M.blk) (x₀ : Rb.X)
    (hgood : M.GoodAt F (mCoordIdeal (Rb.lift x₀ x₀))) :
    ∃ (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ),
      x₀ ∈ (Rb.A.chart kb).source ∧ Rb.A.chart kb x₀ ∈ V ∧ IsBaseChart M Rb F kb V bl := by
  obtain ⟨kb, hkb⟩ := Rb.A.cover x₀
  have hT : IsOpen ((Rb.A.chart kb).target ∩ (Rb.A.chart kb).symm ⁻¹' Rb.U x₀) :=
    (Rb.A.chart kb).isOpen_inter_preimage_symm (Rb.isOpen_U x₀)
  have hlw : Rb.lift x₀ ((Rb.A.chart kb).symm (Rb.A.chart kb x₀)) = Rb.lift x₀ x₀ := by
    rw [(Rb.A.chart kb).left_inv hkb]
  have hw₀ : Rb.A.chart kb x₀ ∈ (Rb.A.chart kb).target ∩ (Rb.A.chart kb).symm ⁻¹' Rb.U x₀ :=
    ⟨(Rb.A.chart kb).map_source hkb, by
      show (Rb.A.chart kb).symm (Rb.A.chart kb x₀) ∈ Rb.U x₀
      rw [(Rb.A.chart kb).left_inv hkb]
      exact Rb.mem_U x₀⟩
  let s : (((Σ k, ι k) × Finset (Fin N)) ⊕ ((Σ k, ι k) × Finset (Fin N))) ⊕
      ({p : Ψ × Fin N // M.blk p = none} ⊕ {p : Ψ × Fin N // M.blk p = none}) → M.Ω :=
    Sum.elim (Sum.elim (fun a => F.u a.1 a.2) (fun a => F.u' a.2 a.1))
      (Sum.elim (fun p => F.υ p.1) (fun p => (F.υ p.1)⁻¹))
  obtain ⟨V, bl, hVT, hVo, hV₀, hq, hval, hpt⟩ := exists_normalised M.x F.c s
    (fun w => Rb.lift x₀ ((Rb.A.chart kb).symm w)) hT (fun q => Rb.holo x₀ q kb)
    (fun w hw => Rb.mem x₀ _ hw.2) hw₀
    (by simpa only [hlw] using hgood.1)
    (by
      simp only [hlw]
      rintro ((⟨q, I⟩ | ⟨q, I⟩) | (⟨p, hp⟩ | ⟨p, hp⟩))
      · exact (hgood.2.1 q I).1
      · exact (hgood.2.1 q I).2
      · exact (hgood.2.2 p hp).2.1
      · exact (hgood.2.2 p hp).2.2)
  refine ⟨kb, V, bl, hkb, hV₀, hVo, fun w hw => (hVT hw).1, hq,
    fun q I => hval (Sum.inl (Sum.inl (q, I))), fun w hw => ?_⟩
  obtain ⟨hz, h1, hor, hr⟩ := hpt w hw
  refine ⟨hz, h1, ⟨fun k e0 => ?_, fun q I => ⟨hr (Sum.inl (Sum.inl (q, I))), hr (Sum.inl (Sum.inr (q, I)))⟩,
    fun p hp => ⟨(hgood.2.2 p hp).1, hr (Sum.inr (Sum.inl ⟨p, hp⟩)), hr (Sum.inr (Sum.inr ⟨p, hp⟩))⟩⟩,
    orbit_trans (Rb.compat _ x₀ _ ⟨Rb.mem_U _, (hVT hw).2⟩) hor⟩
  have := (form_mem_mCoordIdeal_iff (bl w) (GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_X_single
    (⟨k, F.c k⟩ : Σ k, baseIdx ι M.blk k))).1 e0
  rw [aeval_X, h1 k] at this
  exact one_ne_zero this

end GlobalTheory.CompanionTheory.Ar.PB.WMan.BaseLift
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan

theorem continuousWithinAt_valAt_of_regAt {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type}
    [Field Ω] {x : (Σ k, ι k) → Ω} {zb : (Σ k, ι k) → ℂ} (hz : zb ∈ mcPts (mCoordIdeal x)) {s : Ω}
    (hs : RegAt x (mCoordIdeal zb) s) : ContinuousWithinAt (valAt x s) (mcPts (mCoordIdeal x)) zb := by
  obtain ⟨d, g, h, hg, hh, hn, heq⟩ := hs
  have hy := GlobalTheory.CompanionTheory.Ar.PB.ValRing.aeval_ne_zero_of_notMem hz hh hn
  have h0 := GlobalTheory.CompanionTheory.Ar.PB.ValRing.eval_ne_zero_of_notMem hh hn
  have cg : Continuous fun w : (Σ k, ι k) → ℂ => eval w (map (Int.castRingHom ℂ) g) :=
    MvPolynomial.continuous_eval _
  have ch : Continuous fun w : (Σ k, ι k) → ℂ => eval w (map (Int.castRingHom ℂ) h) :=
    MvPolynomial.continuous_eval _
  have hnear : valAt x s =ᶠ[𝓝[mcPts (mCoordIdeal x)] zb]
      fun w => eval w (map (Int.castRingHom ℂ) g) / eval w (map (Int.castRingHom ℂ) h) := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ch.continuousAt.eventually_ne h0)] with w hw hw0
    exact valAt_eq hw ⟨d, g, h, hg, hh, hy, heq, hw0, rfl⟩
  have hat : valAt x s zb = eval zb (map (Int.castRingHom ℂ) g) / eval zb (map (Int.castRingHom ℂ) h) :=
    valAt_eq hz ⟨d, g, h, hg, hh, hy, heq, h0, rfl⟩
  exact (cg.continuousAt.div ch.continuousAt h0).continuousWithinAt.congr_of_eventuallyEq hnear hat

section Flag

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem twMinor_continuousWithinAt (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) {Z : Type}
    [TopologicalSpace Z] {S : Set Z} {z₀ : Z} {β : Z → (Σ k, baseIdx ι M.blk k) → ℂ} {P : Z → (Σ k, ι k) → ℂ}
    (hβ : ContinuousWithinAt β S z₀) (hS : Set.MapsTo β S (mcPts (mCoordIdeal M.x)))
    (hz : β z₀ ∈ mcPts (mCoordIdeal M.x)) (hG : M.GoodAt F (mCoordIdeal (β z₀)))
    (hP : ContinuousWithinAt P S z₀) (i : Fin N) (k : K) (g : Matrix (Fin N) (Fin N) ℂ) (J : Finset (Fin N)) :
    ContinuousWithinAt (fun z => twMinor M F (β z) i k g (P z) J) S z₀ := by
  simp only [twMinor, pluck]
  refine tendsto_finsetSum _ fun I _ => Tendsto.const_mul _ (tendsto_finsetSum _ fun m _ => Tendsto.mul ?_ ?_)
  · exact ContinuousWithinAt.comp (g := valAt M.x (F.u' I ⟨k, m⟩))
      (continuousWithinAt_valAt_of_regAt hz (hG.2.1 _ _).2) hβ hS
  · exact ((continuous_apply (⟨k, m⟩ : Σ k, ι k)).continuousAt.comp_continuousWithinAt hP)

theorem wRho_continuousOn : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin (d + 2)), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → ContinuousOn (wRho M Rb τ k₀ ca cb F kb r h ε) (wO M Rb τ a k₀ ca cb F kb V r h) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε H
  obtain ⟨hb, hab, hk, hca, hcb, hy, hF, hB, horb, hr, hh⟩ := H
  obtain ⟨hVo, hVt, -, -, hbl⟩ := hB
  have hbase : Set.MapsTo (baseOf M k₀) (wO M Rb τ a k₀ ca cb F kb V r h) (mcPts (mCoordIdeal M.x)) := fun z hz =>
    GlobalTheory.CompanionTheory.Ar.PB.CPts.base_mem M (GlobalTheory.CompanionTheory.Ar.PB.CPts.comp_mem_mcPts (GlobalTheory.CompanionTheory.Ar.PB.WSq.Pts.isBlockMap_v₀ k₀)
      (algebraMap Φ (RatFunc Φ)) (funext fun _ => rfl) hz.1)
  have cB : Continuous (baseOf M k₀) := continuous_pi fun q => continuous_apply _
  have cF : Continuous (fstPt (ι := ι) k₀) := continuous_pi fun q => continuous_apply _
  have cS : Continuous (sndPt (ι := ι) k₀) := continuous_pi fun q => continuous_apply _
  have hgood : ∀ z ∈ wO M Rb τ a k₀ ca cb F kb V r h, M.GoodAt F (mCoordIdeal (baseOf M k₀ z)) := by
    intro z hz
    have h3 := (hbl _ hz.2.2.1).2.2
    rw [(Rb.A.chart kb).left_inv hz.2.1] at h3
    have e := orbit_trans (orbit_symm (horb _ (hbase hz))) h3.2
    rw [GlobalTheory.CompanionTheory.Ar.PB.CovMap.mCoordIdeal_eq_of_sameOrbit e]
    exact h3.1
  have cLow : ∀ (P : ((Σ o : Option K, ι (o.getD k₀)) → ℂ) → (Σ k, ι k) → ℂ), Continuous P → ∀ (τ' : Ψ) (a' b' : Fin N),
      ∀ z ∈ wO M Rb τ a k₀ ca cb F kb V r h, (∀ k, M.blk (τ', stepOf N j b') = some k →
        twMinor M F (baseOf M k₀ z) (stepOf N j b') k (h τ')⁻¹ (P z) (stepCols N j (stepOf N j b')) ≠ 0) →
      ContinuousWithinAt (fun z => lowRead M F (baseOf M k₀ z) h (P z) τ' a' b')
        (wO M Rb τ a k₀ ca cb F kb V r h) z := by
    intro P hP τ' a' b' z hz hne
    have cT := fun (k : K) (J : Finset (Fin N)) => twMinor_continuousWithinAt M F cB.continuousWithinAt hbase (hbase hz)
      (hgood z hz) hP.continuousWithinAt (stepOf N j b') k (h τ')⁻¹ J
    cases e : M.blk (τ', stepOf N j b') with
    | none =>
      simp only [lowRead, e, Option.elim_none]
      exact continuousWithinAt_const
    | some k =>
      simp only [lowRead, e, Option.elim_some]
      exact (cT k _).div (cT k _) (hne k e)
  have hst : stepOf N j ca = a := by
    apply Fin.ext
    have h1 := a.2
    have h2 := ca.2
    have h3 := M.j_le
    simp only [stepOf, lastCol] at hca ⊢
    split_ifs at hca ⊢ <;> omega
  intro z hz
  have hz₄ : ∀ p k, M.blk p = some k →
      twMinor M F (baseOf M k₀ z) p.2 k (h p.1)⁻¹ (fstPt k₀ z) (stepCols N j p.2) ≠ 0 := hz.2.2.2.1
  have hz₅ : twMinor M F (baseOf M k₀ z) a k₀ (h τ)⁻¹ (sndPt k₀ z) (stepCols N j a) ≠ 0 := hz.2.2.2.2
  refine continuousWithinAt_pi.2 fun i => ?_
  rcases e : ε.symm i with l | q | u
  · simp only [wRho, e]
    have c2 : ContinuousWithinAt (r ∘ baseOf M k₀) (wO M Rb τ a k₀ ca cb F kb V r h) z :=
      ContinuousWithinAt.comp (hr _ (hbase hz)) cB.continuousWithinAt hbase
    have c3 : ContinuousAt (fun x => Rb.A.chart kb x l) ((r ∘ baseOf M k₀) z) :=
      (continuous_apply l).continuousAt.comp ((Rb.A.chart kb).continuousAt hz.2.1)
    exact ContinuousAt.comp_continuousWithinAt (g := fun x => Rb.A.chart kb x l) c3 c2
  · simp only [wRho, e]
    exact cLow (fstPt k₀) cF q.1.1 q.1.2.1 q.1.2.2 z hz fun k e' => hz₄ (q.1.1, stepOf N j q.1.2.2) k e'
  · simp only [wRho, e]
    refine (cLow (sndPt k₀) cS τ cb ca z hz fun k e' => ?_).sub (cLow (fstPt k₀) cF τ cb ca z hz fun k e' => ?_)
    · rw [hst] at e' ⊢
      obtain rfl : k₀ = k := Option.some.inj (hk.symm.trans e')
      exact hz₅
    · exact hz₄ (τ, stepOf N j ca) k e'

end Flag

end GlobalTheory.CompanionTheory.Ar.PB.WMan
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan


theorem _root_.GlobalTheory.T.twisted_frame_value_formula : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (zb₂ : (Σ k, baseIdx ι M.blk k) → ℂ) (z : (Σ o : Option K, ι (o.getD k₀)) → ℂ) (H U : Ψ → Matrix (Fin N) (Fin N) ℂ) (V : Matrix (Fin N) (Fin N) ℂ) (t : ℂ), M.blk (τ, a) = some k₀ → baseOf M k₀ z ∈ mcPts (mCoordIdeal M.x) → M.GoodAt F (mCoordIdeal (baseOf M k₀ z)) → SameOrbit zb₂ (baseOf M k₀ z) → (∀ τ', IsBlockDiag j (U τ') ∧ (U τ').BlockTriangular id ∧ ∀ c, U τ' c c ≠ 0) → IsBlockDiag j V → V.BlockTriangular id → (∀ c ∈ stepCols N j a, V c c ≠ 0) → (∀ p k, M.blk p = some k → ∃ α : ℂ, α ≠ 0 ∧ ∀ m : ι k, fstPt k₀ z ⟨k, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) (baseOf M k₀ z) * minorIJ (H p.1 * U p.1) I (stepCols N j p.2)) → (∃ α : ℂ, α ≠ 0 ∧ ∀ m : ι k₀, sndPt k₀ z ⟨k₀, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k₀, m⟩ I) (baseOf M k₀ z) * minorIJ (H τ * (1 + Matrix.single cb ca t) * V) I (stepCols N j a)) → SameOrbit (sqZ M F zb₂ H k₀ τ ca cb t) z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.sameOrbit_sqZ_of_flags | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.sameOrbit_sqZ_of_flags | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.sameOrbit_sqZ_of_flags <;> assumption)
end

section

open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.Cj GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.lift_system_real_structure : ∀ {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {P : Ideal (MRing ι)} {U : X → Set X} {lift : X → X → (Σ k, ι k) → ℂ}, IsLiftSys A P U lift → ∀ (c : X → X), (∀ x, SameOrbit (lift (c x) (c x)) (cj (lift x x))) → Continuous c → (∀ j k, AnalyticOnNhd ℂ (fun z => star (A.chart k (c ((A.chart j).symm z)))) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (c ⁻¹' (A.chart k).source))) → ∀ (f : HermLine ι), IsConjInvariantH f → ∀ (th : LocPot X), (∀ x, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∃ G : X → ℂ, A.HoloOn V G ∧ ∀ y ∈ V, Real.log (f.h (lift x y)) - th.φ x y = (G y).re) → ∀ x, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∃ G : X → ℂ, A.HoloOn V G ∧ ∀ y ∈ V, th.φ (c x) (c y) - th.φ x y = (G y).re := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.Cj.pot_conj_pluriharmonic | exact GlobalTheory.CompanionTheory.Ar.PB.Cj.pot_conj_pluriharmonic | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.Cj.pot_conj_pluriharmonic <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

theorem _root_.GlobalTheory.T.flag_cover_arithmetic_second : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 2) → IsArithVar (mCoordIdeal y') (d + 2) → ∀ z ∈ mcPts (mCoordIdeal y'), ∀ w w', CovMap.IsImg Cv z w → CovMap.IsImg Cv z w' → SameOrbit w w' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovMap.isImg_unique | exact GlobalTheory.CompanionTheory.Ar.PB.CovMap.isImg_unique | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovMap.isImg_unique <;> assumption)
end
