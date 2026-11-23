module

public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralWeierstrassChartXyUnitSeries
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
public import Formalism.HermitianCurvature.Bundle009
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle001
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle029
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle031
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle002
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle010
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle091
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle063
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle073
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle081
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.BlockMinorAbsoluteOfExplicit
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSmooth.ExpIntertwine
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormFactor
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
public import Formalism.LocalToGlobal.CharacterGerms.Bundle023
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Formalism.LocalToGlobal.CharacterGerms.Bundle006
public import Formalism.LocalToGlobal.CharacterGerms.Bundle033
public import Formalism.RealPlaceAnalysis.Bundle003
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle003
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle092
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle003
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Formalism.LocalToGlobal.Divisibility.Numbers
import Development.AutomorphicArithmetic.OrbitLabellings.RowLab

@[expose] public section

section

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

theorem _root_.GlobalTheory.T.integral_weierstrass_chart_xy_unit_series : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (ℓ : ℂ_[q]⟦X⟧), M.Chart ℓ → coeff 1 ℓ ≠ 0 ∧ ∃ v xs ys : ℂ_[q]⟦X⟧, Bd 1 v ∧ Bd 1 xs ∧ Bd 1 ys ∧ ‖constantCoeff v‖ = 1 ∧ ‖constantCoeff xs‖ = 1 ∧ ‖constantCoeff ys‖ = 1 ∧ hat M.ι ℓ M.u = X * v ∧ hat M.ι ℓ M.w * ys = -X ^ 3 ∧ xs = -v * ys ∧ ∀ (F : ℂ → ℂ) (A B : Polynomial ℂ) (k : ℕ), AnalyticAt ℂ F 0 → A.natDegree ≤ k → B.natDegree ≤ k → ∀ G : ℂ → ℂ, AnalyticAt ℂ G 0 → ∀ (D : Polynomial ℂ) (j : ℕ), D.natDegree ≤ j → (∀ᶠ z in 𝓝[≠] (0 : ℂ), F z * D.eval (M.x z) = G z * (A.eval (M.x z) + B.eval (M.x z) * M.y z)) → hat M.ι ℓ F * X ^ (2 * k + 3) * (∑ i ∈ Finset.range (j + 1), C (M.ι (D.coeff i)) * X ^ (2 * (j - i)) * xs ^ i) = hat M.ι ℓ G * X ^ (2 * j) * ∑ i ∈ Finset.range (k + 1), (C (M.ι (A.coeff i)) * X ^ (2 * (k - i) + 3) * xs ^ i + C (M.ι (B.coeff i)) * X ^ (2 * (k - i)) * xs ^ i * ys) := by
  first | exact @GlobalTheory.MomOne.ChartXY.chart_xy | exact GlobalTheory.MomOne.ChartXY.chart_xy | (intros; apply GlobalTheory.MomOne.ChartXY.chart_xy <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.MomentPointwise

theorem sum_sq_eq_trace {n : Type} [Fintype n] (A : Matrix n n ℂ) :
    ((∑ i, ∑ j, ‖A i j‖ ^ 2 : ℝ) : ℂ) = (Aᴴ * A).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.conj_mul']

theorem sum_sq_conj {n : Type} [Fintype n] [DecidableEq n] (Q X : Matrix n n ℂ)
    (hQ : Q ∈ Matrix.unitaryGroup n ℂ) :
    ∑ i, ∑ j, ‖(Q * X * Q⁻¹) i j‖ ^ 2 = ∑ i, ∑ j, ‖X i j‖ ^ 2 := by
  have h1 : Qᴴ * Q = 1 := Matrix.mem_unitaryGroup_iff'.1 hQ
  have hinv : Q⁻¹ = Qᴴ := Matrix.inv_eq_left_inv h1
  apply Complex.ofReal_injective
  rw [sum_sq_eq_trace, sum_sq_eq_trace, hinv]
  have : (Q * X * Qᴴ)ᴴ * (Q * X * Qᴴ) = Q * (Xᴴ * X * Qᴴ) := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Qᴴ Q, h1, Matrix.one_mul]
  rw [this, Matrix.trace_mul_comm, Matrix.mul_assoc, h1, Matrix.mul_one]

theorem exp_mem {k r : ℕ} {X : Mx k r} (hX : PI.UpqRep.InLieHpk k r X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ GG k r := by
  refine CCRuleCW.exp_mem_UH (Formalism.QuantumDeterminants.Hpk k r) _ ?_
  have hL : Xᴴ * Formalism.QuantumDeterminants.Hpk k r + Formalism.QuantumDeterminants.Hpk k r * X = 0 := hX
  rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
      Matrix.mul_smul, ← smul_add, hL, smul_zero]

theorem one_mem_UW (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : (1 : Mx k r) ∈ Formalism.QuantumDeterminants.UWset k r z := by
  refine ⟨?_, fun a => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩, Matrix.one_mulVec _⟩
  show (1 : Mx k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r * 1 = Formalism.QuantumDeterminants.Hpk k r
  simp

theorem pointwise : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (l : R.H → Wp) (Q : Mx k r) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub), R.IsDS ε mu → SideG k r z π u μW μN μG νq → IsBes R z π l → PI.UpqRep.IsCayleyU k r ε Q → R.IsE Q E → ∀ g ∈ GG k r, ∀ (a : Fin r) (w : R.smSub), (lenA k r z g a.succ / lenA k r z g a.castSucc) ^ 2 * ‖l (R.σ g w)‖ ^ 2 ≤ ∑ c, ∑ e, ‖l (R.σ g (E c e w))‖ ^ 2 := by
  intro hK k r ε mu R Wp _ _ _ _ z π u μW μN μG νq l Q E hR hS hl hQ hE g hg a w
  obtain ⟨hz, hT, ⟨u₀, hπ⟩, -⟩ := hS
  have hπ1 : π 1 = 1 := (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_facts hT hπ).1
  obtain ⟨hmul, -, -, hsm, -⟩ := GlobalTheory.T.discreteSeries_unitary_smooth_basic hK k r ε mu R hR
  obtain ⟨hact, -, -, hcomp⟩ := GlobalTheory.T.smooth_maps_closure hK k r ε mu mu mu R R R hR hR hR
  obtain ⟨X, hX, hXn, hXt⟩ := GlobalTheory.T.exists_lie_unitary_element_simple_root k r z hz hT g hg a
  obtain ⟨-, -, hexp⟩ := GlobalTheory.T.derivedAction_expand_matrixUnits hK k r ε mu R hR Q E hQ.1.1 hE
  obtain ⟨ladd, lsmul, leq, lcont⟩ := hl
  have hla : 0 ≤ lenA k r z g a.castSucc := Metric.infDist_nonneg
  have hla1 : 0 ≤ lenA k r z g a.succ := Metric.infDist_nonneg
  rcases hla.eq_or_lt with h0 | hpos
  · rw [← h0]
    simp only [div_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
    positivity
  set L := lenA k r z g a.succ with hL
  have badd : ∀ v ∈ R.sm, ∀ v' ∈ R.sm, l (R.σ g (v + v')) = l (R.σ g v) + l (R.σ g v') := by
    intro v hv v' hv'
    rw [map_add (f := _)]; exact ladd _ (hsm g hg v hv) _ (hsm g hg v' hv')
  have bsmul : ∀ (c : ℂ), ∀ v ∈ R.sm, l (R.σ g (c • v)) = c • l (R.σ g v) := by
    intro c v hv
    rw [map_smul]; exact lsmul _ _ (hsm g hg v hv)
  have hder := (GlobalTheory.T.frechetContinuous_continuousOn_orbit_hasDerivAt hK k r ε mu R hR Wp (fun v => l (R.σ g v)) badd bsmul
    (hcomp Wp _ l (hact g hg) lcont) w w.2).2 X hX
  have hfun : (fun t : ℝ => l (R.σ g (R.σ (NormedSpace.exp ((t : ℂ) • X)) w))) =
      fun t : ℝ => Complex.exp (-(2 * (L : ℂ) * (t : ℂ)) * Complex.I) • l (R.σ g w) := by
    funext t
    obtain ⟨m, hm, hgm, hψ⟩ := hXt t
    rw [← hmul g hg _ (exp_mem hX t), hgm, hmul m hm.1 g hg, ← hψ]
    have := leq 1 (one_mem_UW k r z) m hm _ (hsm g hg w w.2)
    rw [Matrix.one_mul, hπ1] at this
    exact this
  have hd2 : HasDerivAt (fun t : ℝ => Complex.exp (-(2 * (L : ℂ) * (t : ℂ)) * Complex.I) • l (R.σ g w))
      ((-(2 * (L : ℂ)) * Complex.I) • l (R.σ g w)) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => -(2 * (L : ℂ) * (t : ℂ)) * Complex.I) (-(2 * (L : ℂ)) * Complex.I) 0 := by
      have := (((Complex.ofRealCLM.hasDerivAt (x := 0)).const_mul (2 * (L : ℂ))).neg).mul_const Complex.I
      simpa using this
    have h2 := h1.cexp.smul_const (l (R.σ g w))
    simpa using h2
  rw [hfun] at hder
  have heq := hd2.unique hder
  let B : R.smSub →ₗ[ℂ] Wp :=
    { toFun := fun v => l (R.σ g v)
      map_add' := fun v v' => badd v v.2 v' v'.2
      map_smul' := fun c v => bsmul c v v.2 }
  have hsum : l (R.σ g (PI.UpqRep.dsig (k := k) (r := r) R.σ X w)) =
      ∑ p : Fin (2 * r + k + 1) × Fin (2 * r + k + 1), (Q * X * Q⁻¹) p.1 p.2 • l (R.σ g (E p.1 p.2 w)) := by
    have h1 : B (∑ c, ∑ e, (Q * X * Q⁻¹) c e • E c e w) = ∑ c, ∑ e, (Q * X * Q⁻¹) c e • B (E c e w) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul]
    rw [Fintype.sum_prod_type, hexp X hX w]
    refine Eq.trans ?_ h1
    show _ = l (R.σ g ((∑ c, ∑ e, (Q * X * Q⁻¹) c e • E c e w : R.smSub) : R.H))
    simp only [Submodule.coe_sum, Submodule.coe_smul]
  have key := Formalism.HermitianLatticeCounting.P.majorant_cauchy_schwarz_holds Wp (Fin (2 * r + k + 1) × Fin (2 * r + k + 1))
    (fun p => (Q * X * Q⁻¹) p.1 p.2) (fun p => l (R.σ g (E p.1 p.2 w))) (l (R.σ g w))
    (-(2 * (L : ℂ)) * Complex.I) 1 _ L hpos (by simp [abs_of_nonneg hla1]) (heq.trans hsum)
    (by rw [Fintype.sum_prod_type, sum_sq_conj Q X hQ.2]; exact hXn)
  rw [Fintype.sum_prod_type, one_mul] at key
  exact key

end GlobalTheory.MomentPointwise
end
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory


open Matrix MeasureTheory Finset in
open scoped InnerProductSpace ENNReal in
theorem _root_.GlobalTheory.gN_rpow_neg_integrable_haar : _root_.Formalism.FourierDecayAlt.ThreeDimData.GrowthG := by
  unfold _root_.Formalism.FourierDecayAlt.ThreeDimData.GrowthG
  intro k r μG A hμ hA
  have hW : _root_.Formalism.FourierDecayAlt.B.IsHaarOn (_root_.Formalism.FourierDecayAlt.B.GV k r) μG :=
    (_root_.GlobalTheory.HaarNotions.isHaarOn_iff_groups k r μG).1.1 hμ
  have hvol := _root_.Formalism.FourierDecayAlt.P.norm_ball_volume_sharp
  unfold _root_.Formalism.FourierDecayAlt.B2.VolSharp at hvol
  obtain ⟨C, hC⟩ := hvol k r μG hW
  have hU : ∀ᵐ x ∂μG, Matrix.of x ∈ _root_.Formalism.QuantumDeterminants.UH (_root_.Formalism.QuantumDeterminants.Hpk k r) := by
    unfold _root_.PI.BesselPeriodGGP.IsHaarOn at hμ
    exact ae_iff.2 hμ.2.2.1
  set N : _root_.Formalism.QuantumDeterminants.Mt k r → ℝ := fun x ↦ _root_.Formalism.FourierDecayAlt.B.gN (Matrix.of x) with hNdef
  have hNcont : Continuous N := by
    simp only [hNdef]
    unfold _root_.Formalism.FourierDecayAlt.B.gN
    fun_prop
  have hNm : Measurable N := hNcont.measurable
  have h1 : ∀ᵐ x ∂μG, 1 ≤ N x := hU.mono fun x hx ↦ _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hx
  have hd0 : (0:ℝ) ≤ 2 * ((k:ℝ) + r) * (r + 1) := by positivity
  have hAd : 2 * ((k:ℝ) + r) * (r + 1) < A := by
    have : _root_.Formalism.FourierDecayAlt.ThreeDimData.AG k r = 4 * ((k:ℝ) + r) * (r + 1) := by unfold _root_.Formalism.FourierDecayAlt.ThreeDimData.AG; ring
    rw [this] at hA
    linarith
  set d : ℝ := 2 * ((k:ℝ) + r) * (r + 1) with hd
  set C' : ℝ := max C 0 with hC'
  set q : ℝ := (2:ℝ) ^ (d - A) with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have hS : ∀ n : ℕ, MeasurableSet {x | N x ≤ (2:ℝ) ^ (n + 1)} := fun n ↦
    measurableSet_le hNm measurable_const
  have hvolS : ∀ n : ℕ, μG {x | N x ≤ (2:ℝ) ^ (n + 1)}
      ≤ ENNReal.ofReal (C' * ((2:ℝ) ^ (n + 1)) ^ d) := by
    intro n
    refine (hC _ (one_le_pow₀ one_le_two)).trans (ENNReal.ofReal_le_ofReal ?_)
    gcongr
    exact le_max_left _ _
  have hkey : ∀ n : ℕ, ((2:ℝ) ^ n) ^ (-A) * (C' * ((2:ℝ) ^ (n + 1)) ^ d)
      = C' * 2 ^ d * q ^ n := by
    intro n
    rw [← Real.rpow_natCast_mul (by norm_num), ← Real.rpow_natCast_mul (by norm_num), hq,
      ← Real.rpow_mul_natCast (by norm_num)]
    have e : (2:ℝ) ^ ((n:ℝ) * -A) * (2:ℝ) ^ (((n + 1 : ℕ) : ℝ) * d)
        = 2 ^ d * 2 ^ ((d - A) * n) := by
      rw [← Real.rpow_add two_pos, ← Real.rpow_add two_pos]
      congr 1
      push_cast
      ring
    calc ((2:ℝ) ^ ((n:ℝ) * -A)) * (C' * (2:ℝ) ^ (((n + 1 : ℕ) : ℝ) * d))
        = C' * ((2:ℝ) ^ ((n:ℝ) * -A) * (2:ℝ) ^ (((n + 1 : ℕ) : ℝ) * d)) := by ring
      _ = C' * 2 ^ d * 2 ^ ((d - A) * n) := by rw [e]; ring
  have hsum : Summable fun n : ℕ ↦ C' * 2 ^ d * q ^ n :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left _
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hpt : ∀ᵐ x ∂μG, ENNReal.ofReal (N x ^ (-A)) ≤ ∑' n : ℕ,
      {y | N y ≤ (2:ℝ) ^ (n + 1)}.indicator (fun _ ↦ ENNReal.ofReal (((2:ℝ) ^ n) ^ (-A))) x := by
    filter_upwards [h1] with x hx
    obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near hx one_lt_two
    refine le_trans ?_ (ENNReal.le_tsum n)
    rw [Set.indicator_of_mem (show x ∈ {y | N y ≤ (2:ℝ) ^ (n + 1)} from hn2.le)]
    exact ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_nonpos (by positivity) hn1 (by linarith))
  refine ⟨(hNm.pow_const _).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  calc ∫⁻ x, ‖_root_.Formalism.FourierDecayAlt.B.gN (Matrix.of x) ^ (-A)‖ₑ ∂μG
      = ∫⁻ x, ENNReal.ofReal (N x ^ (-A)) ∂μG := by
        refine lintegral_congr fun x ↦ ?_
        rw [Real.enorm_eq_ofReal
          (Real.rpow_nonneg (by unfold _root_.Formalism.FourierDecayAlt.B.gN; exact Real.sqrt_nonneg _) _)]
    _ ≤ ∫⁻ x, ∑' n : ℕ, {y | N y ≤ (2:ℝ) ^ (n + 1)}.indicator
          (fun _ ↦ ENNReal.ofReal (((2:ℝ) ^ n) ^ (-A))) x ∂μG := lintegral_mono_ae hpt
    _ = ∑' n : ℕ, ENNReal.ofReal (((2:ℝ) ^ n) ^ (-A)) * μG {y | N y ≤ (2:ℝ) ^ (n + 1)} := by
        rw [lintegral_tsum fun n ↦ (measurable_const.indicator (hS n)).aemeasurable]
        exact tsum_congr fun n ↦ lintegral_indicator_const (hS n) _
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (C' * 2 ^ d * q ^ n) := by
        refine ENNReal.tsum_le_tsum fun n ↦ ?_
        rw [← hkey n, ENNReal.ofReal_mul (by positivity)]
        gcongr
        exact hvolS n
    _ = ENNReal.ofReal (∑' n : ℕ, C' * 2 ^ d * q ^ n) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun n ↦ by positivity) hsum).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

end GlobalTheory
end

section

open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

namespace GlobalTheory

theorem reducedWigner_lowering : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (β : ℂ) (L : Fin (n + 1) → ℤ) (l : Fin (n + 1)), Hyp E β L → (∀ a b x y, inner ℂ (E a b x) y = inner ℂ x (E b a y)) → (∀ a b y c, Et a b y c = E a b (y c) - if c = b then y a else 0) → (∀ y a, Om y a = ∑ c, E a c (y c)) → ∀ (M : Fin n → ℤ) (v : V), v ∈ CapSp (subA E) (shf β M) → (Module.End.eigenspace Om (β + L l + (n : ℂ))).starProjection (PiLp.single 2 (Fin.last n) v) (Fin.last n) = (GlobalTheory.WigSh.wM L M l : ℂ) • v := by
  intro V _ _ _ n E Et Om β L l hH hE hEt hOm M v hv
  set m : Fin (n + 1) → ℂ := shf β L with hm
  have hcap : ∀ w v, qdet E w v = (∏ j, (w + m j)) • v := fun w v => hH.cap w v
  have hrel := tensor_dual_standard_rel V n E Et Om hH.gl hE hEt hOm
  obtain ⟨K, hK1, hK2⟩ := lastComatrixRow_inverts_dual V n E Om m hH.gl hcap hOm
  have hinj : Function.Injective m := by
    intro i j hij
    have h1 : ((L i : ℤ) : ℂ) = ((L j : ℤ) : ℂ) := by
      simpa [hm, shf] using hij
    exact hH.anti.injective (by exact_mod_cast h1)
  let ev : PiLp 2 (fun _ : Fin (n + 1) => V) →ₗ[ℂ] V :=
    { toFun := fun x => x (Fin.last n)
      map_add' := fun x y => by simp
      map_smul' := fun c x => by simp }
  let q : ℂ → ℂ := fun u => ∏ j, (u + shf β M j)
  have hq : Continuous q := by
    exact continuous_finsetProd _ (fun j _ => continuous_id.add continuous_const)
  have hKy : ∀ u, K u (PiLp.single 2 (Fin.last n) v) = q u • v := by
    intro u
    rw [hK2]
    exact (mem_CapSp.mp hv) u
  have hres := ev_starProjection_eigenspace_eq_residue (PiLp 2 (fun _ : Fin (n + 1) => V)) V (n + 1)
    m (n : ℂ) Om ev K q (PiLp.single 2 (Fin.last n) v) v l hinj hrel.2.2.1
    (splitCasimir_eigenvalue_dual V n E Et Om m hH.gl hE hcap hEt hOm)
    (fun u x => hK1 u x) hq hKy
  have hev : m l + (n : ℂ) = β + L l + (n : ℂ) := by simp [hm, shf]
  rw [hev] at hres
  change ev _ = _
  rw [hres]
  congr 1
  simp only [q, hm, shf, WigSh.wM]
  push_cast
  congr 1
  · apply Finset.prod_congr rfl
    intro j _
    ring
  · apply Finset.prod_congr rfl
    intro j _
    ring

end GlobalTheory
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.SParamMeas

open Formalism.QuantumDeterminants

variable {k r : ℕ}

noncomputable def conjInvM (a : B.Mat k r) (x : Mt k r) : Mt k r := a⁻¹ * Matrix.of x * a

theorem meas_mul {α : Type*} [MeasurableSpace α] {f g : α → Mt k r} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x => Formalism.FourierDecayAlt.P.B7.mulM (f x) (g x)) :=
  Formalism.FourierDecayAlt.P.B7.continuous_mulM.measurable.comp (hf.prodMk hg)

theorem meas_inv {α : Type*} [MeasurableSpace α] {f : α → Mt k r} (hf : Measurable f) :
    Measurable (fun x => Formalism.FourierDecayAlt.P.B7.invM (f x)) :=
  Formalism.FourierDecayAlt.P.B7.measurable_invM.comp hf

theorem mp_lmul {U : Set (B.Mat k r)} {μ : Measure (Mt k r)} (h : B.IsHaarOn U μ) {a : B.Mat k r} (ha : a ∈ U) :
    MeasurePreserving (lmulM a) μ μ :=
  ⟨meas_mul (f := fun _ => a) measurable_const measurable_id, h.left a ha⟩

theorem mp_rmul {U : Set (B.Mat k r)} {μ : Measure (Mt k r)} (h : B.IsHaarOn U μ) {a : B.Mat k r} (ha : a ∈ U) :
    MeasurePreserving (B.rmulF a) μ μ :=
  ⟨meas_mul (g := fun _ => a) measurable_id measurable_const, h.right a ha⟩

theorem mp_inv {U : Set (B.Mat k r)} {μ : Measure (Mt k r)} (hU : B2.IsClosedSubgroup U) (h : B.IsHaarOn U μ) :
    MeasurePreserving (B2.invM (k := k) (r := r)) μ μ :=
  ⟨Formalism.FourierDecayAlt.P.B7.measurable_invM, Formalism.FourierDecayAlt.P.haar_measure_inversion k r U μ hU h⟩

theorem mp_conj {z : Fin (2 * r + k + 1) → ℂ} {μ : Measure (Mt k r)} (hz : inWb k r z) (hT : 0 < Tz k r z)
    (h : B.IsHaarOn (Nset k r) μ) {a : B.Mat k r} (ha : a ∈ UWset k r z) :
    MeasurePreserving (conjM a) μ μ :=
  ⟨meas_mul (g := fun _ => (a⁻¹ : B.Mat k r)) (meas_mul (f := fun _ => a) measurable_const measurable_id)
    measurable_const, Formalism.FourierDecayAlt.P.b2_conjInvRaw_proof k r z μ hz hT h a ha⟩

theorem mp_conj_inv {z : Fin (2 * r + k + 1) → ℂ} {μ : Measure (Mt k r)} (hz : inWb k r z) (hT : 0 < Tz k r z)
    (h : B.IsHaarOn (Nset k r) μ) {a : B.Mat k r} (ha : a ∈ UWset k r z) :
    MeasurePreserving (conjInvM a) μ μ := by
  have hW := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z
  have := mp_conj hz hT h (hW.inv_mem a ha)
  have e : conjM (a⁻¹) = conjInvM a := by
    funext x
    unfold conjM conjInvM
    rw [Matrix.nonsing_inv_nonsing_inv _ (hW.unit a ha)]
  rwa [e] at this

end GlobalTheory.SParamMeas


open GlobalTheory.SParamMeas in
theorem GlobalTheory.sParam_measurePreserving : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)), 1 ≤ k → Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW → PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN → (∀ h₀ ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ n₀ ∈ Formalism.QuantumDeterminants.Nset k r, MeasurePreserving (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (((fun i j => (Matrix.of p.1 * h₀ : Mx k r) i j), (fun i j => (h₀⁻¹ * Matrix.of p.2 * h₀ * n₀ : Mx k r) i j)) : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (μW.prod μN) (μW.prod μN) ∧ MeasurePreserving (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (((fun i j => (h₀ * Matrix.of p.1 : Mx k r) i j), (fun i j => ((Matrix.of p.1)⁻¹ * n₀ * Matrix.of p.1 * Matrix.of p.2 : Mx k r) i j)) : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (μW.prod μN) (μW.prod μN)) ∧ MeasurePreserving (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (((fun i j => ((Matrix.of p.1)⁻¹ : Mx k r) i j), (fun i j => (Matrix.of p.1 * (Matrix.of p.2)⁻¹ * (Matrix.of p.1)⁻¹ : Mx k r) i j)) : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (μW.prod μN) (μW.prod μN) ∧ MeasurePreserving (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (((fun i j => (Matrix.of p.1 : Mx k r) i j), (fun i j => (Matrix.of p.1 * Matrix.of p.2 * (Matrix.of p.1)⁻¹ : Mx k r) i j)) : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (μW.prod μN) (μW.prod μN) ∧ MeasurePreserving (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (((fun i j => (Matrix.of p.1 : Mx k r) i j), (fun i j => ((Matrix.of p.1)⁻¹ * Matrix.of p.2 * Matrix.of p.1 : Mx k r) i j)) : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (μW.prod μN) (μW.prod μN) ∧ MeasurePreserving (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (((fun i j => ((Matrix.of p.1)⁻¹ : Mx k r) i j), (fun i j => ((Matrix.of p.2)⁻¹ : Mx k r) i j)) : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (μW.prod μN) (μW.prod μN) ∧ ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r := by
  intro k r z μW μN hk hz hT hW0 hN0
  have hW : B.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW := ((GlobalTheory.HaarNotions.isHaarOn_iff_groups k r μW).2.2 z hz hT hk).1 hW0
  have hN : B.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN := (GlobalTheory.HaarNotions.isHaarOn_iff_groups k r μN).2.1.1 hN0
  have := hW0.1
  have := hN0.1
  have cW := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z
  have cN := Formalism.FourierDecayAlt.P.unipotent_radical_closed k r
  have aW := Formalism.FourierDecayAlt.P.B7.ae_mem hW
  have aN := Formalism.FourierDecayAlt.P.B7.ae_mem hN
  have m1 : Measurable (Prod.fst : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r → _) := measurable_fst
  have m2 : Measurable (Prod.snd : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r → _) := measurable_snd
  refine ⟨fun h₀ hh n₀ hn => ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact (mp_rmul hW hh).prod ((mp_rmul hN hn).comp (mp_conj_inv hz hT hN hh))
  · have m3 : Measurable (fun _ : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of.symm n₀ : Formalism.QuantumDeterminants.Mt k r)) :=
      measurable_const
    refine (mp_lmul hW hh).skew_product
      (g := fun (a x : Formalism.QuantumDeterminants.Mt k r) => Formalism.QuantumDeterminants.lmulM ((Matrix.of a)⁻¹ * n₀ * Matrix.of a) x)
      (meas_mul (meas_mul (meas_mul (meas_inv m1) m3) m1) m2) ?_
    filter_upwards [aW] with a ha
    refine hN.left _ ?_
    have := (Formalism.QuantumDeterminants.unitary_weyl_normal_holds k r z hz _ (cW.inv_mem _ ha) n₀ hn).1
    rwa [Matrix.nonsing_inv_nonsing_inv _ (cW.unit _ ha)] at this
  · refine (mp_inv cW hW).skew_product
      (g := fun (a x : Formalism.QuantumDeterminants.Mt k r) => Formalism.QuantumDeterminants.conjM (Matrix.of a) (B2.invM x))
      (meas_mul (meas_mul m1 (meas_inv m2)) (meas_inv m1)) ?_
    filter_upwards [aW] with a ha
    exact ((mp_conj hz hT hN ha).comp (mp_inv cN hN)).map_eq
  · refine (MeasurePreserving.id μW).skew_product
      (g := fun (a x : Formalism.QuantumDeterminants.Mt k r) => Formalism.QuantumDeterminants.conjM (Matrix.of a) x)
      (meas_mul (meas_mul m1 m2) (meas_inv m1)) ?_
    filter_upwards [aW] with a ha
    exact (mp_conj hz hT hN ha).map_eq
  · refine (MeasurePreserving.id μW).skew_product
      (g := fun (a x : Formalism.QuantumDeterminants.Mt k r) =>
        conjInvM (Matrix.of a) x)
      (meas_mul (meas_mul (meas_inv m1) m2) m1) ?_
    filter_upwards [aW] with a ha
    exact (mp_conj_inv hz hT hN ha).map_eq
  · exact (mp_inv cW hW).prod (mp_inv cN hN)
  · exact (Measure.quasiMeasurePreserving_fst.ae aW).and (Measure.quasiMeasurePreserving_snd.ae aN)
end

section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.EmbSep

theorem v_intCast_eq_zero {C : Type} [Field C] (V : VF C) {n : ℤ} (hn : ¬ (V.l : ℤ) ∣ n) : V.v (n : C) = 0 := by
  apply _root_.UpperTheory.G2.RowLab.Sep.v_intCast_eq_zero <;> assumption

theorem exists_v_sub_eq_zero {C : Type} [Field C] (V : VF C) {I : Type} [Fintype I] (M : Matrix I I C)
    (h : ∀ i j, V.Ge 0 (M i j)) (hd : V.v M.det = 0) {j j' : I} (hj : j ≠ j') :
    ∃ i, V.v (M i j - M i j') = 0 := by
  apply _root_.UpperTheory.G2.RowLab.Sep.exists_v_sub_eq_zero <;> assumption

theorem cmEmbeddings_integral_and_distinct_mod_maximal' : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (lv : Level H) (c : Coeff lv) (T : CDVR) (io : c.F →+* T.Fr) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → ¬ (V.l : ℤ) ∣ NumberField.discr E → (∀ τ x, V.Ge 0 (emA3 io ι τ x)) ∧ ∀ τ τ' : E →+* ℂ, τ ≠ τ' → ∃ a : 𝓞 E, V.v (emA3 io ι τ a - emA3 io ι τ' a) = 0 := by
  apply _root_.UpperTheory.G2.RowLab.Sep.cmEmbeddings_integral_and_distinct_mod_maximal' <;> assumption

end GlobalTheory.EmbSep
end

section

open Formalism.REAL

theorem _root_.GlobalTheory.T.capelli_comatrix_last_row_inverts_casimir : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (m : Fin (n + 1) → ℂ), GlRel E → (∀ w v, qdet E w v = (∏ j, (w + m j)) • v) → (∀ y b, Om y b = ∑ c, E c b (y c)) → ∃ K : ℂ → ((PiLp 2 (fun _ : Fin (n + 1) => V)) →ₗ[ℂ] V), (∀ u x, K u ((u - 0) • x + Om x) = (∏ j, (u + m j)) • x (Fin.last n)) ∧ ∀ u v, K u (PiLp.single 2 (Fin.last n) v) = qdet (fun a b : Fin n => E a.castSucc b.castSucc) (u - 1) v := by
  first | exact @GlobalTheory.comatrix_last_row_inverts_casimir | exact GlobalTheory.comatrix_last_row_inverts_casimir | (intros; apply GlobalTheory.comatrix_last_row_inverts_casimir <;> assumption)
end

section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

theorem _root_.GlobalTheory.T.covariantDerivative_value_character_germs : (∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → Function.Injective (algebraMap R k) → ∀ (w0 : O) (N m n : ℕ) (I : Ideal R), (N : R) ∈ I → ∀ (a c : Fin n → O), (∀ b, star (a b) * a b = (N : O) * c b) →
    ∀ (ι : Type) [Fintype ι] (u : ι → Fin d → R) (S : Fin n → Set ι) (α : Fin n → ι → R), (∀ b, ∀ l ∈ S b, α b l - 1 ∈ I ∧ IsUnit (α b l) ∧
      (dAct k B (a b)).mulVec (fun i => algebraMap R k (u l i)) = algebraMap R k (α b l) • (fun i => algebraMap R k (u l i))) →
    (∀ b, ∀ l ∈ S b, ∀ l' ∈ S b, dotProduct (fun i => algebraMap R k (u l i)) ((bilinPart k h).mulVec ((dAct k B (c b * w0)).mulVec (fun i => algebraMap R k (u l' i)))) ∈ (algebraMap R k).range) →
    ∀ (χ : Fin n → PS R 1 d) (y : ι × Fin n → R), (∀ b, constantCoeff (χ b) = 1) → (∀ b, ∀ l ∈ S b, Dof B.G.F (u l) (χ b) = C (y (l, b)) * χ b) →
    ∀ P : MvPolynomial (ι × Fin n) R, (∀ mo ∈ P.support, ∀ l b, mo (l, b) ≠ 0 → l ∈ S b) →
    ∃ g : Fin n → PS R 1 d, ∃ r ∈ I, ∑ mo ∈ P.support, algebraMap R k (P.coeff mo) *
      ∏ b, B.nabVal k h w0 m (FB.toK k (g b)) (fun l i => algebraMap R k (u l i)) (MvPolynomial.monomial (colM mo b) 1) =
        algebraMap R k (MvPolynomial.eval y P + r)) := by
  first | exact @GlobalTheory.nabVal_character_columns_of_canonGauge | exact GlobalTheory.nabVal_character_columns_of_canonGauge | (intros; apply GlobalTheory.nabVal_character_columns_of_canonGauge <;> assumption)
end
