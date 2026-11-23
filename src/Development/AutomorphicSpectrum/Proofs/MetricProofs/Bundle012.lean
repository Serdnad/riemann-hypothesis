module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.InFlagDomainOne
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsOrthFull
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Bundle002
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle009
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle001
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Topology.Instances.Matrix
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle010
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Monotonicity.Lemmas
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Presheaf
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshPoisson
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.FubiniLevi
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Statements
public import Mathlib.Algebra.Module.Projective

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

open Matrix Topology
open scoped ComplexOrder

theorem posDef_eventually_of_continuous {X n : Type*} [TopologicalSpace X] [Fintype n] [DecidableEq n]
    (A : X → Matrix n n ℂ) (hc : ∀ i j, Continuous fun x => A x i j)
    (hH : ∀ x, (A x).IsHermitian) (x0 : X) (h0 : (A x0).PosDef) :
    ∀ᶠ x in 𝓝 x0, (A x).PosDef := by
  set K : Set (n → ℂ) := Metric.sphere 0 1 with hKdef
  have hK : IsCompact K := isCompact_sphere 0 1
  have hQ : Continuous fun z : X × (n → ℂ) => (star z.2 ⬝ᵥ (A z.1 *ᵥ z.2)).re := by
    simp only [dotProduct, mulVec]
    refine Complex.continuous_re.comp (continuous_finsetSum _ fun i _ => ?_)
    exact (continuous_star.comp ((continuous_apply i).comp continuous_snd)).mul
      (continuous_finsetSum _ fun j _ =>
        ((hc i j).comp continuous_fst).mul ((continuous_apply j).comp continuous_snd))
  have hP : ∀ y ∈ K, ∀ᶠ z : X × (n → ℂ) in 𝓝 (x0, y),
      0 < (star z.2 ⬝ᵥ (A z.1 *ᵥ z.2)).re := by
    intro y hy
    have hy0 : y ≠ 0 := by rintro rfl; simp [hKdef] at hy
    have h := h0.dotProduct_mulVec_pos hy0
    rw [Complex.lt_def] at h
    exact (hQ.tendsto (x0, y)).eventually_const_lt (by simpa using h.1)
  filter_upwards [hK.eventually_forall_of_forall_eventually
    (P := fun x y => 0 < (star y ⬝ᵥ (A x *ᵥ y)).re) hP] with x hx
  refine PosDef.of_dotProduct_mulVec_pos (hH x) fun y hy => ?_
  have hn : 0 < ‖y‖ := norm_pos_iff.2 hy
  have hyK : ((‖y‖⁻¹ : ℝ) : ℂ) • y ∈ K := by
    simp [hKdef, norm_smul, hn.ne']
  have h1 := hx _ hyK
  have e : star (((‖y‖⁻¹ : ℝ) : ℂ) • y) ⬝ᵥ (A x *ᵥ (((‖y‖⁻¹ : ℝ) : ℂ) • y)) =
      ((‖y‖⁻¹ ^ 2 : ℝ) : ℂ) * (star y ⬝ᵥ (A x *ᵥ y)) := by
    rw [star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul]
    simp only [smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
    push_cast; ring
  rw [e, Complex.re_ofReal_mul] at h1
  have him : (star y ⬝ᵥ (A x *ᵥ y)).im = 0 := by
    rw [← Complex.conj_eq_iff_im]

    simp only [dotProduct, mulVec, map_sum, map_mul, Pi.star_apply, Complex.star_def,
    Complex.conj_conj, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have h := (hH x).apply i j
    rw [Complex.star_def] at h
    rw [h]; ring
  rw [Complex.lt_def]
  refine ⟨?_, by simpa using him.symm⟩
  have := pos_of_mul_pos_right h1 (by positivity)
  simpa using this

theorem gramOf_isHermitian {N : ℕ} (hd : Fin N → ℝ) (g : Matrix (Fin N) (Fin N) ℂ) :
    (gramOf hd g).IsHermitian := by
  unfold gramOf
  refine isHermitian_conjTranspose_mul_mul g ?_
  ext i j
  by_cases h : i = j
  · subst h; simp
  · simp [diagonal_apply, h, Ne.symm h]

theorem continuous_gramHead {N : ℕ} (hd : Fin N → ℝ) (k : ℕ) :
    Continuous fun g : Matrix (Fin N) (Fin N) ℂ => gramHead hd k g := by
  unfold gramHead gramOf
  exact (((continuous_id.matrix_conjTranspose).matrix_mul continuous_const).matrix_mul
    continuous_id).matrix_submatrix _ _

theorem isOpen_inFlagDomain (N j : ℕ) :
    IsOpen {g : Matrix (Fin N) (Fin N) ℂ | InFlagDomain N j g} := by
  have h1 : IsOpen {g : Matrix (Fin N) (Fin N) ℂ | IsUnit g.det} := by
    simp only [isUnit_iff_ne_zero]
    exact isOpen_ne_fun (continuous_id.matrix_det) continuous_const
  have h2 : IsOpen {g : Matrix (Fin N) (Fin N) ℂ | (-gramHead (sigForm N j) (N - j) g).PosDef} := by
    refine isOpen_iff_mem_nhds.2 fun g0 hg0 => ?_
    refine posDef_eventually_of_continuous (fun g => -gramHead (sigForm N j) (N - j) g) (fun a b => ?_)
      (fun g => ?_) g0 hg0
    · exact ((continuous_gramHead _ _).neg).matrix_elem a b
    · exact ((gramOf_isHermitian _ g).submatrix _).neg
  exact h1.inter h2

theorem gramOf_mul_of_preserves {N : ℕ} (hd : Fin N → ℝ) (u g : Matrix (Fin N) (Fin N) ℂ)
    (hu : gramOf hd u = diagonal (fun i => ((hd i : ℝ) : ℂ))) :
    gramOf hd (u * g) = gramOf hd g := by
  unfold gramOf at hu ⊢
  rw [conjTranspose_mul]
  calc gᴴ * uᴴ * diagonal (fun i => ((hd i : ℝ) : ℂ)) * (u * g)
      = gᴴ * (uᴴ * diagonal (fun i => ((hd i : ℝ) : ℂ)) * u) * g := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hu]

theorem gramHead_of_triangular {N : ℕ} (hd : Fin N → ℝ) (k : ℕ) (b : Matrix (Fin N) (Fin N) ℂ)
    (hb : b.BlockTriangular id) :
    gramHead hd k b = (b.submatrix Subtype.val Subtype.val)ᴴ *
      diagonal (fun a : {a : Fin N // (a : ℕ) < k} => ((hd a : ℝ) : ℂ)) *
      b.submatrix Subtype.val Subtype.val := by
  ext i j
  simp only [gramHead, gramOf, submatrix_apply]
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [mul_diagonal, conjTranspose_apply, submatrix_apply]
  rw [← Finset.sum_subtype (Finset.univ.filter fun a : Fin N => (a : ℕ) < k) (by simp)
    (fun l => star (b l i.1) * ((hd l : ℝ) : ℂ) * b l j.1)]
  rw [Finset.sum_filter_of_ne]
  intro l _ hl
  by_contra hlk
  apply hl
  have : b l i.1 = 0 := hb (by
    show i.1 < l
    have := i.2
    exact Fin.lt_def.2 (by omega))
  simp [this]

theorem sigForm_apply_ne_zero (N j : ℕ) (a : Fin N) : sigForm N j a ≠ 0 := by
  unfold sigForm; split_ifs <;> norm_num

theorem gramHead_det_ne_zero_of_triangular {N : ℕ} (hd : Fin N → ℝ) (hd0 : ∀ a, hd a ≠ 0) (k : ℕ)
    (b : Matrix (Fin N) (Fin N) ℂ) (hb : b.BlockTriangular id) (hu : IsUnit b.det) :
    (gramHead hd k b).det ≠ 0 := by
  have hbd : ∀ i, b i i ≠ 0 := by
    have h := (isUnit_iff_ne_zero.1 hu)
    rw [det_of_upperTriangular hb] at h
    exact fun i => (Finset.prod_ne_zero_iff.1 h) i (Finset.mem_univ i)
  have hs : (b.submatrix (Subtype.val : {a : Fin N // (a : ℕ) < k} → Fin N) Subtype.val).det ≠ 0 := by
    have ht : (b.submatrix (Subtype.val : {a : Fin N // (a : ℕ) < k} → Fin N) Subtype.val).BlockTriangular id :=
      fun i j hij => hb hij
    rw [det_of_upperTriangular ht]
    exact Finset.prod_ne_zero_iff.2 fun i _ => hbd i.1
  rw [gramHead_of_triangular hd k b hb, det_mul, det_mul, det_conjTranspose, det_diagonal]
  refine mul_ne_zero (mul_ne_zero (star_ne_zero.2 hs) ?_) hs
  exact Finset.prod_ne_zero_iff.2 fun a _ => Complex.ofReal_ne_zero.2 (hd0 a)

theorem gramHead_det_ne_zero (N j : ℕ) (hj : j ≤ N) (g : Matrix (Fin N) (Fin N) ℂ)
    (hg : InFlagDomain N j g) (k : ℕ) : (gramHead (sigForm N j) k g).det ≠ 0 := by
  obtain ⟨u, b, hu, hb, hbu, hug⟩ := GlobalTheory.T.flag_domain_unitary_triangular N j hj g hg
  have e : gramHead (sigForm N j) k g = gramHead (sigForm N j) k b := by
    unfold gramHead
    rw [← hug, gramOf_mul_of_preserves _ _ _ hu]
  rw [e]
  exact gramHead_det_ne_zero_of_triangular _ (sigForm_apply_ne_zero N j) k b hb hbu

theorem flagDomain_open_and_minors : ∀ (N j : ℕ), j ≤ N →
    IsOpen {g : Matrix (Fin N) (Fin N) ℂ | InFlagDomain N j g} ∧
      ∀ g : Matrix (Fin N) (Fin N) ℂ, InFlagDomain N j g → ∀ k,
        (gramHead (sigForm N j) k g).det ≠ 0 :=
  fun N j hj => ⟨isOpen_inFlagDomain N j, fun g hg k => gramHead_det_ne_zero N j hj g hg k⟩

end GlobalTheory.CompanionTheory.Ar.PB
end
end

section

open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Decomp

theorem normDegree_step_zero {K : Type} [Field K] [NumberField K] {E : HermitianBundle.{0} K} {r : ℕ}
    (A : SatFlag E r) : E.normDegree (A.F 0) = 0 := by
  have h : A.F 0 = ⊥ := (Submodule.finrank_eq_zero (R := 𝓞 K) (S := A.F 0)).mp (A.rank 0)
  rw [HermitianBundle.normDegree, h, HermitianBundle.degree_bot, zero_div]

theorem lamDeg_eq : ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (Ψ : Type) [Fintype Ψ] (j k : ℕ) (A : FlagPair E Ψ (j + 1) (k + 1)) (lam : Ψ → Fin (j + 1 + (k + 1)) → ℝ), A.lamDeg lam = ∑ τ, ((∑ i : Fin j, (lam τ (Fin.castAdd (k + 1) i.castSucc) - lam τ (Fin.castAdd (k + 1) i.succ)) * (-E.normDegree ((A.W τ).F i.succ.castSucc))) + (lam τ (Fin.castAdd (k + 1) (Fin.last j)) - lam τ (Fin.natAdd (j + 1) 0)) * (-E.normDegree (A.W τ).top) + (∑ i : Fin k, (lam τ (Fin.natAdd (j + 1) i.castSucc) - lam τ (Fin.natAdd (j + 1) i.succ)) * (-E.normDegree ((A.S τ).F i.rev.succ.castSucc))) - lam τ (Fin.natAdd (j + 1) 0) * A.flatDeg τ) := by
  intro K _ _ E Ψ _ j k A lam
  unfold FlagPair.lamDeg
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hW := GlobalTheory.CompanionTheory.AbelFlag.abel_summation_flag j (fun i => lam τ (Fin.castAdd (k + 1) i))
    (fun i => E.normDegree ((A.W τ).F i)) (normDegree_step_zero (A.W τ))
  have hS := GlobalTheory.CompanionTheory.DualFlag.abel_sum_rev k (fun i => lam τ (Fin.natAdd (j + 1) i))
    (fun i => E.normDegree ((A.S τ).F i)) (normDegree_step_zero (A.S τ))
  simp only [SatFlag.grDeg, FlagPair.flatDeg, SatFlag.top]
  linear_combination hW + hS

end GlobalTheory.CompanionTheory.Ar.Decomp
end

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights

theorem _root_.GlobalTheory.T.vandermonde_product_weight_positive : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (Q : MvPolynomial (Ψ × Fin N) ℝ) (v : ℝ), (∀ c : Ψ × Fin N → ℝ, eval c Q = v * ∏ τ : Ψ, ∏ i : Fin N, ∏ l ∈ Finset.Ioi i, ∑ m ∈ Finset.Ico i l, c (τ, m)) → toWt Q = C v * antisymDelta Ψ N ∧ 0 < eval (rhoWt Ψ N) (antisymDelta Ψ N) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.toWt_eq_C_mul_antisymDelta | exact GlobalTheory.CompanionTheory.Ar.PB.toWt_eq_C_mul_antisymDelta | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.toWt_eq_C_mul_antisymDelta <;> assumption)
end

section

open MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar.PB.Flat
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.PuncturedDisc

theorem le_zero_of_bddAbove_punctured (g : ℂ → ℝ) (ρ C : ℝ) (hρ : 0 < ρ)
    (hc : ContinuousOn g {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ ≤ ρ})
    (hh : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ρ → InnerProductSpace.HarmonicAt g z)
    (h0 : ∀ z : ℂ, ‖z‖ = ρ → g z ≤ 0)
    (hC : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ ≤ ρ → g z ≤ C) :
    ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < ρ → g w ≤ 0 := by
  intro w hw0 hwρ
  have hlogw : Real.log ‖w‖ < Real.log ρ := Real.log_lt_log hw0 hwρ
  have hD : 0 < Real.log ρ - Real.log ‖w‖ := sub_pos.mpr hlogw
  have key : ∀ ε : ℝ, 0 < ε → g w ≤ ε * (Real.log ρ - Real.log ‖w‖) := by
    intro ε hε
    have hexp_pos : 0 < Real.exp (-(|C| / ε)) := Real.exp_pos _
    have hexp_le : Real.exp (-(|C| / ε)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ |C| / ε := div_nonneg (abs_nonneg C) hε.le
      linarith
    obtain ⟨r, hr_def⟩ : ∃ r : ℝ, r = ‖w‖ * Real.exp (-(|C| / ε)) / 2 := ⟨_, rfl⟩
    have hr0 : 0 < r := by
      rw [hr_def]
      exact div_pos (mul_pos hw0 hexp_pos) two_pos
    have hrw : r < ‖w‖ := by
      have := mul_le_mul_of_nonneg_left hexp_le hw0.le
      rw [hr_def]
      linarith
    have hrρ : r < ρ := lt_trans hrw hwρ
    have hlogr : Real.log r = Real.log ‖w‖ - |C| / ε - Real.log 2 := by
      rw [hr_def, Real.log_div (mul_pos hw0 hexp_pos).ne' two_ne_zero,
        Real.log_mul hw0.ne' hexp_pos.ne', Real.log_exp]
      ring
    let h : ℂ → ℝ := fun z => g z - ε * (Real.log ρ - Real.log ‖z‖)
    have hcont : ContinuousOn h {z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ ≤ ρ} := by
      have hsub : {z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ ≤ ρ} ⊆ {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ ≤ ρ} :=
        fun z hz => ⟨lt_of_lt_of_le hr0 hz.1, hz.2⟩
      refine (hc.mono hsub).sub (continuousOn_const.mul (continuousOn_const.sub ?_))
      refine ContinuousOn.log continuous_norm.continuousOn ?_
      intro z hz
      exact (lt_of_lt_of_le hr0 hz.1).ne'
    have hharm : ∀ z : ℂ, r < ‖z‖ → ‖z‖ < ρ → InnerProductSpace.HarmonicAt h z := by
      intro z hz1 hz2
      have hz0 : 0 < ‖z‖ := lt_trans hr0 hz1
      have hlog : InnerProductSpace.HarmonicAt (fun y : ℂ => Real.log ‖y‖) z :=
        analyticAt_id.harmonicAt_log_norm (norm_pos_iff.mp hz0)
      have hcst : InnerProductSpace.HarmonicAt (fun _ : ℂ => Real.log ρ) z :=
        InnerProductSpace.harmonicAt_const _
      have h2 : InnerProductSpace.HarmonicAt
          (ε • ((fun _ : ℂ => Real.log ρ) - fun y : ℂ => Real.log ‖y‖)) z := by
        apply InnerProductSpace.HarmonicAt.const_smul
        exact hcst.sub hlog
      exact (hh z hz0 hz2).sub h2
    have hbdry : ∀ z : ℂ, ‖z‖ = r ∨ ‖z‖ = ρ → h z ≤ 0 := by
      intro z hz
      rcases hz with hz | hz
      · have hgz : g z ≤ C := hC z (by rw [hz]; exact hr0) (by rw [hz]; exact hrρ.le)
        have hCabs : C ≤ |C| := le_abs_self C
        have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
        show g z - ε * (Real.log ρ - Real.log ‖z‖) ≤ 0
        rw [hz, hlogr]
        have e1 : ε * (Real.log ρ - (Real.log ‖w‖ - |C| / ε - Real.log 2)) =
            ε * (Real.log ρ - Real.log ‖w‖) + ε * (|C| / ε) + ε * Real.log 2 := by ring
        have e2 : ε * (|C| / ε) = |C| := by field_simp
        rw [e1, e2]
        linarith [mul_pos hε hD, mul_pos hε hlog2]
      · show g z - ε * (Real.log ρ - Real.log ‖z‖) ≤ 0
        rw [hz, sub_self, mul_zero, sub_zero]
        exact h0 z hz
    have hmax := GlobalTheory.T.harmonic_annulus_maximum_principle h r ρ hr0 hrρ hcont hharm hbdry w hrw.le hwρ.le
    simp only [h] at hmax
    linarith
  by_contra hneg
  have hpos := not_le.mp hneg
  have hk := key (g w / (2 * (Real.log ρ - Real.log ‖w‖))) (div_pos hpos (mul_pos two_pos hD))
  have e3 : g w / (2 * (Real.log ρ - Real.log ‖w‖)) * (Real.log ρ - Real.log ‖w‖) = g w / 2 := by
    rw [div_mul_eq_mul_div, mul_div_mul_right _ _ hD.ne']
  linarith

theorem poisson_formula_punctured (f : ℂ → ℝ) (ρ R M : ℝ) (hρ : 0 < ρ) (hρR : ρ < R)
    (hH : ∀ z : ℂ, z ≠ 0 → ‖z‖ < R → InnerProductSpace.HarmonicAt f z)
    (hB : ∀ z : ℂ, z ≠ 0 → ‖z‖ < R → |f z| ≤ M) (w : ℂ) (hw0 : w ≠ 0) (hwρ : ‖w‖ < ρ) :
    ∫ t, pker ρ w t * f (circleMap 0 ρ t) ∂angMeas = f w := by
  have hρabs : |ρ| = ρ := abs_of_pos hρ
  have hfc : ContinuousOn f (Metric.sphere 0 ρ) := by
    intro z hz
    have hz' : ‖z‖ = ρ := by simpa using hz
    have hz0 : z ≠ 0 := by
      intro h
      rw [h, norm_zero] at hz'
      linarith
    exact (hH z hz0 (by rw [hz']; exact hρR)).1.continuousAt.continuousWithinAt
  have hPbd : ∀ z : ℂ, ‖z‖ < ρ → |ReciprocityTheory.AnForm.A.poissonInt f ρ z| ≤ M := by
    intro z hz
    have hzb : z ∈ Metric.ball (0 : ℂ) ρ := by simpa using hz
    have hup := ReciprocityTheory.AnForm.A.poissonInt_sub hρ hfc hzb M
    have hlo := ReciprocityTheory.AnForm.A.poissonInt_sub hρ hfc hzb (-M)
    have hsph : ∀ x ∈ Metric.sphere (0 : ℂ) |ρ|, |f x| ≤ M ∧ 0 ≤ poissonKernel 0 z x := by
      intro x hx
      rw [hρabs] at hx
      have hx' : ‖x‖ = ρ := by simpa using hx
      have hx0 : x ≠ 0 := by
        intro h
        rw [h, norm_zero] at hx'
        linarith
      exact ⟨hB x hx0 (by rw [hx']; exact hρR), ReciprocityTheory.AnForm.A.poissonKernel_zero_nonneg hzb hx⟩
    have h1 : 0 ≤ Real.circleAverage (fun x => -(poissonKernel 0 z x * (f x - M))) 0 ρ :=
      Real.circleAverage_nonneg_of_nonneg fun x hx => by
        obtain ⟨hb, hk⟩ := hsph x hx
        have := (abs_le.mp hb).2
        have : 0 ≤ poissonKernel 0 z x * (M - f x) := mul_nonneg hk (by linarith)
        linarith
    have h1' : Real.circleAverage (fun x => -(poissonKernel 0 z x * (f x - M))) 0 ρ =
        -Real.circleAverage (fun x => poissonKernel 0 z x * (f x - M)) 0 ρ := by
      simp only [Real.circleAverage, intervalIntegral.integral_neg, smul_neg]
    have h2 : 0 ≤ Real.circleAverage (fun x => poissonKernel 0 z x * (f x - -M)) 0 ρ :=
      Real.circleAverage_nonneg_of_nonneg fun x hx => by
        obtain ⟨hb, hk⟩ := hsph x hx
        have := (abs_le.mp hb).1
        exact mul_nonneg hk (by linarith)
    rw [abs_le]
    constructor <;> linarith
  let Φ : ℂ → ℝ := fun z => if ‖z‖ < ρ then ReciprocityTheory.AnForm.A.poissonInt f ρ z else f z
  have hPharm : ∀ z : ℂ, ‖z‖ < ρ → InnerProductSpace.HarmonicAt Φ z := by
    intro z hz
    have hzb : z ∈ Metric.ball (0 : ℂ) ρ := by simpa using hz
    have hev : Φ =ᶠ[𝓝 z] ReciprocityTheory.AnForm.A.poissonInt f ρ := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hzb] with y hy
      have : ‖y‖ < ρ := by simpa using hy
      simp only [Φ, if_pos this]
    exact (InnerProductSpace.harmonicAt_congr_nhds hev).mpr
      (ReciprocityTheory.AnForm.A.poissonInt_harmonicAt hρ hfc hzb)
  have hΦcont : ContinuousOn Φ (Metric.closedBall 0 ρ) := by
    intro z hz
    by_cases hzl : ‖z‖ < ρ
    · exact (hPharm z hzl).1.continuousAt.continuousWithinAt
    · have hzle : ‖z‖ ≤ ρ := by simpa using hz
      have hzeq : ‖z‖ = ρ := le_antisymm hzle (not_lt.mp hzl)
      have hzs : z ∈ Metric.sphere (0 : ℂ) ρ := by simpa using hzeq
      have hΦz : Φ z = f z := by simp only [Φ, if_neg hzl]
      rw [← Metric.ball_union_sphere]
      apply ContinuousWithinAt.union
      · rw [ContinuousWithinAt, hΦz]
        refine Filter.Tendsto.congr' ?_ (ReciprocityTheory.AnForm.A.poissonInt_tendsto hρ hfc hzs)
        filter_upwards [self_mem_nhdsWithin] with y hy
        have : ‖y‖ < ρ := by simpa using hy
        simp only [Φ, if_pos this]
      · rw [ContinuousWithinAt, hΦz]
        refine Filter.Tendsto.congr' ?_ (hfc z hzs)
        filter_upwards [self_mem_nhdsWithin] with y hy
        have hy' : ‖y‖ = ρ := by simpa using hy
        simp only [Φ, if_neg (not_lt.mpr hy'.ge)]
  have hΦb : ∀ z : ℂ, ‖z‖ = ρ → Φ z = f z := by
    intro z hz
    simp only [Φ, if_neg (not_lt.mpr hz.ge)]
  have hS : {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ ≤ ρ} ⊆ Metric.closedBall 0 ρ := fun z hz => by
    simpa using hz.2
  have hfS : ContinuousOn f {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ ≤ ρ} := fun z hz =>
    (hH z (norm_pos_iff.mp hz.1) (lt_of_le_of_lt hz.2 hρR)).1.continuousAt.continuousWithinAt
  have hΦbd : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ ≤ ρ → |Φ z| ≤ M := by
    intro z hz0 hzρ
    by_cases hzl : ‖z‖ < ρ
    · simp only [Φ, if_pos hzl]
      exact hPbd z hzl
    · simp only [Φ, if_neg hzl]
      exact hB z (norm_pos_iff.mp hz0) (lt_of_le_of_lt hzρ hρR)
  have hA := le_zero_of_bddAbove_punctured (fun z => f z - Φ z) ρ (2 * M) hρ
    (hfS.sub (hΦcont.mono hS))
    (fun z hz0 hzρ => (hH z (norm_pos_iff.mp hz0) (lt_trans hzρ hρR)).sub (hPharm z hzρ))
    (fun z hz => by simp only [hΦb z hz, sub_self, le_refl])
    (fun z hz0 hzρ => by
      have h1 := abs_le.mp (hB z (norm_pos_iff.mp hz0) (lt_of_le_of_lt hzρ hρR))
      have h2 := abs_le.mp (hΦbd z hz0 hzρ)
      linarith [h1.1, h1.2, h2.1, h2.2])
    w (norm_pos_iff.mpr hw0) hwρ
  have hA' := le_zero_of_bddAbove_punctured (fun z => Φ z - f z) ρ (2 * M) hρ
    ((hΦcont.mono hS).sub hfS)
    (fun z hz0 hzρ => (hPharm z hzρ).sub (hH z (norm_pos_iff.mp hz0) (lt_trans hzρ hρR)))
    (fun z hz => by simp only [hΦb z hz, sub_self, le_refl])
    (fun z hz0 hzρ => by
      have h1 := abs_le.mp (hB z (norm_pos_iff.mp hz0) (lt_of_le_of_lt hzρ hρR))
      have h2 := abs_le.mp (hΦbd z hz0 hzρ)
      linarith [h1.1, h1.2, h2.1, h2.2])
    w (norm_pos_iff.mpr hw0) hwρ
  have hΦw : Φ w = ReciprocityTheory.AnForm.A.poissonInt f ρ w := by simp only [Φ, if_pos hwρ]
  have hfw : f w = ReciprocityTheory.AnForm.A.poissonInt f ρ w := by linarith
  rw [hfw]
  have hint := GlobalTheory.CompanionTheory.Ar.PB.Flat.integral_angMeas (fun z => poissonKernel 0 w z * f z) ρ
  exact hint

end GlobalTheory.CompanionTheory.Ar.PuncturedDisc
end

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

namespace GlobalTheory.CompanionTheory.Ar.QuotUniv

theorem ringAction_descends_along_surjection
    (O : Type) [Ring O] (g g' : ℕ) (B : O →+* Module.End ℂ (Fin g → ℂ))
    (q : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (hq : Function.Surjective q)
    (hk : ∀ (a : O) z, q z = 0 → q (B a z) = 0) :
    ∃ B' : O →+* Module.End ℂ (Fin g' → ℂ), ∀ a z, B' a (q z) = q (B a z) := by
  obtain ⟨s, hs⟩ := q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hq)
  have hqs : ∀ w, q (s w) = w := fun w => LinearMap.congr_fun hs w
  obtain ⟨F, hF⟩ : ∃ F : O → Module.End ℂ (Fin g' → ℂ), ∀ a z, F a (q z) = q (B a z) := by
    refine ⟨fun a => q ∘ₗ (B a ∘ₗ s), fun a z => ?_⟩
    have h0 : q (B a (s (q z) - z)) = 0 := hk a _ (by rw [map_sub, hqs, sub_self])
    rw [map_sub, map_sub, sub_eq_zero] at h0
    exact h0
  have hext : ∀ L M : Module.End ℂ (Fin g' → ℂ), (∀ z, L (q z) = M (q z)) → L = M := by
    intro L M h
    refine LinearMap.ext fun w => ?_
    obtain ⟨z, rfl⟩ := hq w
    exact h z
  refine ⟨{ toFun := F, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ },
    fun a z => hF a z⟩
  · exact hext _ _ fun z => by simp [hF]
  · intro a b
    exact hext _ _ fun z => by simp [hF, Module.End.mul_apply]
  · exact hext _ _ fun z => by simp [hF]
  · intro a b
    exact hext _ _ fun z => by simp [hF]

end GlobalTheory.CompanionTheory.Ar.QuotUniv
end
