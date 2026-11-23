module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle035
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle003
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle025
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Mathlib.Algebra.Module.ZLattice.Summable
public import Formalism.GradedWeylDivisibility.StatementA
public import Formalism.LocalToGlobal.HermitianForms.Bundle001
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle045
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LFunctionConjEqZero
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.OrderNeTop
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle041
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle034
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle004
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle003
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

namespace GlobalTheory.FibrePositive

theorem act_mul {P Q : ℕ} (g h : UpqT P Q) (x : ActionCoordinates.Wsp P Q) :
    ActionCoordinates.act (g * h) x = ActionCoordinates.act g (ActionCoordinates.act h x) := by
  have : UpqT.mat (g * h) = UpqT.mat g * UpqT.mat h := rfl
  simp only [ActionCoordinates.act, this, Matrix.mulVec_mulVec]

theorem act_one {P Q : ℕ} (x : ActionCoordinates.Wsp P Q) : ActionCoordinates.act (1 : UpqT P Q) x = x := by
  have : UpqT.mat (1 : UpqT P Q) = 1 := rfl
  simp only [ActionCoordinates.act, this, Matrix.one_mulVec]

theorem act_inv_of_fix {P Q : ℕ} {g : UpqT P Q} {x : ActionCoordinates.Wsp P Q} (h : ActionCoordinates.act g x = x) :
    ActionCoordinates.act g⁻¹ x = x := by
  conv_lhs => rw [← h]
  rw [← act_mul, inv_mul_cancel, act_one]

theorem fibre_lintegral_ne_zero : ActionCoordinates.QuotientMeasure → CDHaar → ∀ (P Q : ℕ) (β : ℝ), (β = 1 ∨ β = -1) → ∀ x₀ : ActionCoordinates.Wsp P Q, ActionCoordinates.qf x₀ = β → ∀ fib : ℝ → Measure (ActionCoordinates.Wsp P Q), ActionCoordinates.IsDxDq β fib → ∀ φ : ActionCoordinates.Wsp P Q → ℝ, Continuous φ → 0 < φ x₀ → ∫⁻ y, ENNReal.ofReal (φ y) ∂(fib β) ≠ 0 := by
  intro hQ c P Q β hβ x₀ hx₀ fib hfib φ hφ hpos h0
  obtain ⟨h1, ⟨P', Q', j, ι, -, -, hfr⟩, h3⟩ := hQ P Q β hβ x₀ hx₀
  obtain ⟨htop, -, -, -, hbor, hcl⟩ := GlobalTheory.UpqTopology.upq_lcsc P Q
  classical
  choose s0 hs0 using h1
  let s : ActionCoordinates.Wsp P Q → UpqT P Q := fun y => if h : ActionCoordinates.qf y = β then s0 y h else 1
  have hs : ∀ y, ActionCoordinates.qf y = β → ActionCoordinates.act (s y)⁻¹ x₀ = y := by
    intro y hy
    simp only [s, dif_pos hy]
    exact hs0 y hy
  have hc : Continuous fun g : UpqT P Q => ActionCoordinates.act g⁻¹ x₀ :=
    (hcl.continuous.comp continuous_inv).matrix_mulVec continuous_const
  have hfc : Continuous fun g : UpqT P Q => ENNReal.ofReal (φ (ActionCoordinates.act g⁻¹ x₀)) :=
    ENNReal.continuous_ofReal.comp (hφ.comp hc)
  have key := (h3 P' Q' j ι hfr).2 c fib hfib s hs _ hfc.measurable
  have hφm : Measurable fun y => ENNReal.ofReal (φ y) :=
    (ENNReal.continuous_ofReal.comp hφ).measurable
  have hae := (lintegral_eq_zero_iff hφm).1 h0
  have hqm : MeasurableSet {y : ActionCoordinates.Wsp P Q | ActionCoordinates.qf y = β} := by
    have : Continuous (ActionCoordinates.qf : ActionCoordinates.Wsp P Q → ℝ) := by
      unfold ActionCoordinates.qf ActionCoordinates.herm
      fun_prop
    exact (isClosed_eq this continuous_const).measurableSet
  have hR : ∫⁻ y in {y | ActionCoordinates.qf y = β}, (∫⁻ g', ENNReal.ofReal (φ (ActionCoordinates.act (ι g' * s y)⁻¹ x₀))
      ∂(c.cd P' Q')) ∂(fib β) = 0 := by
    refine lintegral_eq_zero_of_ae_eq_zero ?_
    filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem hqm] with y hy hq
    have : ∀ g', ENNReal.ofReal (φ (ActionCoordinates.act (ι g' * s y)⁻¹ x₀)) = 0 := by
      intro g'
      rw [_root_.mul_inv_rev, act_mul, act_inv_of_fix (hfr.2.2 g').1, hs y hq]
      exact hy
    simp only [this, lintegral_zero, Pi.zero_apply]
  rw [hR, mul_zero] at key
  have := c.haar P Q
  have hz := (hfc.ae_eq_iff_eq (c.cd P Q) continuous_const).1 ((lintegral_eq_zero_iff hfc.measurable).1 key)
  have h1 : ENNReal.ofReal (φ (ActionCoordinates.act (1 : UpqT P Q)⁻¹ x₀)) = 0 := congrFun hz 1
  rw [inv_one, act_one, ENNReal.ofReal_eq_zero] at h1
  linarith

end GlobalTheory.FibrePositive
end

section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

namespace GlobalTheory.ExceptionalPair

theorem one_le_log {M : ℕ} (hM : 3 ≤ M) : 1 ≤ Real.log M := by
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  rw [Real.le_log_iff_exp_le (by linarith)]
  linarith [Real.exp_one_lt_d9]

theorem log_mul_le {M : ℕ} (hM : 3 ≤ M) {a : ℝ} (ha : 0 < a) (ha3 : a ≤ 3) :
    Real.log (a * M) ≤ 2 * Real.log M := by
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  rw [Real.log_mul ha.ne' hM0.ne']
  have := Real.log_le_log ha (show a ≤ (M : ℝ) by linarith)
  linarith

theorem le_log_mul {M : ℕ} (hM : 3 ≤ M) {a : ℝ} (ha : 1 ≤ a) :
    Real.log M ≤ Real.log (a * M) := by
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  exact Real.log_le_log hM0 (le_mul_of_one_le_left hM0.le ha)

theorem div_log_le {M : ℕ} (hM : 3 ≤ M) {c₁ c : ℝ} (h0 : 0 ≤ c) (h : c₁ ≤ c / 2) :
    c₁ / Real.log M ≤ c / Real.log (2 * M) := by
  have hl := log_mul_le hM (a := 2) (by norm_num) (by norm_num)
  have hpos : 0 < Real.log M := lt_of_lt_of_le one_pos (one_le_log hM)
  have hpos2 : 0 < Real.log (2 * M) := by
    linarith [le_log_mul hM (a := 2) (by norm_num)]
  rw [div_le_div_iff₀ hpos hpos2]
  nlinarith [mul_nonneg (sub_nonneg.2 h) hpos2.le, mul_nonneg h0 (sub_nonneg.2 hl)]

private theorem exists_ne_zero_smul_mem_of_mem_span' {a b x y : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hx : 0 < x) (hxy : x ≤ y) :
    a / y ≤ b / x := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  rw [div_le_div_iff₀ hy hx]
  nlinarith [mul_le_mul_of_nonneg_right hab hx.le, mul_le_mul_of_nonneg_left hxy (ha.trans hab)]

theorem main : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ c₀ → ∃ c : ℝ, 0 < c ∧ ∀ (M : ℕ) [NeZero M], 3 ≤ M → (∀ (χ χ' : DirichletCharacter ℂ M) (β β' : ℝ), IsExc c₁ χ β → IsExc c₁ χ' β' → χ = χ' ∧ β = β') ∧ (∀ (χ : DirichletCharacter ℂ M) (β : ℝ), IsExc c₁ χ β → χ ≠ 1 ∧ 7 / 8 ≤ β ∧ LFunction χ β = 0 ∧ ord χ β = 1 ∧ c / ((M : ℝ) ^ 2 * Real.log M) ≤ 1 - β) ∧ ∀ (χ : DirichletCharacter ℂ M) (ρ : ℂ), ρ.re < 1 → LFunction χ ρ = 0 → (ρ.im = 0 ∧ IsExc c₁ χ ρ.re) ∨ ρ.re ≤ 1 - c / Real.log (M * (|ρ.im| + 2)) := by
  obtain ⟨cu, hcu, hU⟩ := GlobalTheory.RealZeroNearOne.main
  obtain ⟨cp, hcp, hP⟩ := GlobalTheory.ZeroFreePrincipal.zero_free
  obtain ⟨cz, hcz, hZ⟩ := GlobalTheory.ZeroFreeComplex.zero_free_region
  obtain ⟨cs, hcs, hS⟩ := GlobalTheory.T.exists_dirichletLFunction_zero_gap_near_one
  refine ⟨min (1 / 8) (min (cu / 2) (cp / 2)),
    lt_min (by norm_num) (lt_min (by linarith) (by linarith)), fun c₁ hc₁ hc₁0 => ?_⟩
  have hc18 : c₁ ≤ 1 / 8 := hc₁0.trans (min_le_left _ _)
  have hcu2 : c₁ ≤ cu / 2 := hc₁0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hcp2 : c₁ ≤ cp / 2 := hc₁0.trans ((min_le_right _ _).trans (min_le_right _ _))
  set c := min c₁ (min cz (min cp (cs / 2))) with hcdef
  have hcpos : 0 < c := lt_min hc₁ (lt_min hcz (lt_min hcp (by linarith)))
  have hcc₁ : c ≤ c₁ := min_le_left _ _
  have hccz : c ≤ cz := (min_le_right _ _).trans (min_le_left _ _)
  have hccp : c ≤ cp := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hccs : c ≤ cs / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨c, hcpos, fun M _ hM => ?_⟩
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hlog1 : 1 ≤ Real.log M := one_le_log hM
  have hlogpos : 0 < Real.log M := lt_of_lt_of_le one_pos hlog1
  have hsmall : c₁ / Real.log M ≤ 1 / 8 := (div_le_self hc₁.le hlog1).trans hc18
  have hlogT : ∀ t : ℝ, 0 < Real.log (M * (|t| + 2)) := fun t =>
    Real.log_pos (by nlinarith [abs_nonneg t])
  have hexc : ∀ (χ : DirichletCharacter ℂ M) (β : ℝ), IsExc c₁ χ β →
      χ ≠ 1 ∧ 7 / 8 ≤ β ∧ LFunction χ β = 0 ∧ 1 - cu / Real.log (2 * M) ≤ β := by
    intro χ β h
    obtain ⟨_, hlt, hlt1, hL⟩ := h
    have hβ : 7 / 8 ≤ β := by linarith
    have hne : (β : ℂ) ≠ 1 := fun h => by
      have := congrArg Complex.re h
      simp at this
      linarith
    have hLχ : LFunction χ β = 0 :=
      (GlobalTheory.T.dirichletL_zeros_eq_primitiveCharacter_zeros M χ β (by simp; linarith) (Or.inr hne)).1.mpr hL
    refine ⟨fun hχ => ?_, hβ, hLχ, by linarith [div_log_le hM hcu.le hcu2]⟩
    rw [hχ] at hLχ
    have h1 := hP M (β : ℂ) hne hLχ
    have e : (M : ℝ) * 2 = 2 * M := mul_comm _ _
    rw [Complex.ofReal_re, Complex.ofReal_im, abs_zero, zero_add, e] at h1
    linarith [div_log_le hM hcp.le hcp2]
  refine ⟨fun χ χ' β β' h h' => ?_, fun χ β h => ?_, fun χ ρ hre hL => ?_⟩
  · obtain ⟨n1, -, L1, b1⟩ := hexc χ β h
    obtain ⟨n2, -, L2, b2⟩ := hexc χ' β' h'
    obtain ⟨s1, -⟩ := h
    obtain ⟨s2, -⟩ := h'
    obtain ⟨e1, e2, -⟩ := hU M χ χ' β β' n1 n2 s1 s2 b1 b2 L1 L2
    exact ⟨e1, e2⟩
  · obtain ⟨n1, h78, L1, b1⟩ := hexc χ β h
    obtain ⟨s1, -⟩ := h
    refine ⟨n1, h78, L1, ?_, ?_⟩
    · have hd := (hU M χ χ β β n1 n1 s1 s1 b1 b1 L1 L1).2.2
      have h1 := (GlobalTheory.RealZeroNearOne.analyticAt_L n1 (β : ℂ)).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
        L1 hd
      rw [GlobalTheory.Lin.ord, analyticOrderNatAt, h1]
      rfl
    · have h1 := hS M χ β (Or.inl n1) L1 (by simp)
      rw [Complex.ofReal_re] at h1
      have hl3 := log_mul_le hM (a := 3) (by norm_num) le_rfl
      have hl3pos : 0 < Real.log (3 * M) := Real.log_pos (by linarith)
      have hD : 0 < (M : ℝ) ^ 2 * Real.log M := by positivity
      have hE : 0 < (M : ℝ) ^ 2 * Real.log (3 * M) := by positivity
      calc c / ((M : ℝ) ^ 2 * Real.log M) ≤ (cs / 2) / ((M : ℝ) ^ 2 * Real.log M) :=
            exists_ne_zero_smul_mem_of_mem_span' hcpos.le hccs hD le_rfl
        _ = cs / (2 * ((M : ℝ) ^ 2 * Real.log M)) := div_div cs 2 _
        _ ≤ cs / ((M : ℝ) ^ 2 * Real.log (3 * M)) :=
            exists_ne_zero_smul_mem_of_mem_span' hcs.le le_rfl hE (by nlinarith [sq_nonneg (M : ℝ)])
        _ ≤ 1 - β := h1
  · by_cases hreal : χ ^ 2 = 1 ∧ ρ.im = 0
    · obtain ⟨hsq, him⟩ := hreal
      have hρ : ρ = (ρ.re : ℂ) := Complex.ext (by simp) (by simp [him])
      by_cases hbig : 1 - c₁ / Real.log M < ρ.re
      · left
        refine ⟨him, ?_⟩
        have hpos : 0 < ρ.re := by linarith
        have hne : ρ ≠ 1 := fun h => by
          rw [h] at hre
          simp at hre
        have hL' := (GlobalTheory.T.dirichletL_zeros_eq_primitiveCharacter_zeros M χ ρ hpos (Or.inr hne)).1.mp hL
        unfold IsExc
        refine ⟨hsq, hbig, hre, ?_⟩
        rw [← hρ]
        exact hL'
      · right
        replace hbig := not_lt.mp hbig
        rw [him, abs_zero, zero_add]
        have h2 : Real.log M ≤ Real.log (M * 2) := by
          rw [mul_comm]
          exact le_log_mul hM (by norm_num)
        have := exists_ne_zero_smul_mem_of_mem_span' hcpos.le hcc₁ hlogpos h2
        linarith
    · right
      have hne' : χ ^ 2 = 1 → ρ.im ≠ 0 := fun h h' => hreal ⟨h, h'⟩
      by_cases hχ : χ = 1
      · have him : ρ.im ≠ 0 := hne' (by rw [hχ]; exact one_pow 2)
        have hne : ρ ≠ 1 := fun h => him (by rw [h]; simp)
        rw [hχ] at hL
        have h1 := hP M ρ hne hL
        have := exists_ne_zero_smul_mem_of_mem_span' hcpos.le hccp (hlogT ρ.im) le_rfl
        linarith
      · have hor : χ ^ 2 ≠ 1 ∨ ρ.im ≠ 0 := by
          by_cases h : χ ^ 2 = 1
          · exact Or.inr (hne' h)
          · exact Or.inl h
        have h1 := hZ M χ ρ hχ hL hor
        have := exists_ne_zero_smul_mem_of_mem_span' hcpos.le hccz (hlogT ρ.im) le_rfl
        linarith

end GlobalTheory.ExceptionalPair
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal

noncomputable section
namespace GlobalTheory.SumMaj
open scoped Classical
variable {F : Type} [Field F] [NumberField F] {N : ℕ}

theorem re_add (x y : Ainf F) (w : InfinitePlace F) : re (x + y) w = re x w + re y w := by
  show (InfinitePlace.Completion.extensionEmbedding w (x w + y w)).re = _
  rw [map_add (f := _), Complex.add_re]; rfl

theorem abs_re_algebraMap (hF : IsTotallyReal F) (x : F) (w : InfinitePlace F) :
    |re (algebraMap F (Ainf F) x) w| = w x := by
  unfold re
  have hw : w.IsReal := hF.isReal w
  rw [InfiniteAdeleRing.algebraMap_apply]
  rw [InfinitePlace.Completion.extensionEmbedding_coe]
  rw [← InfinitePlace.embedding_of_isReal_apply hw, Complex.ofReal_re]
  first
  | (rw [← Real.norm_eq_abs]; exact InfinitePlace.norm_embedding_of_isReal hw x)
  | simpa [Real.norm_eq_abs] using InfinitePlace.norm_embedding_of_isReal hw x

theorem sz_nonneg (u : Fin N → AF F) : 0 ≤ sz u :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem sz_sub_le (u y : Fin N → AF F) : sz u - sz y ≤ sz (u + y) := by
  unfold sz
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun l _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun w _ => ?_
  have h : re (inf (u + y) l) w = re (inf u l) w + re (inf y l) w := by
    rw [← re_add]; congr 1
  rw [h]
  have := abs_sub_abs_le_abs_sub (re (inf u l) w) (-(re (inf y l) w))
  simpa [abs_neg, sub_neg_eq_add] using this

theorem continuous_sz : Continuous (sz : (Fin N → AF F) → ℝ) := by
  unfold sz
  refine continuous_finsetSum _ fun l _ => continuous_finsetSum _ fun w _ => ?_
  have h1 : Continuous fun u : Fin N → AF F => inf u l := by
    show Continuous fun u : Fin N → AF F => (u l).1
    exact continuous_fst.comp (continuous_apply l)
  have h2 : Continuous fun x : Ainf F => re x w :=
    Complex.continuous_re.comp ((InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp
      (continuous_apply w))
  exact continuous_abs.comp (h2.comp h1)

theorem continuous_fin : Continuous (fin : (Fin N → AF F) → Fin N → Af F) := by
  refine continuous_pi fun l => ?_
  show Continuous fun u : Fin N → AF F => (u l).2
  exact continuous_snd.comp (continuous_apply l)

theorem fin_add (u y : Fin N → AF F) : fin (u + y) = fin u + fin y := by
  funext l; simp [fin, map_add (f := _)]

theorem inf_rat (ξ : Fin N → F) (l : Fin N) : inf (rat ξ) l = algebraMap F (Ainf F) (ξ l) := by
  simp [inf, rat]

theorem fin_rat (ξ : Fin N → F) (l : Fin N) : fin (rat ξ) l = algebraMap F (Af F) (ξ l) := by
  simp [fin, rat]

theorem norm_le_sz (hF : IsTotallyReal F) (ξ : Fin N → F) :
    ‖(fun l => mixedEmbedding F (ξ l))‖ ≤ sz (rat ξ) := by
  refine (pi_norm_le_iff_of_nonneg (sz_nonneg _)).2 fun l => ?_
  classical
  rw [mixedEmbedding.norm_eq_sup'_normAtPlace]
  refine Finset.sup'_le _ _ fun w _ => ?_
  rw [mixedEmbedding.normAtPlace_apply]
  unfold sz
  calc w (ξ l) = |re (inf (rat ξ) l) w| := by rw [inf_rat, abs_re_algebraMap hF]
    _ ≤ ∑ w', |re (inf (rat ξ) l) w'| :=
        Finset.single_le_sum (f := fun w' => |re (inf (rat ξ) l) w'|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ w)
    _ ≤ _ := Finset.single_le_sum (f := fun l' => ∑ w', |re (inf (rat ξ) l') w'|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ l)

theorem finrank_le_of_discrete {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] : Module.finrank ℤ L ≤ Module.finrank ℝ E := by
  let E' := Submodule.span ℝ (L : Set E)
  let L' : Submodule ℤ E' := ZLattice.comap ℝ L E'.subtype
  haveI : DiscreteTopology L' :=
    ZLattice.comap_discreteTopology _ _ (by fun_prop) Subtype.val_injective
  haveI : IsZLattice ℝ L' :=
    ⟨Submodule.map_injective_of_injective E'.subtype_injective (by simp [E', L'])⟩
  let e : L' ≃ₗ[ℤ] L := Submodule.comapSubtypeEquivOfLe (p := L) (q := E'.restrictScalars ℤ)
    Submodule.subset_span
  rw [← e.finrank_eq, ZLattice.rank ℝ L']
  exact Submodule.finrank_le E'

end GlobalTheory.SumMaj

namespace GlobalTheory.SumMaj
open scoped Classical

theorem summable_majorant : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ), IsTotallyReal F →
    ∀ K : Set (Fin N → Af F), IsCompact K → ∃ k : ℕ, ∀ ω : Set (Fin N → AF F), IsCompact ω →
      ∃ c : (Fin N → F) → ℝ, Summable c ∧ (∀ ξ, 0 ≤ c ξ) ∧
        ∀ ξ, ∀ y ∈ ω, fin (rat ξ + y) ∈ K → 1 ≤ c ξ * (1 + sz (rat ξ + y)) ^ k := by
  intro F _ _ N hF K hK
  refine ⟨Module.finrank ℝ (Fin N → mixedEmbedding.mixedSpace F) + 1, fun ω hω => ?_⟩
  set k := Module.finrank ℝ (Fin N → mixedEmbedding.mixedSpace F) + 1 with hk
  obtain ⟨B, hB⟩ := hω.bddAbove_image (continuous_sz (F := F) (N := N)).continuousOn
  set B0 := max B 0 with hB0
  have hB0n : 0 ≤ B0 := le_max_right _ _
  have hszB : ∀ y ∈ ω, sz y ≤ B0 := fun y hy => (hB ⟨y, hy, rfl⟩).trans (le_max_left _ _)
  set K' : Set (Fin N → Af F) := (fun p : (Fin N → Af F) × (Fin N → Af F) => p.1 - p.2) '' (K ×ˢ (fin '' ω))
    with hK'
  have hK'c : IsCompact K' :=
    (hK.prod (hω.image continuous_fin)).image (continuous_fst.sub continuous_snd)
  obtain ⟨M, hM0, hM⟩ := GlobalTheory.WeilM.exists_nat_mul_integral_of_isCompact F hK'c
  set S : Set (Fin N → F) := {ξ | fin (rat ξ) ∈ K'} with hS
  set c : (Fin N → F) → ℝ := S.indicator fun ξ => (1 + B0) ^ k / (1 + sz (rat ξ)) ^ k with hc
  have hc0 : ∀ ξ, 0 ≤ c ξ := fun ξ =>
    Set.indicator_nonneg (fun ξ _ => div_nonneg (pow_nonneg (by linarith) _)
      (pow_nonneg (by linarith [sz_nonneg (rat ξ)]) _)) ξ
  refine ⟨c, ?_, hc0, fun ξ y hy hξ => ?_⟩
  · haveI := GlobalTheory.WeilM.discreteTopology_denomLattice F (Fin N) hM0
    set L := GlobalTheory.WeilM.denomLattice F (Fin N) M with hL
    have memL : ∀ ξ ∈ S, (fun i => mixedEmbedding F (ξ i)) ∈ L := by
      intro ξ hξ i
      obtain ⟨y, hy⟩ := (GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties F).2.2.2.1 ((M : F) * ξ i)
        fun v => by
          rw [map_mul, map_natCast]
          have := hM _ hξ i v
          rwa [fin_rat] at this
      refine ⟨y, ?_⟩
      have h2 := congrArg (mixedEmbedding F) hy
      rw [← nsmul_eq_mul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ] at h2
      exact h2.symm
    let j : S → L := fun ξ => ⟨_, memL ξ.1 ξ.2⟩
    have hj : Function.Injective j := fun a b h => Subtype.ext (funext fun i =>
      mixedEmbedding_injective F (congrFun (congrArg Subtype.val h) i))
    have hkL : Module.finrank ℤ L < k := Nat.lt_succ_of_le (finrank_le_of_discrete L)
    have hg : Summable fun z : L => ((1 + ‖z‖) ^ k)⁻¹ := by
      refine Summable.of_norm_bounded_eventually (ZLattice.summable_norm_pow_inv L k hkL) ?_
      refine (Set.finite_singleton (0 : L)).subset fun z hz => ?_
      by_contra h0
      apply hz
      show ‖((1 + ‖z‖) ^ k)⁻¹‖ ≤ ‖z‖⁻¹ ^ k
      have hz0 : 0 < ‖z‖ := norm_pos_iff.2 h0
      rw [Real.norm_of_nonneg (inv_nonneg.2 (pow_nonneg (by positivity) _)), inv_pow]
      exact inv_anti₀ (pow_pos hz0 _) (pow_le_pow_left₀ hz0.le (by linarith) _)
    refine ((Subtype.val_injective (p := fun ξ => ξ ∈ S)).summable_iff ?_).1 ?_
    · intro ξ hξ
      have : ξ ∉ S := fun h => hξ ⟨⟨ξ, h⟩, rfl⟩
      exact Set.indicator_of_notMem this _
    · refine Summable.of_nonneg_of_le (fun ξ => hc0 _) (fun ξ => ?_) ((hg.comp_injective hj).mul_left ((1 + B0) ^ k))
      show c ξ.1 ≤ (1 + B0) ^ k * ((1 + ‖j ξ‖) ^ k)⁻¹
      rw [hc, Set.indicator_of_mem ξ.2, div_eq_mul_inv]
      refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (by linarith) _)
      have hn : ‖j ξ‖ ≤ sz (rat ξ.1) := norm_le_sz hF ξ.1
      exact inv_anti₀ (pow_pos (by positivity) _) (pow_le_pow_left₀ (by positivity) (by linarith) _)
  · have hS' : ξ ∈ S := by
      refine ⟨(fin (rat ξ + y), fin y), ⟨hξ, y, hy, rfl⟩, ?_⟩
      simp [fin_add]
    rw [hc, Set.indicator_of_mem hS']
    have hs0 := sz_nonneg (rat ξ)
    have ht0 := sz_nonneg (rat ξ + y)
    have hst := sz_sub_le (rat ξ) y
    have hy0 := hszB y hy
    have key : 1 + sz (rat ξ) ≤ (1 + B0) * (1 + sz (rat ξ + y)) := by nlinarith
    rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos (by linarith) _), one_mul, ← mul_pow]
    exact pow_le_pow_left₀ (by linarith) key _

end GlobalTheory.SumMaj
end
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.rationalVectors_adeles_fundamentalDomain_mass_one : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (ν : Measure (AF F)), IsCov1 ν → (muV N ν).IsAddHaarMeasure ∧ (∀ u : (Fin N → AF F), u ∈ (AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F)))) ↔ ∃ ξ, u = rat ξ) ∧ Function.Injective (rat : (Fin N → F) → (Fin N → AF F)) ∧ (∃ K : Set (Fin N → AF F), IsCompact K ∧ ∀ u, ∃ ξ, u - rat ξ ∈ K) ∧ ∃ D : Set (Fin N → AF F), MeasurableSet D ∧ IsAddFundamentalDomain (AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F)))) D (muV N ν) ∧ muV N ν D = 1 := by
  first | exact @GlobalTheory.SWQ.rat_lattice_fundamentalDomain | exact GlobalTheory.SWQ.rat_lattice_fundamentalDomain | (intros; apply GlobalTheory.SWQ.rat_lattice_fundamentalDomain <;> assumption)
end

section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

theorem _root_.GlobalTheory.T.rowDeg_dominated_of_mem_dualWeylModule : ∀ (k : Type) [Field k] (N : ℕ) (ν : Fin N → ℕ), ∀ f ∈ dualWeyl k N N ν, ∀ m ∈ f.support, (∀ j : ℕ, (∑ a : Fin N with a.val < j, rowDeg m a) ≤ ∑ a : Fin N with a.val < j, ν a) ∧ ∑ a, rowDeg m a = ∑ a, ν a := by
  first | exact @GlobalTheory.Alc.rowDeg_dominated_of_mem_dualWeyl | exact GlobalTheory.Alc.rowDeg_dominated_of_mem_dualWeyl | (intros; apply GlobalTheory.Alc.rowDeg_dominated_of_mem_dualWeyl <;> assumption)
end

section

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

theorem _root_.GlobalTheory.T.level_character_no_blocks_pth_root_of_unity : ∀ (k K : Type) [Field k] [Field K] (s : K →+* ℂ) (p : ℕ), p.Prime → (p : k) = 0 → (∃ ζ : K, IsPrimitiveRoot ζ p) → ∀ (n : ℕ) (ψ : AddChar k ℂ) (χ : ℕ → MulChar k ℂ) (a t skip : ℕ) (M : Matrix (Fin n) (Fin n) k), (∃ r : K, s r = lamJ ψ χ a t 0 skip M) ∧ lamJ ψ χ a t 0 skip M ^ p = 1 := by
  first | exact @GlobalTheory.lamJ_zero_blocks_mem_range_and_pow_eq_one | exact GlobalTheory.lamJ_zero_blocks_mem_range_and_pow_eq_one | (intros; apply GlobalTheory.lamJ_zero_blocks_mem_range_and_pow_eq_one <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct


theorem _root_.GlobalTheory.T.fibreIntegral_pi_prod_eq_prod_fibreIntegral : ∀ (T V : Type) [Fintype T] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ₀ : Measure V) [SigmaFinite μ₀] (q : V → ℝ), Continuous q → ∀ U : Set V, IsOpen U → ∀ fib : ℝ → Measure V, IsFibreFamily μ₀ q id U (volume : Measure ℝ) Set.univ fib → ∀ B : Set (T → ℝ), IsOpen B → ∀ Fib : (T → ℝ) → Measure (T → V), IsFibreFamily (Measure.pi fun _ : T => μ₀) (fun x ρ => q (x ρ)) id Set.univ (volume : Measure (T → ℝ)) B Fib → ∀ b ∈ B, ∀ φ : T → V → ℝ, (∀ ρ, Continuous (φ ρ) ∧ HasCompactSupport (φ ρ) ∧ tsupport (φ ρ) ⊆ U ∧ ∀ y, 0 ≤ φ ρ y) → ∫⁻ x, ∏ ρ, ENNReal.ofReal (φ ρ (x ρ)) ∂(Fib b) = ∏ ρ, ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib (b ρ)) := by
  first | exact @GlobalTheory.FibreProd.lintegral_fibre_prod | exact GlobalTheory.FibreProd.lintegral_fibre_prod | (intros; apply GlobalTheory.FibreProd.lintegral_fibre_prod <;> assumption)
end
