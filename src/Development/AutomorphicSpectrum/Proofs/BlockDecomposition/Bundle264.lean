module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle248
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionalCalculusFirstAssumption
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.HeisenbergTheta.HeisenbergThetaConstant.ThetaC
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle244
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.KerFc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem inner_cls_eq {n : ℕ} [MeasurableSpace (G n)] (μ : Measure (G n)) {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] {a b : Mat n → V} (ha : MemLp (fun y : G n => a y.val) 2 μ)
    (hb : MemLp (fun y : G n => b y.val) 2 μ) :
    ⟪cls μ a, cls μ b⟫_ℂ = ∫ y : G n, ⟪a y.val, b y.val⟫_ℂ ∂μ := by
  have e1 : cls μ a = ha.toLp _ := dif_pos ha
  have e2 : cls μ b = hb.toLp _ := dif_pos hb
  rw [e1, e2, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with y h1 h2
  rw [h1, h2]

theorem integrable_inner_of_memLp {n : ℕ} [MeasurableSpace (G n)] (μ : Measure (G n)) {V : Type}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] {a b : G n → V} (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
    Integrable (fun y => ⟪a y, b y⟫_ℂ) μ := by
  have h := L2.integrable_inner (𝕜 := ℂ) (ha.toLp _) (hb.toLp _)
  refine h.congr ?_
  filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with y h1 h2
  rw [h1, h2]

theorem integrable_adjoint_apply {n : ℕ} [MeasurableSpace (G n)] (μ : Measure (G n)) {V : Type}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V]
    {A : G n → (V →L[ℂ] V)} {φ : G n → V} (hA : ∀ v, MemLp (fun y => A y v) 2 μ) (hφ : MemLp φ 2 μ) :
    Integrable (fun y => ContinuousLinearMap.adjoint (A y) (φ y)) μ := by
  classical
  let b := stdOrthonormalBasis ℂ V
  have key : (fun y => ContinuousLinearMap.adjoint (A y) (φ y)) =
      fun y => ∑ i, ⟪A y (b i), φ y⟫_ℂ • b i := by
    funext y
    rw [← b.sum_repr' (ContinuousLinearMap.adjoint (A y) (φ y))]
    simp only [ContinuousLinearMap.adjoint_inner_right]
  rw [key]
  exact integrable_finsetSum _ fun i _ => (integrable_inner_of_memLp μ (hA (b i)) hφ).smul_const _

theorem actFormula (hLt : LtSob) (hComm : LtComm) : ActFormula := by
  intro n _ _ μ _ E _ Ω T F c hStd h A hRow f hf hCpt f' hSob' hSec' hcls x hx
  have hStd0 := hStd
  obtain ⟨hLg, hUni, hRC, hSG, hAE, hWS, hWC, hCS, hSO, hPW, -⟩ := hStd0
  obtain ⟨-, -, -, -, -, -, hCptSob, -⟩ := hCS
  have hdet : x.det ≠ 0 := hx
  let x₀ : G n := Matrix.GeneralLinearGroup.mkOfDetNeZero x hdet
  have hx₀ : x₀.val = x := rfl
  have hfS : Sob μ f := (hCptSob n μ E.V hLg hRC f hf.1 hCpt).1
  have hmul : ∀ g ∈ GLs n, x * g ∈ GLs n := fun g hg => by
    have hg' : g.det ≠ 0 := hg
    show (x * g).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero hdet hg'
  have hφS : Sob μ (lTr x₀ f) := (hLt n μ E.V hLg hUni hRC x₀ f hfS).1
  have hψS : Sob μ (lTr x₀ f') := (hLt n μ E.V hLg hUni hRC x₀ f' hSob').1
  have hφE : IsSec E (lTr x₀ f) := fun g hg k => by
    show f (x₀.val * (g * k.1)) = E.ρ k⁻¹ (f (x₀.val * g))
    rw [hx₀, ← mul_assoc]
    exact hf.2 _ (hmul g hg) k
  have hψE : IsSec E (lTr x₀ f') := fun g hg k => by
    show f' (x₀.val * (g * k.1)) = E.ρ k⁻¹ (f' (x₀.val * g))
    rw [hx₀, ← mul_assoc]
    exact hSec' _ (hmul g hg) k
  have hclsT : cls μ (lTr x₀ f') = F.Φ h (cls μ (lTr x₀ f)) :=
    hComm n μ E Ω T F c hStd h x₀ f f' hfS hSob' hcls
  have hφL : MemLp (fun y : G n => lTr x₀ f y.val) 2 μ := hφS.2 []
  have hAL : ∀ v, MemLp (fun y : G n => A y.val v) 2 μ := fun v => (hRow v).1.2 []
  have hint : Integrable
      (fun y : G n => ContinuousLinearMap.adjoint (A y.val) (lTr x₀ f y.val)) μ :=
    integrable_adjoint_apply μ (A := fun y : G n => A y.val) hAL hφL
  refine ext_inner_left ℂ fun v => ?_
  have hrow := (hRow v).2.2 (lTr x₀ f) (lTr x₀ f') hφS hφE hψS hψE hclsT
  rw [inner_cls_eq μ (hAL v) hφL] at hrow
  have hval : lTr x₀ f' 1 = f' x := by
    show f' (x₀.val * 1) = f' x
    rw [hx₀, mul_one]
  rw [hval] at hrow
  rw [← hrow]
  show ⟪v, ∫ y : G n, ContinuousLinearMap.adjoint (A y.val) (f (x * y.val)) ∂μ⟫_ℂ = _
  have hint' : Integrable (fun y : G n => ContinuousLinearMap.adjoint (A y.val) (f (x * y.val))) μ := hint
  rw [← integral_inner hint' v]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  show ⟪v, ContinuousLinearMap.adjoint (A y.val) (f (x * y.val))⟫_ℂ = ⟪A y.val v, f (x₀.val * y.val)⟫_ℂ
  rw [hx₀, ContinuousLinearMap.adjoint_inner_right]

end GlobalTheory.CompanionTheory.KerFc
end
end

section

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.KerFc.RowLin

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem sum_sec {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    (E : KMod n) (hLg : LgFacts) (hU : Unimod) (hR : RCalc) (hCl : ClsFacts) (hOps : SobOps)
    {ι : Type} (f₀ : Mat n → E.V) (h₀ : Sob μ f₀) (f : ι → Mat n → E.V) (hS : ∀ i, Sob μ (f i))
    (hI : ∀ i, IsSec E (f i)) (a : ι → ℂ) (s : Finset ι) :
    Sob μ (fun y => ∑ i ∈ s, a i • f i y) ∧ IsSec E (fun y => ∑ i ∈ s, a i • f i y) ∧
      cls μ (fun y => ∑ i ∈ s, a i • f i y) = ∑ i ∈ s, a i • cls μ (f i) := by
  classical
  have hlin := (hCl n μ E.V hU).2.1
  have hadd : ∀ (b : ℂ) (g g' : Mat n → E.V), Sob μ g → Sob μ g' → Sob μ (b • g + g') := fun b g g' hg hg' =>
    ((hOps n μ E.V hLg hU hR g hg).2.2.2.1 b g' hg').1
  have hmem : ∀ g : Mat n → E.V, Sob μ g → MemLp (fun y : G n => g y.val) 2 μ := fun g hg => hg.2 []
  induction s using Finset.induction_on with
  | empty =>
    have hz : (fun _ : Mat n => (0 : E.V)) = (-1 : ℂ) • f₀ + f₀ := by
      funext y; simp
    simp only [Finset.sum_empty]
    refine ⟨hz ▸ hadd _ _ _ h₀ h₀, fun g _ k => by simp, ?_⟩
    rw [hz, hlin _ _ _ (hmem _ h₀) (hmem _ h₀)]
    simp
  | insert i s hi ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih
    have hz : (fun y => ∑ j ∈ insert i s, a j • f j y) = a i • f i + fun y => ∑ j ∈ s, a j • f j y := by
      funext y; simp [Finset.sum_insert hi]
    rw [hz, Finset.sum_insert hi]
    refine ⟨hadd _ _ _ (hS i) ih1, fun g hg k => ?_, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, map_add (f := _), map_smul]
      rw [hI i g hg k]
      exact congrArg (a i • (E.ρ k⁻¹) (f i g) + ·) (ih2 g hg k)
    · rw [hlin _ _ _ (hmem _ (hS i)) (hmem _ ih1), ih3]

end GlobalTheory.CompanionTheory.KerFc.RowLin

namespace GlobalTheory.CompanionTheory.KerFc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem rowMatrix_holds : RowMatrix := by
  intro n _ _ μ _ E _ Ω T F c hstd h hrow
  obtain ⟨hLg, hU, hR, -, -, -, -, hCS, -⟩ := hstd
  obtain ⟨-, -, -, -, hCl, hOps, -⟩ := hCS
  let e := stdOrthonormalBasis ℂ E.V
  choose f hf using fun i => hrow (e i)
  obtain ⟨f₀, hf₀⟩ := hrow 0
  refine ⟨fun y => ∑ i, (innerSL ℂ (e i)).smulRight (f i y), fun v => ?_⟩
  have hA : (fun y => (∑ i, (innerSL ℂ (e i)).smulRight (f i y)) v) =
      fun y => ∑ i ∈ Finset.univ, (⟪e i, v⟫_ℂ) • f i y := by
    funext y
    simp [ContinuousLinearMap.sum_apply]
  obtain ⟨h1, h2, h3⟩ := RowLin.sum_sec μ E hLg hU hR hCl hOps f₀ hf₀.1 f (fun i => (hf i).1)
    (fun i => (hf i).2.1) (fun i => ⟪e i, v⟫_ℂ) Finset.univ
  show Row μ E F h v (fun y => (∑ i, (innerSL ℂ (e i)).smulRight (f i y)) v)
  rw [hA]
  refine ⟨h1, h2, fun φ f' hφ hφs hf' hf's hcl => ?_⟩
  rw [h3, sum_inner, ← (e.sum_inner_mul_inner v (f' 1))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_left, inner_conj_symm, (hf i).2.2 φ f' hφ hφs hf' hf's hcl]

end GlobalTheory.CompanionTheory.KerFc
end
end

section

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.KerFc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem toC0_eq_of_coe (p : C₀(ℝ, ℂ)) (f : ℝ → ℂ) (h : ∀ y, p y = f y) : toC0 f = p := by
  have hf : f = ⇑p := funext fun y => (h y).symm
  subst hf
  have hc : Continuous (⇑p) ∧ Tendsto (⇑p) (cocompact ℝ) (𝓝 0) := ⟨p.continuous, p.zero_at_infty'⟩
  unfold toC0
  rw [dite_eq_left hc]
  ext y
  rfl

theorem exists_resolvent_C0 : ∃ r : C₀(ℝ, ℂ), ∀ y, r y = (((1 + y ^ 2)⁻¹ : ℝ) : ℂ) := by
  have hpos : ∀ y : ℝ, (1 + y ^ 2) ≠ 0 := fun y => by positivity
  have hcont : Continuous (fun y : ℝ => (((1 + y ^ 2)⁻¹ : ℝ) : ℂ)) := by
    refine Complex.continuous_ofReal.comp ?_
    exact (by fun_prop : Continuous fun y : ℝ => 1 + y ^ 2).inv₀ hpos
  have hat : Tendsto (fun y : ℝ => 1 + y ^ 2) (cocompact ℝ) atTop := by
    have h1 : Tendsto (fun y : ℝ => ‖y‖ ^ 2) (cocompact ℝ) atTop :=
      (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp tendsto_norm_cocompact_atTop
    have h2 : Tendsto (fun y : ℝ => 1 + ‖y‖ ^ 2) (cocompact ℝ) atTop :=
      tendsto_atTop_add_const_left _ 1 h1
    simpa using h2
  have htend : Tendsto (fun y : ℝ => (((1 + y ^ 2)⁻¹ : ℝ) : ℂ)) (cocompact ℝ) (𝓝 0) := by
    have h3 : Tendsto (fun y : ℝ => (1 + y ^ 2)⁻¹) (cocompact ℝ) (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hat
    have h4 : Tendsto (fun y : ℝ => (((1 + y ^ 2)⁻¹ : ℝ) : ℂ)) (cocompact ℝ) (𝓝 ((0 : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto 0).comp h3
    rwa [Complex.ofReal_zero] at h4
  exact ⟨⟨⟨_, hcont⟩, htend⟩, fun y => rfl⟩

theorem phiRes_holds : PhiRes := by
  intro n _ _ μ _ E _ Ω T F c hS g T₀ hb N _
  obtain ⟨-, -, -, -, -, -, -, -, -, hPW, -⟩ := hS
  have h0 := (hPW c g T₀ hb).1 0
  simp only [pow_zero, one_mul] at h0
  obtain ⟨r, hr⟩ := exists_resolvent_C0
  have hT : F.Φ r = T := F.res r hr
  let q : C₀(ℝ, ℂ) := ⟨⟨hg c g, h0.1⟩, h0.2⟩
  have hq : ∀ y, q y = hg c g y := fun y => rfl
  have key : ∀ M : ℕ, ∃ p : C₀(ℝ, ℂ),
      (∀ y, p y = ((((1 + y ^ 2) ^ M)⁻¹ : ℝ) : ℂ) * hg c g y) ∧ F.Φ p = F.Φ q * T ^ M := by
    intro M
    induction M with
    | zero => exact ⟨q, fun y => by simp [hq], by simp⟩
    | succ M ih =>
      obtain ⟨p, hp, hΦ⟩ := ih
      refine ⟨p * r, fun y => ?_, ?_⟩
      · have : (p * r) y = p y * r y := rfl
        rw [this, hp, hr, pow_succ (1 + y ^ 2) M, mul_inv]
        push_cast
        ring
      · rw [F.map_mul, hΦ, hT, pow_succ, mul_assoc]
  obtain ⟨p, hp, hΦ⟩ := key N
  rw [toC0_eq_of_coe p _ hp, toC0_eq_of_coe q _ hq, hΦ]

end GlobalTheory.CompanionTheory.KerFc
end
end

section

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.KerFc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def lTrL {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type)
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] (x : G n) : Lp V 2 μ →L[ℂ] Lp V 2 μ :=
  (Lp.compMeasurePreservingₗᵢ ℂ (fun y : G n => x * y) (measurePreserving_mul_left μ x)).toContinuousLinearMap

theorem memLp_lTr {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] {V : Type}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] (x : G n) {f : Mat n → V}
    (hf : MemLp (fun y : G n => f y.val) 2 μ) : MemLp (fun y : G n => lTr x f y.val) 2 μ :=
  hf.comp_measurePreserving (measurePreserving_mul_left μ x)

theorem lTrL_cls {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] {V : Type}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] (x : G n) {f : Mat n → V}
    (hf : MemLp (fun y : G n => f y.val) 2 μ) : lTrL μ V x (cls μ f) = cls μ (lTr x f) := by
  unfold cls
  rw [dite_eq_left hf, dite_eq_left (memLp_lTr μ x hf)]
  exact Lp.toLp_compMeasurePreserving hf (measurePreserving_mul_left μ x)

theorem ltComm_of_ltSob : LtSob → LtComm := by
  intro hL n _ _ μ _ E _ Ω T F c hS h x f f' hf hf' hff'
  obtain ⟨hLg, hU, hR, -, -, -, -, hCS, -, -, hM, -, -, -, hO, -⟩ := hS
  obtain ⟨-, -, -, -, hCl, hOps, -⟩ := hCS
  have hcomm : lTrL μ E.V x * F.Φ h = F.Φ h * lTrL μ E.V x := by
    refine F.comm _ (fun m => ?_) h
    obtain ⟨f₀, hf₀, hc⟩ := hM m.1 m.2
    have hL₀ := hL n μ E.V hLg hU hR x f₀ hf₀
    have hmem : cls μ (lTr x f₀) ∈ Msob μ E.V := Submodule.subset_span ⟨_, hL₀.1, rfl⟩
    have hm₀ : cls μ f₀ ∈ Msob μ E.V := hc ▸ m.2
    have hm : m = ⟨cls μ f₀, hm₀⟩ := Subtype.ext hc.symm
    have hO₀ : Sob μ (Om f₀) := (hOps n μ E.V hLg hU hR f₀ hf₀).1
    have hf₀m : MemLp (fun y : G n => f₀ y.val) 2 μ := hf₀.2 []
    have hO₀m : MemLp (fun y : G n => Om f₀ y.val) 2 μ := hO₀.2 []
    refine ⟨⟨_, hmem⟩, ?_, ?_⟩
    · change cls μ (lTr x f₀) = lTrL μ E.V x m.1
      rw [← hc, lTrL_cls μ x hf₀m]
    · rw [hO _ hmem hL₀.1, hm, hO _ hm₀ hf₀, lTrL_cls μ x hO₀m]
      exact (hCl n μ E.V hU).2.2.1 _ _ hL₀.2
  have hfm : MemLp (fun y : G n => f y.val) 2 μ := hf.2 []
  have hfm' : MemLp (fun y : G n => f' y.val) 2 μ := hf'.2 []
  rw [← lTrL_cls μ x hfm', hff', ← lTrL_cls μ x hfm]
  exact DFunLike.congr_fun hcomm (cls μ f)

end GlobalTheory.CompanionTheory.KerFc
end
end

section

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc
open PositivityTheory.RgTw (Mat G)
open GlobalTheory.CompanionTheory.WaveFc.Asm

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.KerFc

variable {n : ℕ}

section Main

variable [MeasurableSpace (G n)] [BorelSpace (G n)] {μ : Measure (G n)} [μ.IsHaarMeasure]

theorem coreRep (E : KMod n) [CompleteSpace E.V] {Ω : Msob μ E.V →ₗ[ℂ] Msob μ E.V} {T : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ}
    (hL : LgFacts) (hU : Unimod) (hR : RCalc) (hSG : SobG)
    (hAC : AbsCut) (hFc : Fcurve) (hW : WvAlg) (hC : ClsFacts) (hO : SobOps) (hCp : CptSob) (hP : PresSob)
    (hCJ : CurveJoint)
    (F : FCalc (Lp E.V 2 μ) (Msob μ E.V) Ω T) (hrep : ∀ x ∈ Msob μ E.V, ∃ f, Sob μ f ∧ cls μ f = x)
    (hΩ : ∀ (f : Mat n → E.V) (hf : cls μ f ∈ Msob μ E.V), Sob μ f → (Ω ⟨cls μ f, hf⟩ : Lp E.V 2 μ) = cls μ (Om f))
    (hT : ∀ x : Msob μ E.V, T ((x : Lp E.V 2 μ) + (Ω (Ω x) : Lp E.V 2 μ)) = x) (c : ℝ)
    (hc : ∀ f : Mat n → E.V, Sob μ f → IsSec E f → (⟪cls μ (Om f), cls μ f⟫_ℂ).re ≤ c * ‖cls μ f‖ ^ 2)
    {f : Mat n → E.V} (hf : f ∈ CE E) (hcf : Cpt f) :
    ∃ (N : ℕ) (b : Lp E.V 2 μ) (U : ℝ → Mat n → E.V), 1 ≤ N ∧ (T ^ N) b = cls μ f ∧ IsWave E U ∧
      (∀ x ∈ GLs n, U 0 x = f x) ∧ ∀ t, Sob μ (U t) ∧ cls μ (U t) = F.Φ (toC0 (wv c N 0 t)) b := by
  have hbp := fun N => Bn_props μ hL hR hCp E hf hcf N
  have hbS : ∀ N, Sob μ (Bn f N) := fun N => (hCp n μ E.V hL hR _ (hbp N).1.1 (hbp N).2).1
  have hbE : ∀ N, IsSec E (Bn f N) := fun N => (hbp N).1.2
  have hC0 : ∀ N j t, j + 2 ≤ 4 * N → (Continuous (wv c N j t) ∧ Tendsto (wv c N j t) (cocompact ℝ) (𝓝 0)) :=
    fun N j t hj => (hFc c N j hj t).1
  have hstep : ∀ N j t, j + 2 ≤ 4 * N →
      F.Φ (toC0 (wv c (N + 1) j t)) (cls μ (Bn f (N + 1))) = F.Φ (toC0 (wv c N j t)) (cls μ (Bn f N)) := by
    intro N j t hj
    rw [wv_step hW F (hC0 N j t hj) (hC0 (N + 1) j t (by omega)), ContinuousLinearMap.mul_apply]
    exact congrArg _ (T_B hC hO hL hU hR hΩ hT (hbS N))
  have hpres := fun g (N : ℕ) => pres hC hO hL hU hR hSG hP F hrep hΩ g (hbS N)
  have hex : ∀ (j : ℕ) (t : ℝ), ∃ u, Sob μ u ∧ IsSec E u ∧
      cls μ u = F.Φ (toC0 (wv c (j + 2) j t)) (cls μ (Bn f (j + 2))) ∧
      ∀ w, cls μ (Rw w u) = F.Φ (toC0 (wv c (j + 2) j t)) (cls μ (Rw w (Bn f (j + 2)))) := by
    intro j t
    obtain ⟨u, h1, h2, h3⟩ := hpres (toC0 (wv c (j + 2) j t)) (j + 2)
    exact ⟨u, h1, sec_pres E hC hO hL hU hR F hrep hΩ _ (hbS _) (hbE _) h1 h2, h2, h3⟩
  choose U hUS hUE hUc hUw using hex
  have hd : ∀ j w t, HasDerivAt (fun s => cls μ (Rw w (U j s))) (cls μ (Rw w (U (j + 1) t))) t := by
    intro j w t
    have e : (fun s => cls μ (Rw w (U j s))) =
        fun s => F.Φ (toC0 (wv c (j + 2) j s)) (cls μ (Rw w (Bn f (j + 2)))) := funext fun s => hUw j s w
    rw [e]
    have hd := curve_deriv hFc F c (N := j + 2) (j := j) (by omega) t (cls μ (Rw w (Bn f (j + 2))))
    obtain ⟨f'', hf'', hc'', hw''⟩ := hpres (toC0 (wv c (j + 2) (j + 1) t)) (j + 2)
    have e2 : cls μ (Rw w (U (j + 1) t)) = F.Φ (toC0 (wv c (j + 2) (j + 1) t)) (cls μ (Rw w (Bn f (j + 2)))) := by
      rw [← hw'' w]
      refine cls_congr hC hU (Rw_congr w (cls_eq_of_sob hC hU (hUS (j + 1) t) hf'' ?_))
      rw [hUc, hc'']
      exact hstep (j + 2) (j + 1) t (by omega)
    rw [e2]
    exact hd
  obtain ⟨hjoint, hder⟩ := hCJ n μ E.V U hL hR hSG hUS hd
  have hT2 : (T ^ 2) (cls μ (Bn f 2)) = cls μ f := by
    rw [pow_two, ContinuousLinearMap.mul_apply]
    have a1 : T (cls μ (Bn f 2)) = cls μ (Bn f 1) := T_B hC hO hL hU hR hΩ hT (hbS 1)
    have a2 : T (cls μ (Bn f 1)) = cls μ (Bn f 0) := T_B hC hO hL hU hR hΩ hT (hbS 0)
    rw [a1, a2]
    rfl
  refine ⟨2, cls μ (Bn f 2), U 0, by norm_num, hT2, ⟨hjoint, fun t => ⟨(hUS 0 t).1, hUE 0 t⟩, ?_, ?_⟩, ?_,
    fun t => ⟨hUS 0 t, hUc 0 t⟩⟩
  · intro t g hg
    have d1 : deriv (fun s => U 0 s g) = fun s => U 1 s g := funext fun s => (hder 0 s g hg).deriv
    have d2 : iteratedDeriv 2 (fun s => U 0 s g) t = U 2 t g := by
      rw [iteratedDeriv_succ, iteratedDeriv_one, d1]
      exact (hder 1 t g hg).deriv
    rw [d2]
    have hOmS := (hO n μ E.V hL hU hR _ (hUS 0 t)).1
    have h0 : cls μ (U 0 t) = F.Φ (toC0 (wv c 4 0 t)) (cls μ (Bn f 4)) := by
      rw [hUc, hstep 3 0 t (by omega), hstep 2 0 t (by omega)]
    have hom := F.omega (toC0 (wv c 4 0 t)) (toC0 (wv c 4 2 t))
      (fun y => by
        rw [coe_toC0 (hC0 4 0 t (by omega)), coe_toC0 (hC0 4 2 t (by omega))]
        exact (hW c 4 t y).1)
      (cls μ (Bn f 4)) ⟨cls μ (U 0 t), cls_mem μ (hUS 0 t)⟩ h0
    rw [hΩ _ _ (hUS 0 t)] at hom
    exact cls_eq_of_sob hC hU (hUS 2 t) hOmS ((hUc 2 t).trans hom.symm) g hg
  · intro g hg
    rw [(hder 0 0 g hg).deriv]
    have hz : toC0 (wv c 3 1 0) = 0 := by
      ext y
      rw [coe_toC0 (hC0 3 1 0 (by omega))]
      exact (hW c 3 0 y).2.1
    have h1 : cls μ (U 1 0) = cls μ (0 : Mat n → E.V) := by
      rw [hUc, cls_zero]
      show F.Φ (toC0 (wv c 3 1 0)) _ = 0
      rw [hz, map_zero]
      rfl
    exact (hC n μ E.V hU).1 _ 0 (sob_cont (hUS 1 0)) continuousOn_const (sob_memLp (hUS 1 0)) MemLp.zero h1 g hg
  · have hcut : F.Φ (toC0 rf * toC0 rf - toC0 (wv c 2 0 0)) (cls μ (Bn f 2)) = 0 := by
      refine hAC (Lp E.V 2 μ) (Msob μ E.V) Ω T F c _ (fun g => ?_) _ (fun y hy => ?_)
      · obtain ⟨u, h1, h2, -⟩ := hpres g 2
        refine ⟨⟨cls μ u, cls_mem μ h1⟩, h2, ?_⟩
        rw [hΩ _ _ h1]
        exact hc u h1 (sec_pres E hC hO hL hU hR F hrep hΩ _ (hbS _) (hbE _) h1 h2)
      · have e1 := (hW c 2 0 y).2.2.1
        rw [cut_eq_one hy] at e1
        have e2 : (toC0 rf * toC0 rf - toC0 (wv c 2 0 0)) y = rf y * rf y - wv c 2 0 0 y := by
          rw [ZeroAtInftyContinuousMap.sub_apply, ZeroAtInftyContinuousMap.mul_apply, coe_toC0 resolvent_function_vanishes_at_infinity,
            coe_toC0 (hC0 2 0 0 (by omega))]
        rw [e2, e1, rf, ← Complex.ofReal_mul, sub_eq_zero]
        congr 1
        rw [one_mul, pow_two (1 + y ^ 2), mul_inv]
    have hr : F.Φ (toC0 rf * toC0 rf) (cls μ (Bn f 2)) = cls μ f := by
      rw [F.map_mul, F.res (toC0 rf) (fun y => by rw [coe_toC0 resolvent_function_vanishes_at_infinity]; rfl), ContinuousLinearMap.mul_apply]
      have a1 : T (cls μ (Bn f 2)) = cls μ (Bn f 1) := T_B hC hO hL hU hR hΩ hT (hbS 1)
      have a2 : T (cls μ (Bn f 1)) = cls μ (Bn f 0) := T_B hC hO hL hU hR hΩ hT (hbS 0)
      rw [a1, a2]
      rfl
    have hw : F.Φ (toC0 (wv c 2 0 0)) (cls μ (Bn f 2)) = cls μ f := by
      rw [map_sub, ContinuousLinearMap.sub_apply, hr, sub_eq_zero] at hcut
      exact hcut.symm
    exact cls_eq_of_sob hC hU (hUS 0 0) (hbS 0) ((hUc 0 0).trans hw)

end Main

theorem waveRep : WaveRep := by
  intro n _ _ μ _ E _ Ω T F c hStd f hf hcf
  obtain ⟨hL, hU, hR, hSG, -, -, -, hCS, -, -, hrep, -, -, hT, hΩ, hc⟩ := hStd
  obtain ⟨-, hAC, hFc, hW, hC, hO, hCp, -, hP, -, hCJ, -, -, -, -⟩ := hCS
  exact coreRep E hL hU hR hSG hAC hFc hW hC hO hCp hP hCJ F hrep hΩ hT c hc hf hcf

end GlobalTheory.CompanionTheory.KerFc
end
end

section

open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.He2M1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix IdeleGroup PositivityTheory.RgEis


theorem _root_.GlobalTheory.T.linearChange_mem_schwartzBruhatPi : ∀ {k : Type} [Field k] [NumberField k], ∀ {ι : Type} [Fintype ι] [DecidableEq ι], ∀ {F : (ι → 𝔸[k]) → ℂ} (hF : F ∈ schwartzBruhatPi (K := k) (ι := ι)) (A : GL ι 𝔸[k]), ltr A F ∈ schwartzBruhatPi (K := k) (ι := ι) := by
  first | exact @GlobalTheory.CompanionTheory.LinearChangeSchwartzBruhat.ltr_mem | exact GlobalTheory.CompanionTheory.LinearChangeSchwartzBruhat.ltr_mem | (intros; apply GlobalTheory.CompanionTheory.LinearChangeSchwartzBruhat.ltr_mem <;> assumption)
end
