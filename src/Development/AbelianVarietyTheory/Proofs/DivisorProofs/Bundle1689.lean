module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicDelChernFormOfGramMatrixEqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1646
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1599
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.UniformSpace.Uniformizable
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.IntegralFderivApplyEqZero
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option autoImplicit false

open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

namespace GlobalTheory.CxForm.GlobLin

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

theorem loc_add (α β : A.Fld) (i : A.ι) : A.loc (α + β) i = fun v => A.loc α i v + A.loc β i v := by
  funext v
  unfold HolAtlas.loc
  split_ifs
  exacts [rfl, (add_zero _).symm]

theorem loc_smul (c : ℂ) (α : A.Fld) (i : A.ι) : A.loc (c • α) i = fun v => c • A.loc α i v := by
  funext v
  unfold HolAtlas.loc
  split_ifs
  exacts [rfl, (smul_zero _).symm]

theorem target_mem_nhds (x : A.Pt) : (A.e x.1.1).target ∈ 𝓝 x.crd :=
  (A.e x.1.1).open_target.mem_nhds (x.ch.map_source x.2)

theorem differentiableAt_coef {α : A.Fld} (h : A.IsForm α) (x : A.Pt) (S : Finset (Fin (n + n))) :
    DifferentiableAt ℝ (fun v => (bas n).repr (A.loc α x.1.1 v) S) x.crd :=
  ((h.smooth x.1.1 S).contDiffAt (target_mem_nhds A x)).differentiableAt (by simp)

theorem loc_one_eventuallyEq (x : A.Pt) : A.loc 1 x.1.1 =ᶠ[𝓝 x.crd] fun _ => 1 :=
  Filter.eventually_of_mem (target_mem_nhds A x) fun v hv => by
    rw [HolAtlas.loc, dite_eq_left hv]
    rfl

end GlobalTheory.CxForm.GlobLin


open GlobalTheory.CxForm.GlobLin in
theorem GlobalTheory.CxForm.HolAtlas.del_dbar_linear : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n),
    (A.del 1 = 0 ∧ A.dbar 1 = 0) ∧
    ∀ (c : ℂ) (α β : A.Fld), A.IsForm α → A.IsForm β →
      A.del (α + β) = A.del α + A.del β ∧ A.dbar (α + β) = A.dbar α + A.dbar β ∧
      A.del (c • α) = c • A.del α ∧ A.dbar (c • α) = c • A.dbar α := by
  intro M _ n A
  refine ⟨⟨funext fun x => ?_, funext fun x => ?_⟩, fun c α β hα hβ =>
    ⟨funext fun x => ?_, funext fun x => ?_, funext fun x => ?_, funext fun x => ?_⟩⟩
  all_goals obtain ⟨hadd, hsmul, -, hgerm, hconst⟩ := GlobalTheory.T.delOperatorAt_dbarOperatorAt_linear_local n x.crd
  · exact (hgerm _ _ (loc_one_eventuallyEq A x)).1.trans (hconst 1).1
  · exact (hgerm _ _ (loc_one_eventuallyEq A x)).2.trans (hconst 1).2
  · rw [HolAtlas.del, loc_add]
    exact (hadd _ _ (differentiableAt_coef A hα x) (differentiableAt_coef A hβ x)).1
  · rw [HolAtlas.dbar, loc_add]
    exact (hadd _ _ (differentiableAt_coef A hα x) (differentiableAt_coef A hβ x)).2
  · rw [HolAtlas.del, loc_smul]
    exact (hsmul _ c (differentiableAt_coef A hα x)).1
  · rw [HolAtlas.dbar, loc_smul]
    exact (hsmul _ c (differentiableAt_coef A hα x)).2
end

section

open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

theorem _root_.GlobalTheory.T.delOperatorAt_dbarOperatorAt_leibniz_of_commute : ∀ (n : ℕ) (F G : V n → Alt n) (v : V n) (F' : Alt n),
    (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v) →
    (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (G x) S) v) →
    ((∀ a, dz a * F v = F' * dz a) → delAt (fun x => F x * G x) v = delAt F v * G v + F' * delAt G v) ∧
    ((∀ a, dzb a * F v = F' * dzb a) → dbarAt (fun x => F x * G x) v = dbarAt F v * G v + F' * dbarAt G v) := by
  first | exact @GlobalTheory.CxForm.FormMul.leibniz_of_comm | exact GlobalTheory.CxForm.FormMul.leibniz_of_comm | (intros; apply GlobalTheory.CxForm.FormMul.leibniz_of_comm <;> assumption)
end

section

open Set Matrix MeasureTheory Filter Topology
open GlobalTheory.HermFrame
open scoped ComplexOrder ContDiff ComplexConjugate

theorem _root_.GlobalTheory.T.differentiableAt_repr_pullback_holomorphic_fderiv : ∀ {n : ℕ} {φ : ReciprocityTheory.L2DbarEstimates.V n → ReciprocityTheory.L2DbarEstimates.V n} {v : ReciprocityTheory.L2DbarEstimates.V n}, ContDiffAt ℂ 2 φ v → ∀ (γ : GlobalTheory.CxForm.Alt n) (S : Finset (Fin (n + n))), DifferentiableAt ℝ (fun w => (GlobalTheory.CxForm.bas n).repr (GlobalTheory.CxForm.pull (fderiv ℂ φ w) γ) S) v := by
  first | exact @GlobalTheory.CxForm.differentiableAt_repr_pull_fderiv | exact GlobalTheory.CxForm.differentiableAt_repr_pull_fderiv | (intros; apply GlobalTheory.CxForm.differentiableAt_repr_pull_fderiv <;> assumption)
end

section

open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

namespace GlobalTheory.CxForm.HolAtlas

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

theorem loc_one {i : A.ι} {v : V n} (hv : v ∈ (A.e i).target) : A.loc 1 i v = 1 := by
  rw [HolAtlas.loc, dite_eq_left hv]; rfl

theorem loc_add (α β : A.Fld) (i : A.ι) (v : V n) : A.loc (α + β) i v = A.loc α i v + A.loc β i v := by
  by_cases hv : v ∈ (A.e i).target
  · rw [HolAtlas.loc, HolAtlas.loc, HolAtlas.loc, dite_eq_left hv, dite_eq_left hv, dite_eq_left hv]; rfl
  · rw [HolAtlas.loc, HolAtlas.loc, HolAtlas.loc, dite_eq_right hv, dite_eq_right hv, dite_eq_right hv, add_zero]

theorem loc_mul (α β : A.Fld) (i : A.ι) (v : V n) : A.loc (α * β) i v = A.loc α i v * A.loc β i v := by
  by_cases hv : v ∈ (A.e i).target
  · rw [HolAtlas.loc, HolAtlas.loc, HolAtlas.loc, dite_eq_left hv, dite_eq_left hv, dite_eq_left hv]; rfl
  · rw [HolAtlas.loc, HolAtlas.loc, HolAtlas.loc, dite_eq_right hv, dite_eq_right hv, dite_eq_right hv, mul_zero]

theorem loc_smul (c : ℂ) (α : A.Fld) (i : A.ι) (v : V n) : A.loc (c • α) i v = c • A.loc α i v := by
  by_cases hv : v ∈ (A.e i).target
  · rw [HolAtlas.loc, HolAtlas.loc, dite_eq_left hv, dite_eq_left hv]; rfl
  · rw [HolAtlas.loc, HolAtlas.loc, dite_eq_right hv, dite_eq_right hv, smul_zero]

theorem isForm_algebra : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n), A.IsForm 1 ∧
    ∀ (c : ℂ) (α β : A.Fld), A.IsForm α → A.IsForm β → A.IsForm (α + β) ∧ A.IsForm (α * β) ∧ A.IsForm (c • α) := by
  intro M _ n A
  refine ⟨⟨fun i S => ?_, fun x x' _ => ?_⟩, fun c α β hα hβ => ⟨⟨fun i S => ?_, fun x x' h => ?_⟩,
    ⟨fun i S => ?_, fun x x' h => ?_⟩, ⟨fun i S => ?_, fun x x' h => ?_⟩⟩⟩
  · exact (contDiffOn_const (c := (bas n).repr (1 : Alt n) S)).congr fun v hv => by
      rw [loc_one A hv]
  · exact (map_one _).symm
  · exact ((hα.smooth i S).add (hβ.smooth i S)).congr fun v _ => by
      rw [loc_add, map_add (f := _), Finsupp.add_apply]
  · change α x + β x = pull _ (α x' + β x')
    rw [map_add (f := _), ← hα.compat x x' h, ← hβ.compat x x' h]
  · exact ((GlobalTheory.T.contDiffOn_coefficients_complexForm_mul n n (A.loc α i) (A.loc β i)).1 _ (hα.smooth i) (hβ.smooth i) S).congr fun v _ => by
      rw [loc_mul]
  · change α x * β x = pull _ (α x' * β x')
    rw [map_mul, ← hα.compat x x' h, ← hβ.compat x x' h]
  · exact ((hα.smooth i S).const_smul c).congr fun v _ => by
      rw [loc_smul, map_smul, Finsupp.smul_apply, smul_eq_mul]
  · change c • α x = pull _ (c • α x')
    rw [map_smul, ← hα.compat x x' h]

end GlobalTheory.CxForm.HolAtlas
end

section

set_option autoImplicit false

open Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.CxForm

namespace GlobalTheory.CxForm

theorem dbarAt_local_calculus : ∀ (n : ℕ) (v : V n),
    (∀ α β : V n → Alt n, α =ᶠ[𝓝 v] β → dbarAt α v = dbarAt β v) ∧
    (∀ (J : Type) (s : Finset J) (α : J → V n → Alt n),
      (∀ j ∈ s, ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (α j x) S) v) →
      dbarAt (fun x => ∑ j ∈ s, α j x) v = ∑ j ∈ s, dbarAt (α j) v) ∧
    (∀ (c : ℂ) (α : V n → Alt n), (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (α x) S) v) →
      dbarAt (fun x => c • α x) v = c • dbarAt α v) ∧
    (∀ γ : Alt n, dbarAt (fun _ => γ) v = 0) ∧
    (∀ (w : V n → Ev n) (β : V n → Alt n),
      (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr ((w x : Alt n)) S) v) →
      (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (β x) S) v) →
      dbarAt (fun x => (w x : Alt n) * β x) v =
        dbarAt (fun x => (w x : Alt n)) v * β v + (w v : Alt n) * dbarAt β v) := by
  intro n v
  obtain ⟨-, hsmul, hsum, hgerm, hconst⟩ := GlobalTheory.CxForm.delAt_dbarAt_linear_local n v
  exact ⟨fun α β h => (hgerm α β h).2, fun J s α h => (hsum J s α h).2, fun c α h => (hsmul α c h).2,
    fun γ => (hconst γ).2, fun w β hw hβ =>
      (FormMul.leibniz_of_comm n (fun x => (w x : Alt n)) β v (w v : Alt n) hw hβ).2
        fun a => Subalgebra.mem_center_iff.1 (w v).2 (dzb a)⟩

end GlobalTheory.CxForm
end

section

open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

namespace GlobalTheory.CxForm

theorem pullback_eq_chart : ∀ (M M' : Type) [TopologicalSpace M] [TopologicalSpace M'] (n n' : ℕ) (A : HolAtlas M n) (A' : HolAtlas M' n')
    (f : M' → M) (α : A.Fld), A.IsHolo A' f → A.IsForm α →
    ∀ (x : A'.Pt) (i : A.ι) (h : f x.pt ∈ (A.e i).source),
      A.pullback A' f α x = pull (fderiv ℂ (A.e i ∘ f ∘ x.ch.symm) x.crd) (α ⟨(i, f x.pt), h⟩) := by
  intro M M' _ _ n n' A A' f α hf hα x i h
  have key : ∀ (j : A.ι) (hj : f x.pt ∈ (A.e j).source),
      pull (fderiv ℂ (A.e j ∘ f ∘ x.ch.symm) x.crd) (α ⟨(j, f x.pt), hj⟩) =
        pull (fderiv ℂ (A.e i ∘ f ∘ x.ch.symm) x.crd) (α ⟨(i, f x.pt), h⟩) := by
    intro j hj
    have hc := hα.compat ⟨(j, f x.pt), hj⟩ ⟨(i, f x.pt), h⟩ rfl
    rw [hc, ← GlobalTheory.T.pullbackComplexFormsLinearMap_comp]
    have hx : x.ch.symm x.crd = x.pt := x.ch.left_inv x.2
    have hxt : x.crd ∈ x.ch.target := x.ch.map_source x.2
    have hopen : IsOpen (x.ch.target ∩ x.ch.symm ⁻¹' (f ⁻¹' (A.e j).source)) :=
      x.ch.isOpen_inter_preimage_symm ((A.e j).open_source.preimage hf.1)
    have hmem : x.crd ∈ x.ch.target ∩ x.ch.symm ⁻¹' (f ⁻¹' (A.e j).source) := by
      refine ⟨hxt, ?_⟩
      simp only [Set.mem_preimage, hx]
      exact hj
    have hd1 : DifferentiableAt ℂ (A.e j ∘ f ∘ x.ch.symm) x.crd :=
      (hf.2 x.1.1 j).differentiableAt (hopen.mem_nhds hmem)
    have hopen2 : IsOpen ((A.e j).target ∩ (A.e j).symm ⁻¹' (A.e i).source) :=
      (A.e j).isOpen_inter_preimage_symm (A.e i).open_source
    have hmem2 : A.e j (f x.pt) ∈ (A.e j).target ∩ (A.e j).symm ⁻¹' (A.e i).source := by
      refine ⟨(A.e j).map_source hj, ?_⟩
      simp only [Set.mem_preimage, (A.e j).left_inv hj]
      exact h
    have hd2 : DifferentiableAt ℂ (A.e i ∘ (A.e j).symm) (A.e j (f x.pt)) :=
      (A.holo j i).differentiableAt (hopen2.mem_nhds hmem2)
    have hpt : (A.e j ∘ f ∘ x.ch.symm) x.crd = A.e j (f x.pt) := by
      simp only [Function.comp, hx]
    have hcomp := fderiv_comp x.crd (hpt ▸ hd2) hd1
    rw [hpt] at hcomp
    have hev : (A.e i ∘ (A.e j).symm) ∘ (A.e j ∘ f ∘ x.ch.symm) =ᶠ[𝓝 x.crd] A.e i ∘ f ∘ x.ch.symm := by
      filter_upwards [hopen.mem_nhds hmem] with v hv
      have hv' : f (x.ch.symm v) ∈ (A.e j).source := hv.2
      simp only [Function.comp, (A.e j).left_inv hv']
    rw [← hev.fderiv_eq, hcomp]
  exact key _ (A.cover (f x.pt)).choose_spec

end GlobalTheory.CxForm
end

section

open Set MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)

theorem _root_.GlobalTheory.T.integral_eq_euclidean_integral_of_support_in_chart : ∀ {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (α : A.Fld) (i : A.ι) (K : Set M), A.IsForm α → IsCompact K → K ⊆ (A.e i).source → (∀ x : A.Pt, x.pt ∉ K → α x = 0) → A.integral α = ∫ v, (GlobalTheory.CxForm.dens (A.loc α i v)).re := by
  exact @GlobalTheory.CxForm.HolAtlas.integral_eq_integral_chart_of_support
end

section

set_option autoImplicit false

noncomputable section

open Set Filter Topology Matrix MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open scoped ContDiff ComplexOrder

namespace GlobalTheory.CxForm.LocStokes

open GlobalTheory.CxForm

variable {n : ℕ}

theorem dens_zero : dens (0 : Alt n) = 0 := by simp [dens]

theorem delAt_eq_zero_of_eventually {F : V n → Alt n} {v : V n} (h : F =ᶠ[𝓝 v] fun _ => 0) : delAt F v = 0 := by
  have hS : ∀ S, GlobalTheory.del (fun x => (bas n).repr (F x) S) v = 0 := fun S => by
    have e : (fun x => (bas n).repr (F x) S) =ᶠ[𝓝 v] fun _ => 0 := h.mono fun x hx => by simp [hx]
    rw [GlobalTheory.del_congr e]
    exact GlobalTheory.del_const _ _
  simp [delAt, coefwise, hS]

theorem del_integral {f : V n → ℂ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (u : V n) :
    Integrable (fun v => GlobalTheory.del f v u) ∧ ∫ v, GlobalTheory.del f v u = 0 := by
  have hint : ∀ w : V n, Integrable (fun y => fderiv ℝ f y w) := fun w =>
    ((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hc.fderiv_apply (𝕜 := ℝ) w)
  have hD : Integrable (fun v => GlobalTheory.del f v u) := by
    simp only [GlobalTheory.del_apply, smul_eq_mul]
    exact ((hint _).sub ((hint _).const_mul _)).const_mul _
  refine ⟨hD, ?_⟩
  simp only [GlobalTheory.del_apply, smul_eq_mul]
  rw [integral_const_mul, integral_sub (hint _) ((hint _).const_mul _), integral_const_mul,
    ReciprocityTheory.L2DbarEstimates.integral_fderiv_apply_eq_zero n f hf hc, ReciprocityTheory.L2DbarEstimates.integral_fderiv_apply_eq_zero n f hf hc]
  simp

theorem dens_delAt (F : V n → Alt n) (v : V n) : dens (delAt F v) =
    ∑ a, ∑ S, GlobalTheory.del (fun x => (bas n).repr (F x) S) v (coordVec a) *
      ((bas n).repr (dz a * bas n S) Finset.univ / (bas n).repr (vol n : Alt n) Finset.univ) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dens, delAt, coefwise, Finset.mul_sum, mul_smul_comm, map_sum, map_smul, Finsupp.coe_finsetSum,
    Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, Finset.sum_div, mul_div_assoc]

theorem integral_dens_delAt {F : V n → Alt n} (hF : ∀ S, ContDiff ℝ 1 fun v => (bas n).repr (F v) S)
    (hc : ∀ S, HasCompactSupport fun v => (bas n).repr (F v) S) :
    Integrable (fun v => dens (delAt F v)) ∧ ∫ v, dens (delAt F v) = 0 := by
  have hi : ∀ a S, Integrable fun v => GlobalTheory.del (fun x => (bas n).repr (F x) S) v (coordVec a) *
      ((bas n).repr (dz a * bas n S) Finset.univ / (bas n).repr (vol n : Alt n) Finset.univ) :=
    fun a S => (del_integral (hF S) (hc S) _).1.mul_const _
  simp only [dens_delAt]
  refine ⟨integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun S _ => hi a S, ?_⟩
  rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun S _ => hi a S]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [integral_finsetSum _ fun S _ => hi a S]
  refine Finset.sum_eq_zero fun S _ => ?_
  rw [integral_mul_const, (del_integral (hF S) (hc S) _).2, zero_mul]

end GlobalTheory.CxForm.LocStokes

namespace GlobalTheory.CxForm.LocStokes

open GlobalTheory.CxForm

variable {n : ℕ}

theorem integral_eq_of_vanish {M : Type} [TopologicalSpace M] [SecondCountableTopology M] [MeasurableSpace M]
    [BorelSpace M] (A : HolAtlas M n) {α : A.Fld} (hα : A.IsForm α) (i : A.ι) {K : Set M} (hKm : MeasurableSet K)
    (hKs : K ⊆ (A.e i).source) (h0 : ∀ x : A.Pt, x.pt ∉ K → α x = 0)
    (hI : Integrable fun v => (dens (A.loc α i v)).re) :
    A.integral α = ∫ v, (dens (A.loc α i v)).re := by
  have hl : ∀ j y (hy : y ∈ (A.e j).source), A.loc α j (A.e j y) = α ⟨(j, y), hy⟩ := fun j y hy =>
    A.loc_crd α ⟨(j, y), hy⟩
  have hρ : ∀ (ε : ℤˣ) j k y, y ∈ (A.e j).source → y ∈ (A.e k).source →
      ENNReal.ofReal ((ε : ℤ) * (dens (A.loc α j (A.e j y))).re) =
      ENNReal.ofReal (‖ChartGlue.transDet (A.e j) (A.e k) y‖ ^ 2) *
        ENNReal.ofReal ((ε : ℤ) * (dens (A.loc α k (A.e k y))).re) := by
    intro ε j k y hj hk
    rw [hl j y hj, hl k y hk, hα.compat ⟨(j, y), hj⟩ ⟨(k, y), hk⟩ rfl, dens_pull,
      ← ENNReal.ofReal_mul (sq_nonneg _)]
    congr 1
    simp only [ChartGlue.transDet, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring
  have hz : ∀ (ε : ℤˣ) j y, y ∈ (A.e j).source → y ∉ K →
      ENNReal.ofReal ((ε : ℤ) * (dens (A.loc α j (A.e j y))).re) = 0 := by
    intro ε j y hy hyK
    rw [hl j y hy, h0 ⟨(j, y), hy⟩ hyK, dens_zero]
    simp
  have hc : ∀ ε : ℤˣ, A.part α ε Kᶜ = 0 := fun ε => by
    have key : A.part α ε ≤ (A.part α ε).restrict K := iSup_le fun j => by
      have e : ChartGlue.chartMeas (A.e j)
          (fun y => ENNReal.ofReal ((ε : ℤ) * (dens (A.loc α j (A.e j y))).re)) Kᶜ = 0 := by
        rw [ChartGlue.chartMeas_apply _ _ hKm.compl]
        refine setLIntegral_eq_zero (ChartGlue.measurableSet_image _
          ((A.e j).open_source.measurableSet.inter hKm.compl) Set.inter_subset_left) ?_
        rintro _ ⟨y, hy, rfl⟩
        simp only [(A.e j).left_inv hy.1]
        exact hz ε j y hy.1 hy.2
      rw [← Measure.restrict_eq_self_of_ae_mem (s := K) (mem_ae_iff.2 e)]
      exact Measure.restrict_mono le_rfl (le_iSup (fun j => ChartGlue.chartMeas (A.e j)
        fun y => ENNReal.ofReal ((ε : ℤ) * (dens (A.loc α j (A.e j y))).re)) j)
    refine le_antisymm ((key Kᶜ).trans_eq ?_) bot_le
    rw [Measure.restrict_apply hKm.compl, Set.compl_inter_self, measure_empty]
  have hv : ∀ v, v ∉ (A.e i) '' K → (dens (A.loc α i v)).re = 0 := fun v hv => by
    by_cases ht : v ∈ (A.e i).target
    · rw [HolAtlas.loc, dite_eq_left ht, h0 ⟨(i, (A.e i).symm v), (A.e i).map_target ht⟩
        fun h => hv ⟨_, h, (A.e i).right_inv ht⟩, dens_zero, Complex.zero_re]
    · rw [HolAtlas.loc, dite_eq_right ht, dens_zero, Complex.zero_re]
  have hp : ∀ ε : ℤˣ, A.part α ε univ = ∫⁻ v, ENNReal.ofReal ((ε : ℤ) * (dens (A.loc α i v)).re) := fun ε => by
    rw [← measure_add_measure_compl hKm, hc ε, add_zero, HolAtlas.part,
      ChartGlue.glueMeas_apply A.e _ (fun j k => A.holo j k) (hρ ε) i hKm hKs,
      ChartGlue.chartMeas_apply_of_subset _ _ hKm hKs,
      ← lintegral_indicator (ChartGlue.measurableSet_image _ hKm hKs)]
    refine lintegral_congr fun v => ?_
    by_cases hvK : v ∈ (A.e i) '' K
    · obtain ⟨y, hy, rfl⟩ := hvK
      rw [Set.indicator_of_mem (Set.mem_image_of_mem _ hy), (A.e i).left_inv (hKs hy)]
    · rw [Set.indicator_of_notMem hvK, hv v hvK, mul_zero, ENNReal.ofReal_zero]
  rw [HolAtlas.integral, measureReal_def, measureReal_def, hp, hp,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hI]
  simp

end GlobalTheory.CxForm.LocStokes

namespace GlobalTheory.CxForm.LocStokes

open GlobalTheory.CxForm

variable {n : ℕ}

theorem integral_del_fn_mul_eq_zero_of_isForm {M : Type} [TopologicalSpace M] [CompactSpace M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (A : HolAtlas M n) (γ : A.Fld) (χ : M → ℝ)
    (i : A.ι) (hγ : A.IsForm γ) (hχ : A.SmoothOn univ (fun y => (χ y : ℂ))) (hs : tsupport χ ⊆ (A.e i).source)
    (hd : A.IsForm (A.del (A.fn χ * γ))) : A.integral (A.del (A.fn χ * γ)) = 0 := by
  set β : A.Fld := A.fn χ * γ with hβdef
  set K : Set M := tsupport χ with hKdef
  have hKc : IsCompact K := (isClosed_tsupport χ).isCompact
  have hKm : MeasurableSet K := (isClosed_tsupport χ).measurableSet
  have hβ : A.IsForm β := FormMul.isForm_mul A _ _ (A.isForm_fn hχ) hγ
  have hβ0 : ∀ x : A.Pt, x.pt ∉ K → β x = 0 := fun x hx => by
    simp [hβdef, HolAtlas.fn, image_eq_zero_of_notMem_tsupport hx]

  have hβn : ∀ j, ∀ y ∈ (A.e j).source, y ∉ K → A.loc β j =ᶠ[𝓝 (A.e j y)] fun _ => 0 := fun j y hy hyK => by
    filter_upwards [(ChartGlue.isOpen_over (A.e j) (isClosed_tsupport χ).isOpen_compl).mem_nhds
      (ChartGlue.mem_over (A.e j) (S := Kᶜ) hy hyK)] with w hw
    rw [HolAtlas.loc, dite_eq_left hw.1]
    exact hβ0 _ hw.2
  have hd0 : ∀ x : A.Pt, x.pt ∉ K → A.del β x = 0 := fun x hx =>
    delAt_eq_zero_of_eventually (hβn x.1.1 x.pt x.2 hx)

  set F : V n → Alt n := A.loc β i with hFdef
  set AK : Set (V n) := (A.e i) '' K with hAKdef
  have hAK : IsCompact AK := hKc.image_of_continuousOn ((A.e i).continuousOn.mono hs)
  have hAKt : AK ⊆ (A.e i).target := by
    rintro _ ⟨y, hy, rfl⟩
    exact (A.e i).map_source (hs hy)
  have hF0 : ∀ v ∉ AK, F v = 0 := fun v hv => by
    by_cases ht : v ∈ (A.e i).target
    · rw [hFdef, HolAtlas.loc, dite_eq_left ht]
      exact hβ0 _ fun h => hv ⟨_, h, (A.e i).right_inv ht⟩
    · rw [hFdef, HolAtlas.loc, dite_eq_right ht]
  have hFA : ∀ v ∉ AK, F =ᶠ[𝓝 v] fun _ => 0 := fun v hv => by
    filter_upwards [hAK.isClosed.isOpen_compl.mem_nhds hv] with w hw
    exact hF0 w hw
  have hFS : ∀ S, ContDiff ℝ 1 fun v => (bas n).repr (F v) S := fun S => contDiff_iff_contDiffAt.2 fun v => by
    by_cases ht : v ∈ (A.e i).target
    · exact ((hβ.smooth i S).contDiffAt ((A.e i).open_target.mem_nhds ht)).of_le (by simp)
    · refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ((hFA v fun h => ht (hAKt h)).mono fun w hw => ?_)
      simp [hw]
  have hFc : ∀ S, HasCompactSupport fun v => (bas n).repr (F v) S := fun S =>
    HasCompactSupport.intro hAK fun v hv => by simp [hF0 v hv]
  have hloc : ∀ v, A.loc (A.del β) i v = delAt F v := fun v => by
    by_cases ht : v ∈ (A.e i).target
    · rw [HolAtlas.loc, dite_eq_left ht]
      show delAt (A.loc β i) ((A.e i) ((A.e i).symm v)) = _
      rw [(A.e i).right_inv ht]
    · rw [HolAtlas.loc, dite_eq_right ht]
      exact (delAt_eq_zero_of_eventually (hFA v fun h => ht (hAKt h))).symm
  obtain ⟨hI, h0⟩ := integral_dens_delAt hFS hFc
  have hIre : Integrable fun v => (dens (A.loc (A.del β) i v)).re := by
    simp only [hloc]
    exact Complex.reCLM.integrable_comp hI
  rw [integral_eq_of_vanish A hd i hKm hs hd0 hIre]
  simp only [hloc]
  have := Complex.reCLM.integral_comp_comm hI
  simp only [Complex.reCLM_apply] at this
  rw [this, h0, Complex.zero_re]

end GlobalTheory.CxForm.LocStokes
end
end

section

open Set Matrix Filter Topology
open GlobalTheory.HermFrame GlobalTheory.CxForm
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec chernPoly curvPoly)
open scoped ContDiff ComplexOrder

theorem _root_.GlobalTheory.T.holomorphicDel_chernFormOfGramMatrix_eq_zero : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (H : V n → Matrix r r ℂ) (s : Set (V n)), IsOpen s → (∀ a b, ContDiffOn ℝ ∞ (fun v => H v a b) s) → (∀ v ∈ s, IsUnit (H v).det) → ∀ (j : ℕ), ∀ v ∈ s, delAt (fun w => (chernAt H w j : Alt n)) v = 0 := by
  first | exact @GlobalTheory.CxForm.ChernDel.delAt_chernAt | exact GlobalTheory.CxForm.ChernDel.delAt_chernAt | (intros; apply GlobalTheory.CxForm.ChernDel.delAt_chernAt <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct

theorem _root_.GlobalTheory.T.isCompact_specialUnitary_supportedAtPlaces : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (∀ w ∈ S₁, ∃ C : Set (w.Completion ⊗[F] E), IsCompact C ∧ ∀ g : Matrix (Fin M) (Fin M) (w.Completion ⊗[F] E), Formalism.UG.cT (sigR w.Completion σ) g * JR w.Completion J * g = JR w.Completion J → ∀ i j, g i j ∈ C) → (∀ v ∈ S₂, ∃ C : Set (Fv F v ⊗[F] E), IsCompact C ∧ ∀ g : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E), Formalism.UG.cT (sigR (Fv F v) σ) g * JR (Fv F v) J * g = JR (Fv F v) J → ∀ i j, g i j ∈ C) → IsCompact (SUSupp σ J ε) := by
  first | exact @GlobalTheory.SUSuppCompact.isCompact_SUSupp_of_bounded | exact GlobalTheory.SUSuppCompact.isCompact_SUSupp_of_bounded | (intros; apply GlobalTheory.SUSuppCompact.isCompact_SUSupp_of_bounded <;> assumption)
end
