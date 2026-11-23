module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle216
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.MapUgAlgebraMap
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.MapWXi
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.AffineHodgeIsomorphisms.IsFormT
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CosieveBot
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle214
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.SobGL

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.SobGL.Expand

variable {n : ℕ}

def co (q : Idx n) (M : Mat n) : ℝ := if q.1 then (M q.2.1 q.2.2).re else (M q.2.1 q.2.2).im

theorem sum_single_ite (a b : Fin n) (g : Fin n → Fin n → ℂ) :
    ∑ x, ∑ i, (if x = a ∧ i = b then g x i else 0) = g a b := by
  rw [Finset.sum_eq_single a (fun x _ hx => by simp [hx]) (by simp),
    Finset.sum_eq_single b (fun i _ hi => by simp [hi]) (by simp)]
  simp

theorem sum_co_smul (M : Mat n) : ∑ q : Idx n, co q M • bs q = M := by
  ext a b
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, co, bs, Matrix.sum_apply, Matrix.add_apply,
    Matrix.smul_apply, Matrix.single_apply, if_true, Bool.false_eq_true, if_false, smul_ite,
    smul_zero]
  rw [sum_single_ite a b (fun x i => (M x i).re • (1 : ℂ)),
    sum_single_ite a b (fun x i => (M x i).im • Complex.I)]
  simp [Complex.ext_iff]

theorem contDiff_entry (i j : Fin n) : ContDiff ℝ ∞ (fun y : Mat n => y i j) :=
  contDiff_apply_apply ℝ i j

theorem contDiff_det (F : Mat n → Mat n) (h : ∀ i j, ContDiff ℝ ∞ (fun y => F y i j)) :
    ContDiff ℝ ∞ (fun y => (F y).det) := by
  simp only [Matrix.det_apply']
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => h _ _)

theorem contDiff_adjugate (i k : Fin n) : ContDiff ℝ ∞ (fun y : Mat n => y.adjugate i k) := by
  simp only [Matrix.adjugate_apply]
  refine contDiff_det (fun y => y.updateRow k (Pi.single i 1)) fun a b => ?_
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiff_const
  · exact contDiff_entry a b

theorem isOpen_GLs : IsOpen (GLs n) :=
  isOpen_ne.preimage (contDiff_det (n := n) id contDiff_entry).continuous

theorem contDiffOn_inv_entry (i k : Fin n) :
    ContDiffOn ℝ ∞ (fun y : Mat n => y⁻¹ i k) (GLs n) := by
  have h : ContDiffOn ℝ ∞ (fun y : Mat n => (y.det)⁻¹ * y.adjugate i k) (GLs n) :=
    ((contDiff_det (n := n) id contDiff_entry).contDiffOn.inv fun y hy => hy).mul
      (contDiff_adjugate i k).contDiffOn
  refine h.congr fun y _ => ?_
  rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]

theorem co_smooth (p q : Idx n) :
    ContDiffOn ℝ ∞ (fun y : Mat n => co q (y⁻¹ * bs p)) (GLs n) := by
  have he : ∀ a b, ContDiffOn ℝ ∞ (fun y : Mat n => (y⁻¹ * bs p) a b) (GLs n) := by
    intro a b
    simp only [Matrix.mul_apply]
    exact ContDiffOn.sum fun k _ => (contDiffOn_inv_entry a k).mul contDiffOn_const
  rcases q with ⟨_ | _, a, b⟩
  · simpa [co, Function.comp_def] using Complex.imCLM.contDiff.comp_contDiffOn (he a b)
  · simpa [co, Function.comp_def] using Complex.reCLM.contDiff.comp_contDiffOn (he a b)

theorem contDiff_mul_right (X : Mat n) : ContDiff ℝ ∞ (fun y : Mat n => y * X) := by
  refine contDiff_pi.2 fun a => contDiff_pi.2 fun b => ?_
  simp only [Matrix.mul_apply]
  exact ContDiff.sum fun k _ => (contDiff_entry a k).mul contDiff_const

theorem Rw_smooth {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {f : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) (w : List (Idx n)) :
    ContDiffOn ℝ ∞ (Rw w f) (GLs n) := by
  induction w with
  | nil => exact hf
  | cons p w ih =>
    exact (ih.fderiv_of_isOpen isOpen_GLs (by simp)).clm_apply
      (contDiff_mul_right (bs p)).contDiffOn

theorem fderiv_mul_expand {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (H : Mat n → V)
    (y M : Mat n) : fderiv ℝ H y (y * M) = ∑ q, co q M • Rd (bs q) H y := by
  conv_lhs => rw [← sum_co_smul M]

  rw [Matrix.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Matrix.mul_smul, map_smul]
  rfl

theorem fderiv_expand {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (H : Mat n → V)
    {y : Mat n} (hy : y ∈ GLs n) (X : Mat n) :
    fderiv ℝ H y X = ∑ q, co q (y⁻¹ * X) • Rd (bs q) H y := by
  have hu : IsUnit y.det := isUnit_iff_ne_zero.2 hy
  rw [← fderiv_mul_expand, Matrix.mul_nonsing_inv_cancel_left y X hu]

theorem exists_integralCombination_of_mem_completedLattice (L : List (Idx n)) :
    ∃ (ι : Type) (_ : Fintype ι) (c : ι → Mat n → ℝ) (w : ι → List (Idx n)),
      (∀ i, ContDiffOn ℝ ∞ (c i) (GLs n)) ∧
      ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V),
        ContDiffOn ℝ ∞ f (GLs n) → ∀ y ∈ GLs n, Dw L f y = ∑ i, c i y • Rw (w i) f y := by
  induction L with
  | nil =>
    exact ⟨Unit, inferInstance, fun _ _ => 1, fun _ => [], fun _ => contDiffOn_const,
      fun V _ _ f _ y _ => by simp [Dw_nil, Rw]⟩
  | cons p L ih =>
    obtain ⟨ι, _, c, w, hc, h⟩ := ih
    refine ⟨ι ⊕ (ι × Idx n), inferInstance,
      Sum.elim (fun i y => fderiv ℝ (c i) y (bs p)) (fun e y => c e.1 y * co e.2 (y⁻¹ * bs p)),
      Sum.elim w (fun e => e.2 :: w e.1), ?_, ?_⟩
    · rintro (i | ⟨i, q⟩)
      · exact ((hc i).fderiv_of_isOpen isOpen_GLs (by simp)).clm_apply contDiffOn_const
      · exact (hc i).mul (co_smooth p q)
    · intro V _ _ f hf y hy
      have hev : Dw L f =ᶠ[nhds y] fun z => ∑ i, c i z • Rw (w i) f z := by
        filter_upwards [isOpen_GLs.mem_nhds hy] with z hz using h V f hf z hz
      have hdc : ∀ i, DifferentiableAt ℝ (c i) y := fun i =>
        ((hc i).contDiffAt (isOpen_GLs.mem_nhds hy)).differentiableAt (by simp)
      have hdr : ∀ i, DifferentiableAt ℝ (Rw (w i) f) y := fun i =>
        ((Rw_smooth hf (w i)).contDiffAt (isOpen_GLs.mem_nhds hy)).differentiableAt (by simp)
      show fderiv ℝ (Dw L f) y (bs p) = _
      have hd : HasFDerivAt (fun z => ∑ i, c i z • Rw (w i) f z)
          (∑ i, (c i y • fderiv ℝ (Rw (w i) f) y +
            (fderiv ℝ (c i) y).smulRight (Rw (w i) f y))) y :=
        HasFDerivAt.fun_sum fun i _ => (hdc i).hasFDerivAt.fun_smul (hdr i).hasFDerivAt
      rw [hev.fderiv_eq, hd.fderiv]
      simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply]
      rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [add_comm]
      congr 1
      rw [fderiv_expand _ hy, Finset.smul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [mul_smul]
      rfl

theorem Dw_eq_comb : ∀ (n : ℕ) (L : List (Idx n)), ∃ (m : ℕ) (c : Fin m → Mat n → ℝ) (w : Fin m → List (Idx n)),
    (∀ i, ContDiffOn ℝ ∞ (c i) (GLs n)) ∧ ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V),
      ContDiffOn ℝ ∞ f (GLs n) → ∀ y ∈ GLs n, Dw L f y = ∑ i, c i y • Rw (w i) f y := by
  intro n L
  obtain ⟨ι, _, c, w, hc, h⟩ := exists_integralCombination_of_mem_completedLattice L
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun i => c (e.symm i), fun i => w (e.symm i), fun i => hc _, ?_⟩
  intro V _ _ f hf y hy
  rw [h V f hf y hy]
  exact (Equiv.sum_comp e.symm fun i => c i y • Rw (w i) f y).symm

end GlobalTheory.CompanionTheory.SobGL.Expand
end
end

section

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.SobGL

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.SobGL.Chart

def cmL (n : ℕ) : (Idx n → ℝ) →L[ℝ] Mat n :=
  ∑ p, (ContinuousLinearMap.proj p : (Idx n → ℝ) →L[ℝ] ℝ).smulRight (bs p)

theorem cmL_apply {n : ℕ} (t : Idx n → ℝ) : cmL n t = cm t := by
  simp [cmL, cm]

theorem cm_single {n : ℕ} (p : Idx n) : cmL n (Pi.single p 1) = bs p := by
  rw [cmL_apply]
  simp [cm, Pi.single_apply, ite_smul]

theorem hasFDerivAt_chart {n : ℕ} (t : Idx n → ℝ) :
    HasFDerivAt (fun t : Idx n → ℝ => (1 : Mat n) + cm t) (cmL n) t := by
  have h : (fun t : Idx n → ℝ => (1 : Mat n) + cm t) = fun t => 1 + cmL n t := by
    funext s; rw [cmL_apply]
  rw [h]
  exact (cmL n).hasFDerivAt.const_add 1

theorem contDiff_chart {n : ℕ} : ContDiff ℝ ∞ (fun t : Idx n → ℝ => (1 : Mat n) + cm t) := by
  have h : (fun t : Idx n → ℝ => (1 : Mat n) + cm t) = fun t => 1 + cmL n t := by
    funext s; rw [cmL_apply]
  rw [h]
  exact contDiff_const.add (cmL n).contDiff

theorem isOpen_GLs' {n : ℕ} : IsOpen (GLs n) := by
  have : Continuous (fun g : Mat n => g.det) := Continuous.matrix_det continuous_id
  exact isOpen_ne_fun this continuous_const

theorem contDiffOn_fderiv_const {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {U : Set E} (hU : IsOpen U) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f U) (v : E) : ContDiffOn ℝ ∞ (fun g => fderiv ℝ f g v) U := by
  have h1 : ContDiffOn ℝ ∞ (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by simp)
  exact h1.clm_apply contDiffOn_const

theorem contDiffOn_Dw {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V)
    (hf : ContDiffOn ℝ ∞ f (GLs n)) (L : List (Idx n)) : ContDiffOn ℝ ∞ (Dw L f) (GLs n) := by
  induction L with
  | nil => exact hf
  | cons p L ih =>
    rw [Dw_cons]
    exact contDiffOn_fderiv_const isOpen_GLs' ih (bs p)

theorem pd_chart {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V)
    (hf : ContDiffOn ℝ ∞ f (GLs n)) (L : List (Idx n)) :
    ∀ t : Idx n → ℝ, 1 + cm t ∈ GLs n →
      pd L (fun t : Idx n → ℝ => f (1 + cm t)) t = Dw L f (1 + cm t) := by
  induction L with
  | nil => intro t _; rfl
  | cons p L ih =>
    intro t ht
    have hopen : IsOpen {s : Idx n → ℝ | (1 : Mat n) + cm s ∈ GLs n} :=
      isOpen_GLs'.preimage contDiff_chart.continuous
    have hev : pd L (fun t : Idx n → ℝ => f (1 + cm t)) =ᶠ[nhds t]
        fun s => Dw L f (1 + cm s) :=
      Filter.eventuallyEq_of_mem (hopen.mem_nhds ht) (fun s hs => ih s hs)
    have hD : DifferentiableAt ℝ (Dw L f) (1 + cm t) :=
      ((contDiffOn_Dw f hf L).contDiffAt (isOpen_GLs'.mem_nhds ht)).differentiableAt (by simp)
    have hc : HasFDerivAt (fun s : Idx n → ℝ => Dw L f (1 + cm s))
        ((fderiv ℝ (Dw L f) (1 + cm t)).comp (cmL n)) t :=
      hD.hasFDerivAt.comp t (hasFDerivAt_chart t)
    rw [pd_cons, Dw_cons]
    show fderiv ℝ (pd L fun t : Idx n → ℝ => f (1 + cm t)) t (Pi.single p 1) = _
    rw [hev.fderiv_eq, hc.fderiv]
    simp [cm_single]

theorem chart_main : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V),
    ContDiffOn ℝ ∞ f (GLs n) → ContDiffOn ℝ ∞ (fun t : Idx n → ℝ => f (1 + cm t)) {t | 1 + cm t ∈ GLs n} ∧
      ∀ (L : List (Idx n)) (t : Idx n → ℝ), 1 + cm t ∈ GLs n →
        pd L (fun t : Idx n → ℝ => f (1 + cm t)) t = Dw L f (1 + cm t) := by
  intro n V _ _ f hf
  refine ⟨?_, fun L t ht => pd_chart f hf L t ht⟩
  exact hf.comp contDiff_chart.contDiffOn (fun t ht => ht)

end GlobalTheory.CompanionTheory.SobGL.Chart
end
end

section

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.SobGL

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.SobGL.LeftTr

variable {n : ℕ}

theorem isOpen_gls (n : ℕ) : IsOpen (GLs n) := by
  have h : Continuous (fun g : Mat n => g.det) := Continuous.matrix_det continuous_id
  exact isOpen_ne.preimage h

def lmul (x : Mat n) : Mat n →L[ℝ] Mat n :=
  LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ x)

def rmul (x : Mat n) : Mat n →L[ℝ] Mat n :=
  LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ x)

theorem lmul_apply (x y : Mat n) : lmul x y = x * y := rfl

theorem mul_mem_gls {x y : Mat n} (hx : x ∈ GLs n) (hy : y ∈ GLs n) : x * y ∈ GLs n := by
  simp only [GLs, Set.mem_setOf_eq, Matrix.det_mul] at *
  exact mul_ne_zero hx hy

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem contDiffOn_along {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {U : Set E} (hU : IsOpen U) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f U) (A : E →L[ℝ] E) :
    ContDiffOn ℝ ∞ (fun g => fderiv ℝ f g (A g)) U := by
  have h1 : ContDiffOn ℝ ∞ (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by simp)
  exact h1.clm_apply A.contDiff.contDiffOn

theorem contDiffOn_Rd {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (X : Mat n) :
    ContDiffOn ℝ ∞ (Rd X f) (GLs n) :=
  contDiffOn_along (isOpen_gls n) hf (rmul X)

theorem contDiffOn_Rw {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n))
    (w : List (Idx n)) : ContDiffOn ℝ ∞ (Rw w f) (GLs n) := by
  induction w with
  | nil => exact hf
  | cons p w ih => exact contDiffOn_Rd ih (bs p)

theorem Rw_left (n : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V)
    (hf : ContDiffOn ℝ ∞ f (GLs n)) (x : Mat n) (hx : x ∈ GLs n) :
    ContDiffOn ℝ ∞ (fun y => f (x * y)) (GLs n) ∧
      ∀ (w : List (Idx n)), ∀ y ∈ GLs n, Rw w (fun y => f (x * y)) y = Rw w f (x * y) := by
  have hmaps : Set.MapsTo (fun y : Mat n => x * y) (GLs n) (GLs n) :=
    fun y hy => mul_mem_gls hx hy
  refine ⟨hf.comp (lmul x).contDiff.contDiffOn hmaps, fun w => ?_⟩
  induction w with
  | nil => intro y _; rfl
  | cons p w ih =>
    intro y hy
    have hev : Rw w (fun y => f (x * y)) =ᶠ[nhds y] (Rw w f) ∘ (lmul x) :=
      Filter.eventually_of_mem ((isOpen_gls n).mem_nhds hy) ih
    have hd : DifferentiableAt ℝ (Rw w f) (lmul x y) :=
      ((contDiffOn_Rw hf w).contDiffAt ((isOpen_gls n).mem_nhds (mul_mem_gls hx hy))).differentiableAt
        (by simp)
    have hc : HasFDerivAt ((Rw w f) ∘ (lmul x))
        ((fderiv ℝ (Rw w f) (lmul x y)).comp (lmul x)) y :=
      hd.hasFDerivAt.comp y (lmul x).hasFDerivAt
    change fderiv ℝ (Rw w (fun y => f (x * y))) y (y * bs p) =
      fderiv ℝ (Rw w f) (x * y) (x * y * bs p)
    rw [hev.fderiv_eq, hc.fderiv]
    simp only [ContinuousLinearMap.comp_apply, lmul_apply, Matrix.mul_assoc]

end GlobalTheory.CompanionTheory.SobGL.LeftTr
end
end

section

open MeasureTheory Matrix Topology Filter
open scoped ContDiff ENNReal ComplexOrder Pointwise
open PositivityTheory.RgTw (Mat G hb)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.ConeHaar
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.ConeHaar

variable {n : ℕ}

theorem posDef_congr_iff (g H : Mat n) (hg : g.det ≠ 0) : (g * H * gᴴ).PosDef ↔ H.PosDef := by
  have hU : IsUnit (star g) := ((Matrix.isUnit_iff_isUnit_det g).2 (isUnit_iff_ne_zero.2 hg)).star
  have h := Matrix.IsUnit.posDef_star_left_conjugate_iff (x := H) hU
  rwa [star_star, Matrix.star_eq_conjTranspose] at h

theorem det_congr_re (g H : Mat n) : (g * H * gᴴ).det.re = ‖g.det‖ ^ 2 * H.det.re := by
  have h1 : (g * H * gᴴ).det = ((‖g.det‖ ^ 2 : ℝ) : ℂ) * H.det := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, Complex.star_def,
      ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
    ring
  rw [h1, Complex.re_ofReal_mul]

theorem coneW_congr (g : Mat n) (v w : Fin n × Fin n → ℝ) (h : hOf w = g * hOf v * gᴴ) :
    coneW n w = ENNReal.ofReal ((‖g.det‖ ^ (2 * n))⁻¹) * coneW n v := by
  unfold coneW
  rw [h, det_congr_re, ← ENNReal.ofReal_mul (inv_nonneg.2 (pow_nonneg (norm_nonneg g.det) (2 * n))),
    mul_pow, ← pow_mul, mul_inv]

theorem map_coneMeas_eq (n : ℕ) (g : Mat n) (hg : g.det ≠ 0)
    (T : (Fin n × Fin n → ℝ) →ₗ[ℝ] (Fin n × Fin n → ℝ)) (hT : ∀ v, hOf (T v) = g * hOf v * gᴴ)
    (hdet : LinearMap.det T = ‖g.det‖ ^ (2 * n)) : Measure.map T (coneMeas n) = coneMeas n := by
  have hd : 0 < LinearMap.det T := by
    rw [hdet]
    exact pow_pos (norm_pos_iff.2 hg) _
  have hdT : LinearMap.det T ≠ 0 := hd.ne'
  let e : (Fin n × Fin n → ℝ) ≃ᵐ (Fin n × Fin n → ℝ) :=
    (LinearMap.equivOfDetNeZero T hdT).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have he : (e : (Fin n × Fin n → ℝ) → (Fin n × Fin n → ℝ)) = T := rfl
  have hC : e ⁻¹' cone n = cone n := by
    ext v
    show (hOf (T v)).PosDef ↔ (hOf v).PosDef
    rw [hT v]
    exact posDef_congr_iff g (hOf v) hg
  have hW : ∀ v, coneW n (e v) = ENNReal.ofReal (LinearMap.det T)⁻¹ * coneW n v := by
    intro v
    rw [hdet]
    exact coneW_congr g v (T v) (hT v)
  have hvol : Measure.map e volume
      = ENNReal.ofReal (LinearMap.det T)⁻¹ • (volume : Measure (Fin n × Fin n → ℝ)) := by
    rw [he, Real.map_linearMap_volume_pi_eq_smul_volume_pi hdT, abs_of_pos (inv_pos.2 hd)]
  have hmap : Measure.map e ((volume : Measure (Fin n × Fin n → ℝ)).restrict (cone n))
      = ENNReal.ofReal (LinearMap.det T)⁻¹ •
        (volume : Measure (Fin n × Fin n → ℝ)).restrict (cone n) := by
    conv_lhs => rw [← hC]
    rw [← MeasurableEquiv.restrict_map, hvol, Measure.restrict_smul]
  have ha0 : ENNReal.ofReal (LinearMap.det T)⁻¹ ≠ 0 := (ENNReal.ofReal_pos.2 (inv_pos.2 hd)).ne'
  have hatop : ENNReal.ofReal (LinearMap.det T)⁻¹ ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [← he]
  ext s hs
  rw [MeasurableEquiv.map_apply]
  unfold coneMeas
  rw [withDensity_apply _ (e.measurable hs), withDensity_apply _ hs,
    ← ENNReal.mul_right_inj ha0 hatop]
  calc ENNReal.ofReal (LinearMap.det T)⁻¹ *
        ∫⁻ v in e ⁻¹' s, coneW n v ∂(volume : Measure (Fin n × Fin n → ℝ)).restrict (cone n)
      = ∫⁻ v in e ⁻¹' s, coneW n (e v) ∂(volume : Measure (Fin n × Fin n → ℝ)).restrict (cone n) := by
        simp_rw [hW]
        rw [lintegral_const_mul' _ _ hatop]
    _ = ∫⁻ w in s, coneW n w
          ∂Measure.map e ((volume : Measure (Fin n × Fin n → ℝ)).restrict (cone n)) := by
        rw [MeasurableEquiv.restrict_map, lintegral_map_equiv]
    _ = ENNReal.ofReal (LinearMap.det T)⁻¹ *
          ∫⁻ w in s, coneW n w ∂(volume : Measure (Fin n × Fin n → ℝ)).restrict (cone n) := by
        rw [hmap, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]

end GlobalTheory.CompanionTheory.ConeHaar
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

theorem _root_.GlobalTheory.T.tilt_sequence_determined_by_sharp : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (a b : ℕ → A.A), (∀ i, a (i + 1) ^ l = a i) → (∀ i, b (i + 1) ^ l = b i) → (∀ i, A.sharp (a i) = A.sharp (b i)) → a = b := by
  first | exact @GlobalTheory.CompanionTheory.Untilt.tilt_inj | exact GlobalTheory.CompanionTheory.Untilt.tilt_inj | (intros; apply GlobalTheory.CompanionTheory.Untilt.tilt_inj <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

theorem _root_.GlobalTheory.T.exists_prime_root_valuation_quotient : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), A.IsTest → ∃ ϖ : A.U, ϖ ^ l = (l : A.U) ∧ R.Val0 (A.U ⧸ Ideal.span {ϖ ^ 2}) ∧ R.Aic (A.U ⧸ Ideal.span {ϖ ^ 2}) := by
  first | exact @GlobalTheory.CompanionTheory.Untilt.untilt_mod_varpi_sq | exact GlobalTheory.CompanionTheory.Untilt.untilt_mod_varpi_sq | (intros; apply GlobalTheory.CompanionTheory.Untilt.untilt_mod_varpi_sq <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh

theorem _root_.GlobalTheory.T.hodge_form_iso_of_bijective : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (a : ℕ),
    (∃ e : CrystallineSemistableComparison.Onto.Om K (CrystallineSemistableComparison.Onto.Sec q ⊤) a →ₗ[K] CrystallineSemistableComparison.Onto.HV q ⊤ a a, CrystallineSemistableComparison.Onto.IsOm q ⊤ a e ∧ Function.Bijective e) →
    ∃ e' : CrystallineSemistableComparison.HT.Hdg q a a ≃ₗ[K] OmU q ⊤ a, CrystallineSemistableComparison.Om.L2.IsOmT q a e' := by
  first | exact @GlobalTheory.CompanionTheory.HodgeFormTop.main | exact GlobalTheory.CompanionTheory.HodgeFormTop.main | (intros; apply GlobalTheory.CompanionTheory.HodgeFormTop.main <;> assumption)
end
