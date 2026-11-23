module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Prod
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.Normed.Ring.Basic

@[expose] public section

section

namespace GlobalTheory

theorem stable_complement_of_kernel_exists
    (V W H : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : V →ₗ[ℂ] H)
    (hι : Function.Injective ι) (pr : V →ₗ[ℂ] W) (H0 : Submodule ℂ V)
    (hfin : FiniteDimensional ℂ H0) (A : Set (Module.End ℂ V))
    (h1 : ∀ a ∈ A, ∀ v ∈ H0, a v ∈ H0)
    (h2 : ∀ a ∈ A, ∀ v ∈ H0, pr v = 0 → pr (a v) = 0)
    (h3 : ∀ a ∈ A, ∃ b ∈ A, ∀ u v, inner ℂ (ι (a u)) (ι v) = inner ℂ (ι u) (ι (b v))) :
    ∀ h ∈ H0, ∃ c ∈ H0, pr c = pr h ∧
      ∀ a ∈ A, ∀ z : ℂ, pr (a c) = z • pr c → a c = z • c := by
  intro h hh
  set K : Submodule ℂ V := H0 ⊓ LinearMap.ker pr with hK
  haveI : FiniteDimensional ℂ K := Submodule.finiteDimensional_of_le inf_le_left
  set K' : Submodule ℂ H := K.map ι with hK'
  haveI : FiniteDimensional ℂ K' := inferInstance
  haveI : CompleteSpace K' := FiniteDimensional.complete ℂ K'
  obtain ⟨y, hy, e, he, hsum⟩ := K'.exists_add_mem_mem_orthogonal (ι h)
  obtain ⟨k, hk, rfl⟩ := Submodule.mem_map.mp hy
  have hkH0 : k ∈ H0 := hk.1
  have hkker : pr k = 0 := hk.2
  refine ⟨h - k, H0.sub_mem hh hkH0, by simp [hkker], ?_⟩
  have horth : ∀ k' ∈ K, inner ℂ (ι k') (ι (h - k)) = 0 := by
    intro k' hk'
    have : ι (h - k) = e := by rw [map_sub, hsum]; abel
    rw [this]
    exact (Submodule.mem_orthogonal K' e).mp he _ (Submodule.mem_map_of_mem hk')
  intro a ha z hz
  set c := h - k with hc
  have hcH0 : c ∈ H0 := H0.sub_mem hh hkH0
  set d := a c - z • c with hd
  have hdK : d ∈ K := by
    refine ⟨H0.sub_mem (h1 a ha c hcH0) (H0.smul_mem z hcH0), ?_⟩
    show pr d = 0
    simp [hd, hz]
  obtain ⟨b, hb, hab⟩ := h3 a ha
  have hdorth : ∀ k' ∈ K, inner ℂ (ι k') (ι d) = 0 := by
    intro k' hk'
    have hbk : b k' ∈ K := ⟨h1 b hb k' hk'.1, h2 b hb k' hk'.1 hk'.2⟩
    have e1 : inner ℂ (ι k') (ι (a c)) = 0 := by
      rw [← inner_conj_symm, hab, inner_conj_symm]
      exact horth _ hbk
    rw [hd, map_sub, inner_sub_right, e1, map_smul, inner_smul_right, horth k' hk']
    simp
  have : ι d = 0 := inner_self_eq_zero.mp (hdorth d hdK)
  have hd0 : d = 0 := hι (by rw [this, map_zero])
  exact sub_eq_zero.mp hd0

end GlobalTheory
end

section

open MeasureTheory
open scoped ContDiff

namespace GlobalTheory
namespace CurveProductSmooth

variable {G : Type} [Group G] {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (ρ : G →* (K →L[ℂ] K)) {P : Type} (A : Set P) (e : P → ℝ → G)

def JointlySmooth {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (Φ : E → K) : Prop :=
  ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] (g : F → E), ContDiff ℝ ∞ g →
    ∀ l : List (P × (F → ℝ)), (∀ a ∈ l, a.1 ∈ A ∧ ContDiff ℝ ∞ a.2) →
      ContDiff ℝ ∞ fun x : F => ρ (l.map fun a => e a.1 (a.2 x)).prod (Φ (g x))

variable {ρ A e}

end CurveProductSmooth

open MeasureTheory in
open scoped ContDiff in
variable {G : Type} [Group G] {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (ρ : G →* (K →L[ℂ] K)) {P : Type} (A : Set P) (e : P → ℝ → G) in
variable {ρ A e} in
private theorem contDiff_prod_ofFn_apply_of_jointlySmooth {k : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Φ : E → K} (h : _root_.GlobalTheory.CurveProductSmooth.JointlySmooth ρ A e Φ) {g : (Fin k → ℝ) → E}
    (hg : ContDiff ℝ ∞ g) (ps : Fin k → P) (hps : ∀ i, ps i ∈ A) :
    ContDiff ℝ ∞ fun t : Fin k → ℝ => ρ (List.ofFn fun i => e (ps i) (t i)).prod (Φ (g t)) := by
  have h1 := h (Fin k → ℝ) g hg (List.ofFn fun i => (ps i, fun t : Fin k → ℝ => t i)) (by
    intro a ha
    rw [List.mem_ofFn] at ha
    obtain ⟨i, rfl⟩ := ha
    exact ⟨hps i, contDiff_apply ℝ (fun _ => ℝ) i⟩)
  simpa [List.map_ofFn, Function.comp_def] using h1

open MeasureTheory in
open scoped ContDiff in
variable {G : Type} [Group G] {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (ρ : G →* (K →L[ℂ] K)) {P : Type} (A : Set P) (e : P → ℝ → G) in
variable {ρ A e} in
private theorem deriv_continuousLinearMap_comp_eq (T : K →L[ℂ] K) (f : ℝ → K) (hf : DifferentiableAt ℝ f 0) :
    deriv (fun r => T (f r)) 0 = T (deriv f 0) :=
  ((T.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hf.hasDerivAt).deriv

open MeasureTheory in
open scoped ContDiff in
variable {G : Type} [Group G] {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (ρ : G →* (K →L[ℂ] K)) {P : Type} (A : Set P) (e : P → ℝ → G) in
variable {ρ A e} in
private theorem jointlySmooth_deriv_action {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Φ : E → K}
    (h : _root_.GlobalTheory.CurveProductSmooth.JointlySmooth ρ A e Φ) {p : P} (hp : p ∈ A) :
    _root_.GlobalTheory.CurveProductSmooth.JointlySmooth ρ A e fun t => deriv (fun r : ℝ => ρ (e p r) (Φ t)) 0 := by
  intro F _ _ g hg l hl
  have hf : ∀ y : E, ContDiff ℝ ∞ fun r : ℝ => ρ (e p r) (Φ y) := fun y => by
    simpa using h ℝ (fun _ => y) contDiff_const [(p, id)] (by simp [hp, contDiff_id])
  let H : F × ℝ → K := fun z =>
    ρ (((l.map fun a : P × (F → ℝ) => (a.1, a.2 ∘ Prod.fst)) ++ [(p, Prod.snd)]).map
      fun a : P × (F × ℝ → ℝ) => e a.1 (a.2 z)).prod
      (Φ (g z.1))
  have hH : ContDiff ℝ ∞ H := h (F × ℝ) (g ∘ Prod.fst) (hg.comp contDiff_fst) _ (by
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
      exact ⟨(hl b hb).1, (hl b hb).2.comp contDiff_fst⟩
    · rw [List.mem_singleton] at ha
      subst ha
      exact ⟨hp, contDiff_snd⟩)
  have hHx : ∀ x r, H (x, r) = ρ (l.map fun a => e a.1 (a.2 x)).prod (ρ (e p r) (Φ (g x))) := by
    intro x r
    simp [H, List.map_append, List.map_map, Function.comp_def, map_mul]
  have hder : ∀ x, ρ (l.map fun a => e a.1 (a.2 x)).prod (deriv (fun r : ℝ => ρ (e p r) (Φ (g x))) 0)
      = fderiv ℝ H (x, 0) (0, 1) := by
    intro x
    rw [← deriv_continuousLinearMap_comp_eq _ _ ((hf (g x)).differentiable (by simp)).differentiableAt]
    have h2 : HasDerivAt (fun r : ℝ => H (x, r)) (fderiv ℝ H (x, 0) (0, 1)) 0 :=
      (hH.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
        ((hasDerivAt_const (0 : ℝ) x).prodMk (hasDerivAt_id (0 : ℝ)))
    rw [← h2.deriv]
    simp only [hHx]
  have hfin : ContDiff ℝ ∞ fun x : F => fderiv ℝ H (x, 0) (0, 1) :=
    ((contDiff_infty_iff_fderiv.1 hH).2.comp (contDiff_id.prodMk contDiff_const)).clm_apply
      contDiff_const
  convert hfin using 1
  funext x
  exact hder x

open MeasureTheory in
open scoped ContDiff in
variable {G : Type} [Group G] {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (ρ : G →* (K →L[ℂ] K)) {P : Type} (A : Set P) (e : P → ℝ → G) in
variable {ρ A e} in
private theorem jointlySmooth_const' {v : K}
    (hv : ∀ (k : ℕ) (ps : Fin k → P), (∀ i, ps i ∈ A) →
      ContDiff ℝ ∞ fun t : Fin k → ℝ => ρ (List.ofFn fun i => e (ps i) (t i)).prod v)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    _root_.GlobalTheory.CurveProductSmooth.JointlySmooth ρ A e (fun _ : E => v) := by
  intro F _ _ g _ l hl
  have h1 := hv l.length (fun i => l[i].1) (fun i => (hl _ (List.getElem_mem _)).1)
  have h2 : ContDiff ℝ ∞ fun x : F => fun i : Fin l.length => l[i].2 x :=
    contDiff_pi.2 fun i => (hl _ (List.getElem_mem _)).2
  have h3 := h1.comp h2
  convert h3 using 1
  funext x
  have hlist : (l.map fun a : P × (F → ℝ) => e a.1 (a.2 x)) =
      List.ofFn fun i : Fin l.length => e l[i].1 (l[i].2 x) :=
    List.ext_getElem (by simp) (by simp)
  simp only [hlist, Function.comp_apply]

open MeasureTheory in
open scoped ContDiff in
variable {G : Type} [Group G] {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (ρ : G →* (K →L[ℂ] K)) {P : Type} (A : Set P) (e : P → ℝ → G) in
variable {ρ A e} in
private theorem jointlySmooth_prod_map_action {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Φ : E → K} (h : _root_.GlobalTheory.CurveProductSmooth.JointlySmooth ρ A e Φ) (m : List (P × (E → ℝ)))
    (hm : ∀ a ∈ m, a.1 ∈ A ∧ ContDiff ℝ ∞ a.2) :
    _root_.GlobalTheory.CurveProductSmooth.JointlySmooth ρ A e fun y => ρ (m.map fun a => e a.1 (a.2 y)).prod (Φ y) := by
  intro F _ _ g hg l hl
  have h1 := h F g hg (l ++ m.map fun a => (a.1, a.2 ∘ g)) (by
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · exact hl a ha
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
      exact ⟨(hm b hb).1, (hm b hb).2.comp hg⟩)
  convert h1 using 1
  funext x
  simp [List.map_append, List.prod_append, map_mul, List.map_map, Function.comp_def]

open MeasureTheory in
open scoped ContDiff in
variable {G : Type} [Group G] {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (ρ : G →* (K →L[ℂ] K)) {P : Type} (A : Set P) (e : P → ℝ → G) in
variable {ρ A e} in
private theorem jointlySmooth_foldr_deriv_action {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Φ : E → K} (h : _root_.GlobalTheory.CurveProductSmooth.JointlySmooth ρ A e Φ) (l : List P) (hl : ∀ p ∈ l, p ∈ A) :
    _root_.GlobalTheory.CurveProductSmooth.JointlySmooth ρ A e fun t =>
      l.foldr (fun p w => deriv (fun r : ℝ => ρ (e p r) w) 0) (Φ t) := by
  induction l with
  | nil => exact h
  | cons q l ih =>
    exact jointlySmooth_deriv_action (ih fun p hp => hl p (List.mem_cons_of_mem _ hp)) (hl q (by simp))


open scoped ContDiff in
theorem _root_.GlobalTheory.smooth_along_curve_products_stable : ∀ (G : Type) [Group G] (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (ρ : G →* (K →L[ℂ] K)) (P : Type) (A : Set P) (e : P → ℝ → G) (v : K), (∀ (k : ℕ) (ps : Fin k → P), (∀ i, ps i ∈ A) → ContDiff ℝ ∞ fun t : Fin k → ℝ => ρ (List.ofFn fun i => e (ps i) (t i)).prod v) → (∀ p ∈ A, ∀ (k : ℕ) (ps : Fin k → P), (∀ i, ps i ∈ A) → ContDiff ℝ ∞ fun t : Fin k → ℝ => ρ (List.ofFn fun i => e (ps i) (t i)).prod (deriv (fun r : ℝ => ρ (e p r) v) 0)) ∧ (∀ (m : ℕ) (qs : Fin m → P) (r : Fin m → ℝ), (∀ i, qs i ∈ A) → ∀ (k : ℕ) (ps : Fin k → P), (∀ i, ps i ∈ A) → ContDiff ℝ ∞ fun t : Fin k → ℝ => ρ (List.ofFn fun i => e (ps i) (t i)).prod (ρ (List.ofFn fun i => e (qs i) (r i)).prod v)) ∧ ∀ l : List P, (∀ p ∈ l, p ∈ A) → ∀ (k : ℕ) (ps : Fin k → P), (∀ i, ps i ∈ A) → ContDiff ℝ ∞ fun t : Fin k → ℝ => l.foldr (fun p w => deriv (fun r : ℝ => ρ (e p r) w) 0) (ρ (List.ofFn fun i => e (ps i) (t i)).prod v) := by
  intro G _ K _ _ _ ρ P A e v hv
  refine ⟨fun p hp k ps hps => ?_, fun m qs r hqs k ps hps => ?_, fun l hl k ps hps => ?_⟩
  · exact contDiff_prod_ofFn_apply_of_jointlySmooth
      (jointlySmooth_deriv_action (jointlySmooth_const' hv (E := ℝ)) hp) (g := fun _ => 0) contDiff_const ps hps
  · have h1 := jointlySmooth_prod_map_action (jointlySmooth_const' hv (E := ℝ))
      (List.ofFn fun i => (qs i, fun _ : ℝ => r i)) (by
        intro a ha
        rw [List.mem_ofFn] at ha
        obtain ⟨i, rfl⟩ := ha
        exact ⟨hqs i, contDiff_const⟩)
    simpa [List.map_ofFn, Function.comp_def] using
      contDiff_prod_ofFn_apply_of_jointlySmooth h1 (g := fun _ => 0) contDiff_const ps hps
  · have h1 := jointlySmooth_prod_map_action (jointlySmooth_const' hv (E := Fin k → ℝ))
      (List.ofFn fun i => (ps i, fun t : Fin k → ℝ => t i)) (by
        intro a ha
        rw [List.mem_ofFn] at ha
        obtain ⟨i, rfl⟩ := ha
        exact ⟨hps i, contDiff_apply ℝ (fun _ => ℝ) i⟩)
    have h2 := jointlySmooth_foldr_deriv_action h1 l hl (Fin k → ℝ) id contDiff_id [] (by simp)
    simpa [List.map_ofFn, Function.comp_def] using h2

end GlobalTheory
end

section

open MeasureTheory Filter Topology Set Module
open scoped ENNReal

namespace GlobalTheory

theorem taylorTail_step_one {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (g : ℝ → F) (a : ℝ) (hg : Differentiable ℝ g) (hd : Continuous (deriv g))
    (hlim : Tendsto g atTop (𝓝 0)) :
    ENNReal.ofReal ‖g a‖ ≤ ∫⁻ t in Ioi a, ‖deriv g t‖ₑ := by
  by_cases hI : IntegrableOn (deriv g) (Ioi a)
  · have hint : ∫ x in Ioi a, deriv g x = 0 - g a :=
      integral_Ioi_of_hasDerivAt_of_tendsto hg.continuous.continuousWithinAt
        (fun x _ => (hg x).hasDerivAt) hI hlim
    rw [zero_sub] at hint
    have h1 : ‖g a‖ ≤ ∫ x in Ioi a, ‖deriv g x‖ := by
      calc ‖g a‖ = ‖∫ x in Ioi a, deriv g x‖ := by rw [hint, norm_neg]
        _ ≤ ∫ x in Ioi a, ‖deriv g x‖ := norm_integral_le_integral_norm _
    calc ENNReal.ofReal ‖g a‖ ≤ ENNReal.ofReal (∫ x in Ioi a, ‖deriv g x‖) := ENNReal.ofReal_le_ofReal h1
      _ = ∫⁻ t in Ioi a, ‖deriv g t‖ₑ := ofReal_integral_norm_eq_lintegral_enorm hI
  · have : ∫⁻ t in Ioi a, ‖deriv g t‖ₑ = ∞ := by
      by_contra hne
      exact hI ⟨hd.aestronglyMeasurable, lt_top_iff_ne_top.mpr hne⟩
    rw [this]; exact le_top

theorem taylorTail_inner (j : ℕ) (s : ℝ) (hs : 0 < s) :
    ∫⁻ t in Ioo (0:ℝ) s, ENNReal.ofReal (t ^ j / (j.factorial : ℝ))
      = ENNReal.ofReal (s ^ (j+1) / ((j+1).factorial : ℝ)) := by
  have hcont : Continuous (fun t : ℝ => t ^ j / (j.factorial : ℝ)) := by fun_prop
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hs.le,
      intervalIntegral.integral_div, integral_pow, Nat.factorial_succ]
    push_cast
    rw [zero_pow (Nat.succ_ne_zero j), sub_zero, div_div, mul_comm]
  · exact (hcont.integrableOn_Icc (a := 0) (b := s)).mono_set Ioo_subset_Icc_self
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact div_nonneg (pow_nonneg ht.1.le _) (by positivity)

theorem taylorTail_tonelli (f : ℝ → ℝ≥0∞) (hf : Measurable f) (j : ℕ) :
    ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ j / (j.factorial : ℝ)) * ∫⁻ s in Ioi t, f s
      = ∫⁻ s in Ioi (0:ℝ), ENNReal.ofReal (s ^ (j+1) / ((j+1).factorial : ℝ)) * f s := by
  set w : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (t ^ j / (j.factorial : ℝ)) with hw
  have hwm : Measurable w := by fun_prop
  let G : ℝ → ℝ → ℝ≥0∞ := fun t s => w t * (Ioi t).indicator f s
  have hG : Measurable (Function.uncurry G) := by
    have hS : MeasurableSet {p : ℝ × ℝ | p.1 < p.2} := measurableSet_lt measurable_fst measurable_snd
    have : Function.uncurry G = fun p : ℝ × ℝ => w p.1 * ({p : ℝ × ℝ | p.1 < p.2}.indicator (fun p => f p.2) p) := by
      ext ⟨t, s⟩
      simp only [Function.uncurry_apply_pair, G, Set.indicator, mem_Ioi, mem_setOf_eq]
    rw [this]
    exact (hwm.comp measurable_fst).mul ((hf.comp measurable_snd).indicator hS)
  have step1 : ∫⁻ t in Ioi (0:ℝ), w t * ∫⁻ s in Ioi t, f s
      = ∫⁻ t in Ioi (0:ℝ), ∫⁻ s in Ioi (0:ℝ), G t s := by
    refine setLIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    simp only [G]
    rw [lintegral_const_mul _ (hf.indicator measurableSet_Ioi), lintegral_indicator measurableSet_Ioi,
      Measure.restrict_restrict measurableSet_Ioi, Ioi_inter_Ioi, sup_eq_left.mpr (le_of_lt (mem_Ioi.mp ht))]
  rw [step1, lintegral_lintegral_swap hG.aemeasurable]
  refine setLIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
  have : ∀ t, G t s = (Iio s).indicator w t * f s := by
    intro t
    by_cases h : t < s <;> simp [G, Set.indicator, h]
  simp_rw [this]
  rw [lintegral_mul_const _ (hwm.indicator measurableSet_Iio), lintegral_indicator measurableSet_Iio,
    Measure.restrict_restrict measurableSet_Iio, Iio_inter_Ioi, taylorTail_inner j s hs]

theorem taylorTail_bound {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (h : ℝ → F) (m : ℕ) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hlim : ∀ j ≤ m, Tendsto (iteratedDeriv j h) atTop (𝓝 0)) :
    ENNReal.ofReal ‖h 0‖ ≤ ∫⁻ t in Ioi (0:ℝ),
      ENNReal.ofReal (t ^ m / (m.factorial : ℝ)) * ‖iteratedDeriv (m + 1) h t‖ₑ := by
  have hdiff : ∀ n : ℕ, Differentiable ℝ (iteratedDeriv n h) := fun n =>
    hh.differentiable_iteratedDeriv n (by exact_mod_cast ENat.coe_lt_top n)
  have hcont : ∀ n : ℕ, Continuous (iteratedDeriv n h) := fun n => (hdiff n).continuous
  have key : ∀ j ≤ m, ENNReal.ofReal ‖h 0‖ ≤ ∫⁻ t in Ioi (0:ℝ),
      ENNReal.ofReal (t ^ j / (j.factorial : ℝ)) * ‖iteratedDeriv (j + 1) h t‖ₑ := by
    intro j
    induction j with
    | zero =>
      intro _
      have := taylorTail_step_one h 0 (hdiff 0) (by rw [← iteratedDeriv_one]; exact hcont 1)
        (by simpa using hlim 0 (Nat.zero_le _))
      simpa [iteratedDeriv_one] using this
    | succ j ih =>
      intro hj
      refine (ih (Nat.le_of_succ_le hj)).trans ?_
      calc ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ j / (j.factorial : ℝ)) * ‖iteratedDeriv (j + 1) h t‖ₑ
          ≤ ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ j / (j.factorial : ℝ)) *
              ∫⁻ s in Ioi t, ‖iteratedDeriv (j + 1 + 1) h s‖ₑ := by
            refine lintegral_mono (fun t => ?_)
            refine mul_le_mul_of_nonneg_left ?_ (zero_le')
            have := taylorTail_step_one (iteratedDeriv (j+1) h) t (hdiff _)
              (by rw [← iteratedDeriv_succ]; exact hcont _) (hlim (j+1) hj)
            simpa [iteratedDeriv_succ] using this
        _ = _ := taylorTail_tonelli _ ((hcont _).enorm.measurable) j
  exact key m le_rfl

end GlobalTheory
end

section

namespace GlobalTheory

noncomputable def circArgChar {G : Type} [Group G] (ν : G →* ℂˣ) : G →* Circle where
  toFun g := ⟨(ν g : ℂ) / (‖(ν g : ℂ)‖ : ℂ), by
    have h : ‖(ν g : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr (ν g).ne_zero
    simp [Submonoid.unitSphere, h]⟩
  map_one' := by
    apply Circle.ext
    simp
  map_mul' a b := by
    apply Circle.ext
    show ((ν (a * b) : ℂˣ) : ℂ) / (‖((ν (a * b) : ℂˣ) : ℂ)‖ : ℂ) =
      ((ν a : ℂ) / (‖(ν a : ℂ)‖ : ℂ)) * ((ν b : ℂ) / (‖(ν b : ℂ)‖ : ℂ))
    rw [ν.map_mul, Units.val_mul, norm_mul, Complex.ofReal_mul, mul_div_mul_comm]

noncomputable def circNormChar {G : Type} [Group G] (ν : G →* ℂˣ) (t : ℝ) : G →* Circle where
  toFun g := Circle.exp (t * Real.log ‖(ν g : ℂ)‖)
  map_one' := by simp
  map_mul' a b := by
    have ha : ‖(ν a : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr (ν a).ne_zero
    have hb : ‖(ν b : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr (ν b).ne_zero
    show Circle.exp (t * Real.log ‖((ν (a * b) : ℂˣ) : ℂ)‖) = _
    rw [ν.map_mul, Units.val_mul, norm_mul, Real.log_mul ha hb, mul_add, Circle.exp_add]

private theorem coe_circArgChar_eq_div_norm {G : Type} [Group G] (ν : G →* ℂˣ) (g : G) :
    ((circArgChar ν g : Circle) : ℂ) = (ν g : ℂ) / (‖(ν g : ℂ)‖ : ℂ) := by
  rfl

theorem complexChar_eq_one_of_forall_circleChar :
    ∀ {G : Type} [Group G] (ν : G →* ℂˣ) (x : G),
      (∀ μ : G →* Circle, (∀ g, ν g = 1 → μ g = 1) → μ x = 1) → ν x = 1 := by
  intro G _ ν x h
  have hx0 : (ν x : ℂ) ≠ 0 := (ν x).ne_zero
  have hpos : 0 < ‖(ν x : ℂ)‖ := norm_pos_iff.mpr hx0

  have hn : ‖(ν x : ℂ)‖ = 1 := by
    by_contra hne
    have hlog : Real.log ‖(ν x : ℂ)‖ ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hpos hne
    have h2 := h (circNormChar ν (Real.pi / Real.log ‖(ν x : ℂ)‖)) (fun g hg => by
      simp [circNormChar, hg])
    have h3 := congrArg (fun z : Circle => (z : ℂ)) h2
    simp only [circNormChar, MonoidHom.coe_mk, OneHom.coe_mk, Circle.coe_exp,
      div_mul_cancel₀ _ hlog, Circle.coe_one] at h3
    norm_num [Complex.exp_pi_mul_I] at h3

  have h1 := h (circArgChar ν) (fun g hg => by
    apply Circle.ext
    rw [coe_circArgChar_eq_div_norm, hg]
    simp)
  have h4 := congrArg (fun z : Circle => (z : ℂ)) h1
  simp only [coe_circArgChar_eq_div_norm, Circle.coe_one, hn, Complex.ofReal_one, div_one] at h4
  apply Units.ext
  simpa using h4

end GlobalTheory
end

section

namespace GlobalTheory.IsotropicVectorExistence

theorem key {z : ℂ} (k : ℕ) (h : ∀ n : ℕ, ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) :
    (3 / 2 : ℝ) ^ k * ‖z - 1‖ ≤ ‖z ^ (2 ^ k) - 1‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : z ^ (2 ^ (k + 1)) - 1 = (z ^ (2 ^ k) - 1) * (z ^ (2 ^ k) + 1) := by
      rw [show 2 ^ (k + 1) = 2 ^ k * 2 from pow_succ 2 k, pow_mul]; ring
    have h2 : (3 / 2 : ℝ) ≤ ‖z ^ (2 ^ k) + 1‖ := by
      have h3 : (2 : ℂ) = (z ^ (2 ^ k) + 1) - (z ^ (2 ^ k) - 1) := by ring
      have h4 : ‖(2 : ℂ)‖ ≤ ‖z ^ (2 ^ k) + 1‖ + ‖z ^ (2 ^ k) - 1‖ := by
        rw [h3]; exact norm_sub_le _ _
      have h5 : ‖(2 : ℂ)‖ = 2 := by norm_num
      have h6 := h (2 ^ k)
      linarith
    rw [e, norm_mul, pow_succ]
    calc (3 / 2 : ℝ) ^ k * (3 / 2) * ‖z - 1‖ = ((3 / 2) ^ k * ‖z - 1‖) * (3 / 2) := by ring
      _ ≤ ‖z ^ (2 ^ k) - 1‖ * ‖z ^ (2 ^ k) + 1‖ :=
        mul_le_mul ih h2 (by norm_num) (norm_nonneg _)

theorem main : ∀ {z : ℂ}, (∀ (n : ℕ), ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) → z = (1 : ℂ) := by
  intro z h
  by_contra hne
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / (2 * ‖z - 1‖)) (by norm_num : (1 : ℝ) < 3 / 2)
  rw [div_lt_iff₀ (by positivity)] at hk
  have a := key k h
  have b := h (2 ^ k)
  nlinarith

end GlobalTheory.IsotropicVectorExistence
end
